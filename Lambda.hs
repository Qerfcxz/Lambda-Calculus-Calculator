module Lambda(Lam,Name,inward,outward,rename,input,output,step,neither,former,latter,both) where

data Lam a=Var a|App (Lam a) (Lam a)|Abs a (Lam a)

data Tra a=Mon a|Pol (Lam a)|Sig

instance Eq a=>Eq (Lam a) where
    (==)::Lam a->Lam a->Bool
    Var a==Var b=a==b
    App a b==App c d=a==c&&b==d
    Abs a b==Abs c d=a==c&&b==d
    _==_=False

class Eq a=>Name a where
    inward::[Char]->a
    outward::a->[Char]
    rename::[a]->a->a

input::Name a=>[Char]->Maybe (Lam a)
input a=inputa a [] [] []

inputa::Name a=>[Char]->[Char]->[Tra a]->[[Tra a]]->Maybe (Lam a)
inputa [] a b c=if null c then inputb (if null a then b else Mon (inward (reverse a)):b) [] else Nothing
inputa (a:b) c d e=case a of
    ' '->inputa b [] (if null c then d else Mon (inward (reverse c)):d) e
    'λ'->inputc b [] (if null c then d else Mon (inward (reverse c)):d) e
    '.'->Nothing
    '('->inputa b [] [] ((if null c then d else Mon (inward (reverse c)):d):e)
    ')'->case e of
        []->Nothing
        (f:g)->case inputb (if null c then d else Mon (inward (reverse c)):d) [] of
            Nothing->Nothing
            Just h->inputa b [] (Pol h:f) g
    _->inputa b (a:c) d e

inputb::Name a=>[Tra a]->[Lam a]->Maybe (Lam a)
inputb [] []=Nothing
inputb [] (a:b)=Just (foldl App a b)
inputb (a:b) c=case a of
    Mon d->inputb b (Var d:c)
    Pol d->inputb b (d:c)
    Sig->case c of
        Var d:e:f->inputb b [Abs d (foldl App e f)]
        _->Nothing

inputc::Name a=>[Char]->[Char]->[Tra a]->[[Tra a]]->Maybe (Lam a)
inputc [] _ _ _=Nothing
inputc (a:b) c d e=case a of
    ' '->if null c then inputc b [] d e else inputd b [] (Mon (inward (reverse c)):Sig:d) e
    'λ'->if null c then Nothing else inputc b [] (Mon (inward (reverse c)):Sig:d) e
    '.'->if null c then Nothing else inputa b [] (Mon (inward (reverse c)):Sig:d) e
    '('->Nothing
    ')'->Nothing
    _->inputc b (a:c) d e

inputd::Name a=>[Char]->[Char]->[Tra a]->[[Tra a]]->Maybe (Lam a)
inputd [] _ _ _=Nothing
inputd (a:b) c d e=case a of
    ' '->inputd b [] (if null c then d else Mon (inward (reverse c)):Sig:d) e
    'λ'->inputc b [] (if null c then d else Mon (inward (reverse c)):Sig:d) e
    '.'->inputa b [] (if null c then d else Mon (inward (reverse c)):Sig:d) e
    '('->Nothing
    ')'->Nothing
    _->inputd b (a:c) d e

join::Eq a=>a->[a]->[a]
join a []=[a]
join a (b:c)=if a==b then b:c else b:join a c

leave::Eq a=>a->[a]->[a]
leave _ []=[]
leave a (b:c)=if a==b then c else b:leave a c

data Lama a=Vara|Varb a|Appa (Lama a) (Lama a)|Appb (Lama a) (Lama a)|Appc (Lama a) (Lama a)|Appd (Lama a) (Lama a)|Appe (Lama a) (Lama a) [a]|Appf (Lama a) (Lama a) [a]|Appg (Lama a) (Lama a) [a]|Apph (Lama a) (Lama a) [a]|Appi (Lama a) (Lama a) [a]|Appj (Lama a) (Lama a) [a]|Appk (Lama a) (Lama a) [a]|Appl (Lama a) (Lama a) [a]|Appm (Lama a) (Lama a) [a] [a]|Appn (Lama a) (Lama a) [a] [a]|Appo (Lama a) (Lama a) [a] [a]|Appp (Lama a) (Lama a) [a] [a]|Absa a (Lama a)|Absb a (Lama a) a

judge::Name a=>a->Lam a->(Bool,Lama a)
judge a (Var b)=if a==b then (True,Vara) else (False,Varb b)
judge a (App b c)=let (d,e)=judge a b in let (f,g)=judge a c in if d then (True,if f then Appa e g else Appb e g) else (f,if f then Appc e g else Appd e g)
judge a (Abs b c)=if a==b then (False,Absa b (judgea c)) else let (d,e)=judge a c in (d,Absa b e)

judgea::Name a=>Lam a->Lama a
judgea (Var a)=Varb a
judgea (App a b)=Appd (judgea a) (judgea b)
judgea (Abs a b)=Absa a (judgea b)

tag::Name a=>[a]->Lama a->Lama a
tag _ Vara=Vara
tag a (Appa b c)=Appa (tag a b) (tag a c)
tag a (Appb b c)=Appb (tag a b) c
tag a (Appc b c)=Appc b (tag a c)
tag a (Absa b c)=if elem b a
    then let (d,_,e,f)=taga [b] a c in case e of
        []->Absa (rename (foldr join a d) b) f
        [g]->Absb (rename (foldr join a (foldr join d g)) b) f b
    else Absa b (tag a c)

taga::Name a=>[a]->[a]->Lama a->([a],[a],[[a]],Lama a)
taga _ _ Vara=([],[],[],Vara)
taga a b (Appa c d)=let (e,f,g,h)=taga a b c in let (i,j,k,l)=taga a b d in if null f then if null j then (foldr join e i,[],[],Appa h l) else (foldr join e i,j,k,Appe h l j) else if null j then (foldr join e i,f,g,Appi h l f) else tagb (foldr join e i) f j [] g k [] (Appm h l f j)
taga a b (Appb c d)=let (e,f,g,h)=taga a b c in let (i,j,k,l)=tagd a d in if null f then if null j then (foldr join e i,[],[],Appb h l) else (foldr join e i,j,k,Appf h l j) else if null j then (foldr join e i,f,g,Appj h l f) else tagb (foldr join e i) f j [] g k [] (Appn h l f j)
taga a b (Appc c d)=let (e,f,g,h)=tagd a c in let (i,j,k,l)=taga a b d in if null f then if null j then (foldr join e i,[],[],Appc h l) else (foldr join e i,j,k,Appg h l j) else if null j then (foldr join e i,f,g,Appk h l f) else tagb (foldr join e i) f j [] g k [] (Appo h l f j)
taga a b (Absa c d)=if elem c b then let (e,f,g,h)=taga (join c a) b d in tage c b e f [] g [] h else let (e,f,g,h)=taga a b d in (leave c e,f,map (join c) g,Absa c h)

tagb::Name a=>[a]->[a]->[a]->[a]->[[a]]->[[a]]->[[a]]->Lama a->([a],[a],[[a]],Lama a)
tagb a (b:c) d e (f:g) h i j=tagc b f a c d [] e g h [] i j
tagb a [] b c [] d e f=(a,b++c,d++e,f)

tagc::Name a=>a->[a]->[a]->[a]->[a]->[a]->[a]->[[a]]->[[a]]->[[a]]->[[a]]->Lama a->([a],[a],[[a]],Lama a)
tagc a b c d (e:f) g h i (j:k) l m n=if a==e then tagb c d (f++g) (e:h) i (k++l) (foldr join b j:m) n else tagc a b c d f (e:g) h i k (j:l) m n
tagc a b c d [] e f g [] h i j=tagb c d e (a:f) g h (b:i) j

tagd::Name a=>[a]->Lama a->([a],[a],[[a]],Lama a)
tagd a (Varb b)=if elem b a then ([],[b],[[]],Varb b) else ([b],[],[],Varb b)
tagd a (Appd b c)=let (d,e,f,g)=tagd a b in let (h,i,j,k)=tagd a c in if null e then if null i then (foldr join d h,[],[],Appd g k) else (foldr join d h,i,j,Apph g k i) else if null i then (foldr join d h,e,f,Appl g k e) else tagb (foldr join d h) e i [] f j [] (Appp g k e i)
tagd a (Absa b c)=let (d,e,f,g)=tagd (leave b a) c in (leave b d,e,map (join b) f,Absa b g)

tage::Name a=>a->[a]->[a]->[a]->[a]->[[a]]->[[a]]->Lama a->([a],[a],[[a]],Lama a)
tage a b c (d:e) f (g:h) i j=if a==d then let k=rename (foldr join b (foldr join c g)) a in (c,e++f,map (join k) (h++i),Absb k j a) else tage a b c e (d:f) h (g:i) j
tage a b c [] d [] e f=let g=rename (foldr join b c) a in (c,d,map (join g) e,Absa g f)

sub::Name a=>Lama a->Lam a->Lam a
sub Vara a=a
sub (Appa a b) c=App (sub a c) (sub b c)
sub (Appb a b) c=App (sub a c) (suba b)
sub (Appc a b) c=App (suba a) (sub b c)
sub (Absa a b) c=Abs a (sub b c)
sub (Absb a b c) d=Abs a (subb [(c,a)] b d)

suba::Name a=>Lama a->Lam a
suba (Varb a)=Var a
suba (Appd a b)=App (suba a) (suba b)
suba (Absa a b)=Abs a (suba b)

subb::Name a=>[(a,a)]->Lama a->Lam a->Lam a
subb a (Appe b c d) e=App (sub b e) (subb (subc d a) c e)
subb a (Appf b c d) e=App (sub b e) (sube (subc d a) c)
subb a (Appg b c d) e=App (suba b) (subb (subc d a) c e)
subb a (Appi b c d) e=App (subb (subc d a) b e) (sub c e)
subb a (Appj b c d) e=App (subb (subc d a) b e) (suba c)
subb a (Appk b c d) e=App (sube (subc d a) b) (sub c e)
subb a (Appm b c d e) f=App (subb (subc d a) b f) (subb (subc e a) c f)
subb a (Appn b c d e) f=App (subb (subc d a) b f) (sube (subc e a) c)
subb a (Appo b c d e) f=App (sube (subc d a) b) (subb (subc e a) c f)
subb a (Absa b c) d=Abs b (subb a c d)
subb a (Absb b c d) e=Abs b (subb ((d,b):a) c e)

subc::Name a=>[a]->[(a,a)]->[(a,a)]
subc [] _=[]
subc (a:b) c=subd a b c []

subd::Name a=>a->[a]->[(a,a)]->[(a,a)]->[(a,a)]
subd _ a [] b=subc a b
subd a b ((c,d):e) f=if a==c then (c,d):subc b (e++f) else subd a b e ((c,d):f)

sube::Name a=>[(a,a)]->Lama a->Lam a
sube [(_,a)] (Varb _)=Var a
sube a (Apph b c d)=App (suba b) (sube (subc d a) c)
sube a (Appl b c d)=App (sube (subc d a) b) (suba c)
sube a (Appp b c d e)=App (sube (subc d a) b) (sube (subc e a) c)
sube a (Absa b c)=Abs b (sube a c)

free::Name a=>Lam a->[a]
free (Var a)=[a]
free (App a b)=foldr join (free a) (free b)
free (Abs a b)=leave a (free b)

step::Name a=>(a->Lam a->Lam a->Lam a)->Lam a->Maybe (Lam a)
step _ (Var _)=Nothing
step a (App (Abs b c) d)=Just (a b c d)
step a (App b c)=case step a b of
    Nothing->case step a c of
        Nothing->Nothing
        Just d->Just (App b d)
    Just d->Just (App d (stepa a c))
step a (Abs b c)=case step a c of
    Nothing->Nothing
    Just d->Just (Abs b d)

stepa::Name a=>(a->Lam a->Lam a->Lam a)->Lam a->Lam a
stepa _ (Var a)=Var a
stepa a (App (Abs b c) d)=a b c d
stepa a (App b c)=App (stepa a b) (stepa a c)
stepa a (Abs b c)=Abs b (stepa a c)

neither::Name a=>a->Lam a->Lam a->Lam a
neither a b c=let (d,e)=judge a b in if d then sub (tag (free c) e) c else b

former::Name a=>a->Lam a->Lam a->Lam a
former a b c=let d=stepa former b in let (e,f)=judge a d in if e then sub (tag (free c) f) c else d

latter::Name a=>a->Lam a->Lam a->Lam a
latter a b c=let (d,e)=judge a b in if d then let f=stepa latter c in sub (tag (free f) e) f else b

both::Name a=>a->Lam a->Lam a->Lam a
both a b c=let d=stepa both b in let (e,f)=judge a d in if e then let g=stepa both c in sub (tag (free g) f) g else d

output::Name a=>Lam a->[Char]
output (Var a)=outward a
output (App a b)=outputa a++" "++outputb b
output (Abs a b)="λ"++outward a++"."++output b

outputa::Name a=>Lam a->[Char]
outputa (Var a)=outward a
outputa (App a b)=outputa a++" "++outputb b
outputa (Abs a b)="(λ"++outward a++"."++output b++")"

outputb::Name a=>Lam a->[Char]
outputb (Var a)=outward a
outputb (App a b)="("++outputa a++" "++outputb b++")"
outputb (Abs a b)="(λ"++outward a++"."++output b++")"
