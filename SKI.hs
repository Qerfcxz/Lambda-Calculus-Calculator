module SKI(to) where

import Lambda

data SKIV a=SV|KV|IV|AV (SKIV a) (SKIV a)|V a

data SKIP=SP|KP|IP|AP SKIP SKIP

instance Name a=>Show (SKIV a) where
    show::SKIV a->[Char]
    show SV="S"
    show KV="K"
    show IV="I"
    show (V a)=outward a
    show (AV a b)="("++show a++") ("++show b++")"

instance Show SKIP where
    show::SKIP->[Char]
    show SP="S"
    show KP="K"
    show IP="I"
    show (AP a b)="("++show a++") ("++show b++")"

toV::Eq a=>Lam a->SKIV a
toV (Var a)=V a
toV (App a b)=AV (toV a) (toV b)
toV (Abs a b)=goV a (toV b)

goV::Eq a=>a->SKIV a->SKIV a
goV _ SV=AV KV SV
goV _ KV=AV KV KV
goV _ IV=AV KV IV
goV a (AV b c)=AV (AV SV (goV a b)) (goV a c)
goV a (V b)=if a==b then IV else AV KV (V b)

toP::SKIV a->SKIP
toP SV=SP
toP KV=KP
toP IV=IP
toP (AV a b)=AP (toP a) (toP b)

isP::SKIV a->Bool
isP (V _)=False
isP (AV a b)=isP a&&isP b
isP _=True

to::Eq a=>Lam a->Either SKIP (SKIV a)
to a=let b=toV a in if isP b then Left (toP b) else Right b