import Lambda

instance Name [Char] where
    inward::[Char]->[Char]
    inward a=a
    rename::[[Char]]->[Char]->[Char]
    rename a b=let (c,d)=break (==' ') b in head [e|e<-[c++" "++show f|f<-[(if null d then 0 else read (init d)::Integer)..]],notElem (filter (/=' ') e) (map (filter (/=' ')) a)]
    outward::[Char]->[Char]
    outward []=[]
    outward (a:b)=if a==' ' then b else a:outward b

main::IO ()
main=do
    putStrLn "neither or former or latter or both:"
    a<-getLine
    case a of
        "N"->maina neither
        "F"->maina former
        "L"->maina latter
        "B"->maina both
        "n"->maina neither
        "f"->maina former
        "l"->maina latter
        "b"->maina both
        "neither"->maina neither
        "former"->maina former
        "latter"->maina latter
        "both"->maina both
        _->main

maina::([Char]->Lam [Char]->Lam [Char]->Lam [Char])->IO ()
maina a=do
    putStrLn "lambda term:"
    b<-getLine
    case input b of
        Just c->mainb a c
        _->maina a

mainb::([Char]->Lam [Char]->Lam [Char]->Lam [Char])->Lam [Char]->IO ()
mainb a b=do
    putStrLn (output b)
    c<-getLine
    case step a b of
        Just d->if c=="E"||c=="e"||c=="exit"||b==d then main else mainb a d
        _->main
