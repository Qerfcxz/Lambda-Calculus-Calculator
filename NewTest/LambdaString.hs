module LambdaString where
import Data.Binary
import Lambda

instance Name [Char] where
    inward a=a
    outward []=[]
    outward (a:b)=if a==' ' then b else a:outward b
    rename a b = let (c, d) = break (== ' ') b in head [e | e <- [c ++ " " ++ show f | f <- [(if null d then 0 else read (init d) :: Integer)..]],notElem (filter (/= ' ') e) (map (filter (/= ' ')) a)]

instance Name a=>Show (Lam a) where
    show=output

instance Binary a=>Binary (Lam a) where
    put (Var a)=do
        put (0::Word8)
        put a
    put (App a b)=do
        put (1::Word8)
        put a
        put b
    put (Abs a b)=do
        put (2::Word8)
        put a
        put b
    get=do
        tag<-get::Get Word8
        case tag of
            0->Var<$>get
            1->App<$>get<*>get
            2->Abs<$>get<*>get
            _->fail "Invalid tag for Lam a"