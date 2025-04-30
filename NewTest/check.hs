import Lambda
import LambdaString
import Data.Binary
import System.Environment(getArgs)
import System.IO (hSetEncoding, stdout, utf8)


function_definition::[Char]
function_definition="function_definition"

main::IO ()
main=do
    hSetEncoding stdout utf8
    a<-getArgs
    case a of
        ["clear"]->do
            encodeFile function_definition ([]::[([Char],Lam [Char])])
            putStrLn "success"
        ["delete",b]->do
            c<-decodeFile function_definition::IO [([Char],Lam [Char])]
            let (d,e)=splitAt (read b) c
            encodeFile function_definition (d++tail e)
            putStrLn "success"
        ["append",b,c]->do
            case input c of
                Nothing->putStrLn "Error: Incorrect expression syntax"
                Just d->do
                    e<-decodeFile function_definition::IO [([Char],Lam [Char])]
                    let f=map fst e
                    if not (any (`notElem` f) (free d)) then do
                        let g=(b,d):e
                        if elem b f then putStrLn "Error: Duplicate function name" else case check d g [b] (b:f) of
                            Nothing->do
                                encodeFile function_definition ((b,d):e)
                                putStrLn (b++" := "++output d)
                                putStrLn "success"
                            Just h->putStrLn h
                    else putStrLn "Error: Not a closed formula"

check::Lam [Char]->[([Char],Lam [Char])]->[[Char]]->[[Char]]->Maybe [Char]
check (Var a) b c d=case lookup a b of
    Nothing->Nothing
    Just e->if elem a c then Just "Error: Recursive function definition" else check e b (a:c) d
check (App a b) c d e=case check a c d e of
    Nothing->check b c d e
    f->f
check (Abs a b) c d e=if elem a e then Just "Error: Binding variables does not allow duplicate names with functions" else check b c d e