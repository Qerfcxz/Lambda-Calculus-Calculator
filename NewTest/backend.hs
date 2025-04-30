import Lambda
import LambdaString
import Data.Binary
import System.Environment(getArgs)
import System.IO (hSetEncoding, stdout, utf8)

function_definition::[Char]
function_definition="function_definition"

expression_result::[Char]
expression_result="expression_result"

main :: IO ()
main = do
    hSetEncoding stdout utf8
    args <- getArgs
    case args of
        ["new" , strategy , stepsStr , exprStr] -> do
            case input exprStr of
                Nothing -> putStrLn "Error: Incorrect expression syntax"
                Just expr -> do
                    funcDefs <- decodeFile function_definition :: IO [([Char],Lam [Char])]
                    if look expr (map fst funcDefs) then putStrLn "Error: Binding variables does not allow duplicate names with functions" else do
                        let strat = case strategy of
                                "neither" -> neither
                                "former" -> former
                                "latter" -> latter
                                "both" -> both
                        case substAll funcDefs expr of
                            Nothing -> do
                                let result = simplify strat (read stepsStr) expr
                                encodeFile expression_result (last result)
                                mapM_ (putStrLn . output) result
                            Just new -> do
                                let time = read stepsStr - 1
                                if time == 0
                                    then do
                                        encodeFile expression_result new
                                        putStrLn (output expr)
                                        putStrLn (output new)
                                    else do
                                        let result = simplify strat time new
                                        encodeFile expression_result (last result)
                                        putStrLn (output expr)
                                        mapM_ (putStrLn . output) result
                        putStrLn "success"
        ["old" , strategy , stepsStr] -> do
            let strat = case strategy of
                    "neither" -> neither
                    "former" -> former
                    "latter" -> latter
                    "both" -> both
            expr <- decodeFile expression_result :: IO (Lam [Char])
            let result = simplify strat (read stepsStr) expr
            encodeFile expression_result (last result)
            mapM_ (putStrLn . output) (tail result)
            putStrLn "success"



look::Lam [Char]->[[Char]]->Bool
look (Var _) _=False
look (App a b) c=look a c||look b c
look (Abs a b) c=if elem a c then True else look b c



simplify :: ([Char] -> Lam [Char] -> Lam [Char] -> Lam [Char]) -> Int -> Lam [Char] -> [Lam [Char]]
simplify strat n expr = if n > 0
    then case step strat expr of
        Just new -> if expr==new then [expr] else expr : simplify strat (n-1) new
        Nothing -> [expr]
    else [expr]


substAll :: [([Char], Lam [Char])] -> Lam [Char] -> Maybe (Lam [Char])
substAll substs expr = case substMulti substs expr of
    Just new -> Just (substThen substs new)
    Nothing -> Nothing
  where
    substThen substs expr = case substMulti substs expr of
        Just new -> substThen substs new
        Nothing -> expr


substMulti :: [([Char], Lam [Char])] -> Lam [Char] -> Maybe (Lam [Char])
substMulti substs (Var v) = lookup v substs
substMulti substs (App e1 e2) = case (substMulti substs e1, substMulti substs e2) of
    (Just new1, Just new2) -> Just (App new1 new2)
    (Just new1, Nothing) -> Just (App new1 e2)
    (Nothing, Just new2) -> Just (App e1 new2)
    (Nothing, Nothing) -> Nothing
substMulti substs (Abs x e) = case substMulti substs e of
    Just new -> Just (Abs x new)
    _->Nothing