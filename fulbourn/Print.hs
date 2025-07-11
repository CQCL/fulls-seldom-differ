{-# LANGUAGE DataKinds, ImplicitParams, LambdaCase, ScopedTypeVariables #-}

module Print where

-- Print syntax-highlighted stuff for LaTeX

import Doc
import Hasochism
import Parser
import Syntax
import Test (examples_dir)

import Control.Monad (mapM_)
import Data.List (delete, intercalate)
import Data.Maybe (fromMaybe, fromJust)
import Data.Traversable (for)
import System.Environment
import System.FilePath ((</>))

import Debug.Trace

--track = trace
track = const id

data Format = Latex | Plain deriving Eq

data Precedence = Atom | VecPat | App | LetIn | Top deriving (Eq, Ord)

data Colour = Blue | Purple | Red | Black | Green

synTex x = "full" ++ show x

latexColour Blue = "blue"
latexColour Purple = "purple"
latexColour Red = "red"
latexColour Black = "black"
latexColour Green = "green"

shellColour Blue = "34"
shellColour Purple = "35"
shellColour Red = "31"
shellColour Black = "37" -- N.B this is actually grey
shellColour Green = "32"

syntaxTbl =
 [(Number, Red)
 ,(Var, Purple)
 ,(TyCtor, Blue)
 ,(Ctor, Red)
 ,(Tyvar, Black)
 ,(Operator, Red)
 ,(Keyword, Black)
 ,(Function, Green)
 ]

-- Invariant: Doesn't change the length of a line
as :: String -> Syntax -> String
str `as` syn = "\\full" ++ show syn ++ "{" ++ str ++ "}"

data Syntax = Number | Var | Function | Ctor | TyCtor | Tyvar | Operator | Keyword deriving (Eq, Show)

format :: Format -> Syntax -> String -> Doc
-- N.B. We're engineering a coincedence between the command names in `syntaxTbl`
-- and the show instances for Syntax!!!
format Latex syn = Text (`as` syn)
format Plain syn = Text (\txt -> "\x1b[" ++ shellColour (fromJust $ lookup syn syntaxTbl) ++ "m" ++ txt ++ "\x1b[0m")

number, var, fn, rec, ctor, tyctor, tyvar, op, kw :: (?fmt :: Format) => String -> Doc
number = format ?fmt Number
var = format ?fmt Var
fn = format ?fmt Function
rec = format ?fmt Function
ctor = format ?fmt Ctor
tyctor = format ?fmt TyCtor
tyvar = format ?fmt Tyvar
op = ctor
kw = format ?fmt Keyword

arrow :: Format -> Doc
-- We don't want the "->" to appear in the latex, but we want to be able to
-- prepend whitespace as appropriate
arrow Latex = Text (\x -> take (length x - 2) x ++ "\\textrightarrow") "->"
arrow Plain = Text id "->"

wrap :: Format -> IO () -> IO ()
wrap Plain m = m
wrap Latex m = do
  putStrLn "\\begin{Verbatim}[commandchars=\\\\\\{\\},xleftmargin=\\fullLeftMargin]"
  m
  putStrLn "\\end{Verbatim}"

-- Define some latex commands for colouring stuff
printPreamble :: IO ()
printPreamble = do
  for syntaxTbl $ \(syn, colour) ->
    putStrLn ("\\newcommand{\\" ++ synTex syn ++ "}[1]{\\" ++ latexColour colour ++ "{#1}}")
  putStrLn("\\newcommand{\\fullLeftMargin}{0.8cm}")

printFile :: Format -> Int -> Maybe String -> [(String, (RawScheme, [RawClause]))] -> IO ()
printFile fmt w mfn defs = do
  -- N.B. We extend defs with the content of ../examples/examples.txt, because
  -- our tests assume these definitions are in scope. This is purely for the
  -- purpose of highlighting ambiguous function calls which are parsed as vars
  prelude <- parseFile (examples_dir </> "examples.txt")
  let declsInScope = fst <$> (prelude ++ defs)
  wrap fmt $ let ?fmt = fmt in case mfn of
    Nothing -> printDefs declsInScope defs
    Just fnName -> case lookup fnName defs of
      Nothing -> error $ "Couldn't find function " ++  fnName ++ " in file"
      Just def -> printDef w declsInScope (fnName, def)
 where
  printDefs _ [] = pure ()
  printDefs env [x] = printDef w env x
  printDefs env (x:xs) = printDef w env x *> putStrLn "" *> printDefs env xs

printDef :: (?fmt :: Format)
         => Int
         -> [String] -- Names of functions defined in the file
         -> (String, (RawScheme, [RawClause])) -- The def to print
         -> IO ()
printDef w fns def = do
  let (sig, cs) = doc fns def
  putStrLn $ pretty w sig
  mapM_ (putStrLn . pretty w) cs


text :: String -> Doc
text = Text id

calate :: Doc -> [Doc] -> Doc
calate sep [] = Doc.Nil
calate sep [x] = x
calate sep (x:xs) = x :<> sep :<> calate sep xs

doc :: (?fmt :: Format)
    => [String] -- A list of functions defined, for catching calls parsed as EVar
    -> (String, (RawScheme, [RawClause]))
    -> (Doc, [Doc])
doc fns (name, ((ns, ins, out), cs)) = (sig, clauseDoc <$> cs)
 where
  sig = fn name :<> natArgs :<> text " : " :<>
        -- N.B. natArgs should never break into multiple lines
        showSigTy (lineLen (flatten (text name :<> natArgs))) (ins, out)

  natArgs = if null ns then Doc.Nil else bracketed "<" (calate (text ",") (var <$> ns)) ">"

  clauseDoc (_, ps, pats, e) = fn name :<> qPatsDoc ps :<> (foldl (<+>) (Doc.Nil) (patDoc Atom <$> pats)) <+> text "=" :<> group (Line 1 (showRhs e))

  -- If the RHS is a sequence of lets, print them one line at a time
  showRhs rhs@((e, p) :& body) = showExpr Top e <+> text "->" <+> patDoc Top p :<> text ";" :<> Line 1 (showRhs body)
  showRhs e = showExpr Top e

  qPatsDoc Nothing = Doc.Nil
  qPatsDoc (Just ps) = bracketed "<" (calate (text ",") (qPatDoc <$> ps)) ">"

  qPatDoc = natDoc

  bracket True x = bracketed "(" x ")"
  bracket _ x = x

  -- TODO: Handle special patterns
  patDoc :: Precedence -> Pat String -> Doc
  patDoc _ p@(_ :? _) | Just str <- patDocList p  = str
  patDoc _ (PV x) = var  x
  patDoc p ("cons" :? [x,xs])     = bracket (p < VecPat) (patDoc Atom x  <+> op ",-"  <+> patDoc Atom xs)
  patDoc p ("snoc" :? [xs,x])     = bracket (p < VecPat) (patDoc Atom xs <+> op "-,"  <+> patDoc Atom x)
  patDoc p ("even" :? [ls,rs])    = bracket (p < VecPat) (patDoc Atom ls <+> op "=&=" <+> patDoc Atom rs)
  patDoc p ("riffle" :? [ls,rs])  = bracket (p < VecPat) (patDoc Atom ls <+> op "=%=" <+> patDoc Atom rs)
  patDoc p ("odd" :? [ls,mid,rs]) = bracket (p < VecPat) (patDoc Atom ls <+> op "=,"  <+> patDoc Atom mid <+> op ",=" <+> patDoc Atom rs)
  patDoc _ ("pair" :? [a,b]) = bracket True $ calate (text ", ") (patDoc Top <$> [a,b])
  patDoc _ (p :? []) = text p

  natDoc :: Nat Z String -> Doc
  -- Hack
  natDoc (Suc (Ful x)) = number "2^" <+> natDoc x
  natDoc Zer = number "Z"
  natDoc (Suc x) = number "S" <+> natDoc x
  natDoc (Dub x) = number "D" <+> natDoc x
  natDoc (Ful x) = number "F" <+> natDoc x
  natDoc (NVar (FV v)) = var v

  showSigTy :: Int -> ([Type Z String], Type Z String) -> Doc
  showSigTy _ ([], out) = showTy True out
  showSigTy indent (ins, out) = prettyIns (showTy True <$> ins) :<> onNewLine (showTy True out)
   where
    onNewLine doc = group (Line indent (arrow ?fmt :<> text " " :<> doc))
    -- Make the first option adding a newline before the output type, then working backwards instead of the other way around
    prettyIns [x] = x
    prettyIns (x:xs) = x :<> (foldr (:<>) Doc.Nil (onNewLine <$> xs))

    variants (ins, out) = prettyIns ins :<> onNewLine out


  showTy :: Bool -- Whether we should bracket big types
         -> Type Z String
         -> Doc
  showTy _ (TVar (FV x)) = tyvar x
  -- Is this only Bit?
  showTy _ (c :* []) = tyctor c
  showTy b ("Prod" :* [s,t]) = bracket True $ showTy False s :<> text "," <+> showTy False t
  showTy b (c :* args) = foldr1 (<+>) (tyctor c:(showTy True <$> args))
  -- This should take a newline, but we need to know what the nesting should be
  showTy b (s :-> t) = bracket b $ calate (text " ") [showTy True s, arrow ?fmt, showTy b t]
  showTy b (ty :^ n) = natDoc n <+> tyctor "of" <+> showTy True ty

  indent = unlines . fmap ("  "++) . lines

  showList :: forall a. (a -> Maybe (String, [a])) -> (a -> Doc) -> a -> Maybe Doc
  showList destruct show x = (\x -> bracketed "[" x "]") . calate (text ", ") <$> (destruct x >>= worker)
   where
    bracket x = '[' : x ++ "]"

    worker :: (String, [a]) -> Maybe [Doc]
    worker ("nil", []) = Just []
    worker ("cons", [x,xs]) = (show x:) <$> (destruct xs >>= worker)
    worker _ = Nothing

  patDocList :: Pat String -> Maybe Doc
  patDocList = showList destruct (patDoc Top)
   where
    destruct (c :? as) = Just (c, as)
    destruct _ = Nothing

  showExprList :: Expr String -> Maybe Doc
  showExprList = showList destruct (showExpr Top)
   where
    destruct (c :$ as) = Just (c, as)
    destruct _ = Nothing

  -- Precedence arg is the biggest thing that we wouldn't need to bracket
  showExpr :: Precedence -> Expr String -> Doc
  showExpr _ x | track (show x) False = undefined
  -- Hack: We carry a list of all the function names defined in the file, and
  -- use this to catch calls that were parsed as EVar. This means if a local var
  -- shadows a global function name, it will be the wrong colour
  showExpr _ (EVar x) = if x `elem` fns then rec x else var x
  -- TODO: Handle special constructors
  showExpr p (c :$ as) = showCtor p c as
  showExpr p (f :/ a) = bracket (p < App) $ showExpr App f :<> group (Line 1 (showExpr Atom a))
  showExpr _ (Rec v Nothing) = rec v
  showExpr _ (Rec v (Just ns)) = rec v :<> bracketed "<" (calate (text ",") (natDoc <$> ns)) ">"
  showExpr p ((e, pat) :& body) = bracket (p < LetIn) $
    showExpr Top e <+> text "->" <+> patDoc Top pat :<> text ";" :<> group (Line 1 (showExpr Top body))

  showCtor :: Precedence -> String -> [Expr String] -> Doc
  showCtor _ c as | Just doc <- showExprList (c :$ as) = doc
  showCtor p "cons" [x,xs] = bracket (p < VecPat) $ showExpr Atom x <+> op ",-" <+> showExpr VecPat xs
  showCtor p "snoc" [xs,x] = bracket (p < VecPat) $ showExpr VecPat xs <+> op "-," <+> showExpr Atom x
  showCtor p "even" [ls,rs] = bracket (p < VecPat) $ showExpr Atom ls <+> op "=&=" <+> showExpr Atom rs
  showCtor p "riffle" [ls,rs] = bracket (p < VecPat) $ showExpr Atom ls <+> op "=%=" <+> showExpr Atom rs
  showCtor p "odd" [ls,mid,rs] = bracket (p < VecPat) $ calate (text " ") [showExpr Atom ls
                                                                          ,op "=,"
                                                                          ,showExpr Atom mid
                                                                          ,op ",="
                                                                          ,showExpr Atom rs
                                                                          ]
  showCtor _ "pair" [a,b] = bracket True $ showExpr Top a :<> text "," <+> showExpr Top b
  showCtor _ "vap" [x] = showExpr Atom x :<> op "!"
  showCtor _ c [] = text c
  showCtor _ c args = error $ "showCtor " ++ c ++ " " ++ show args

defaultWidth = 50
