module Doc where

-- From a prettier printer

import Data.Bifunctor

data Doc
 = Nil
 | Doc :<> Doc -- Concatenation
 | Text (String -> String) String
 | Line Int Doc -- Line + Indent
 | Doc :<|> Doc -- Options

instance Show Doc where
  show Nil = ""
  show (Text f s) = "Text(" ++ s ++ ")"
  show (Line i d) = "Line(" ++ show i ++ ", " ++ show d ++ ")"
  show (a :<|> b) = "(" ++ show a ++ ") <|> (" ++ show b ++ ")"
  show (a :<> b) = show a ++ ", " ++ show b

group :: Doc -> Doc
group x = flatten x :<|> x

flatten :: Doc -> Doc
flatten Nil = Nil
flatten (a :<> b) = flatten a :<> flatten b
flatten (Line _ d) = Text id " " :<> flatten d
flatten (Text f str) = Text f str
flatten (a :<|> _) = flatten a

-- Choose the best layout
best :: Int -- Available width (doesn't change)
     -> Int -- Characters placed already
     -> Doc
     -> (Doc, Int) -- Characters placed after
best w k Nil = (Nil, k)
best w k (Line n d) = let (doc, n') = best w n d in (Line n doc, n')
best w k (Text f str) = (Text f str, k + length str)
best w k (x :<> y) = let (x', k') = best w k x in first (x' :<>) (best w k' y)
best w k (x :<|> y) = better w k (best w k x) (best w k y)

better w k x y = if fits (w - k) (fst x) then x else y

fits :: Int -> Doc -> Bool
fits w x | w < 0 = False
fits w Nil = True
fits w (Text _ str) = length str < w
fits w (Line i d) = True
fits w (x :<> y) = let (_, k) = best w 0 x in fits w x && fits (w - k) y

layout :: Doc -> String
layout (Text f str) = f str
layout (Line n d) = "\n" ++ layout (padLeft n d)
 where
  padLine n (Line n' d) = Line (max n n') d
  padLine n (x :<> y) = padLine n x :<> padLine n y
  padLine n x = x

  padLeft n (Text f str) = Text f (replicate n ' ' ++ str)
  padLeft n (x :<> y) = padLeft n x :<> padLine n y
  padLeft n (Line n' d) = Line (max n n') (padLeft n (padLine n d))
  padLeft n Nil = Nil

layout (a :<> b) = layout a ++ layout b
layout Nil = ""

-- Length of a single line. Undefined if input is not a single line
-- Different to `length . layout . flatten` because we're not applying the function in `Text`
lineLen :: Doc -> Int
lineLen Nil = 0
lineLen (a :<> b) = lineLen a + lineLen b
lineLen (Text _ s) = length s

pretty w x = layout $ fst (best w 0 x)

x <+> y = x :<> (Text id " ") :<> y

bracketed l x r = group (Text id l :<> x :<> Text id r)

x <+/> y = x :<> group (Line 1 y)
