{-# LANGUAGE DataKinds, LambdaCase #-}

module Parser where

import Control.Applicative (some)
import Control.Monad (unless)
import Data.Either (partitionEithers)
import Data.Functor
import Data.List
import Text.Parsec hiding (optional)
import Text.Parsec.String
import Text.Parsec.Expr
import Text.Parsec.Token
import Text.Parsec.Language

import Hasochism
import Syntax
import Util (nTimes)

import Control.Applicative (optional)

languageDef =
   emptyDef { commentStart    = "{-"
            , commentEnd      = "-}"
            , commentLine     = "--"
            , identStart      = char '_' <|> letter
            , identLetter     = char '_' <|> alphaNum
            , reservedNames   = [ "of"
                                , "tt"
                                , "ff"
                                , "pair"
                                , "Z"
                                , "S"
                                , "D"
                                , "F"
                                , "Bit"
                                , "Int"
                                , "2^"
                                ]
            , reservedOpNames = [",-", "-,", "=&=", "=%=", "=", "=,", ",=", ":", "->", ";"]
            }

TokenParser{ parens = m_parens
           , identifier = m_identifier
           , reservedOp = m_reservedOp
           , reserved = m_reserved
           , commaSep = m_commaSep
           , comma = m_comma
           , angles = m_angles
           , brackets = m_brackets
           , whiteSpace = m_whiteSpace } = makeTokenParser languageDef


binaryTable f = [
    [ Infix (m_reservedOp ",-" >> return (constr "cons")) AssocRight
    , Infix (m_reservedOp "-," >> return (constr "snoc")) AssocRight
    , Infix (m_reservedOp "=&=" >> return (constr "even")) AssocRight
    , Infix (m_reservedOp "=%=" >> return (constr "riffle")) AssocRight
    ]
  ]
 where constr name left right = f name [left, right]

unaryTable = [
    [ Prefix (m_reservedOp "fst" >> return (constr "fst"))
    , Prefix (m_reservedOp "fst" >> return (constr "snd"))
    , Postfix (m_reservedOp "!" >> return (constr "vap"))
    ]
  ]
 where constr name op = name :$ [op]

literal f = (m_reserved "tt" >> return (f "tt" []))
      <|> (m_reserved "ff" >> return (f "ff" []))
      <|> (m_reserved "nil" >> return (f "nil" []))

vec p f = do
  elems <- m_brackets (m_commaSep p)
  return $ foldr (\expr list -> f "cons" [expr, list]) (f "nil" []) elems

-- Try to parse an zx =, x ,= xs expression/pattern, just p if we can't
oddOr :: Parser a -> (String -> [a] -> a) -> Parser a
oddOr p mk = do x <- p
                xs <- optional rest
                pure $ case xs of
                  Nothing -> x
                  Just xs -> mk "odd" (x:xs)
 where
  rest = do m_reservedOp "=,"
            mid <- p
            m_reservedOp ",="
            rs  <- p
            pure $ [mid, rs]

block :: String -> Parser (Expr String)
block name = do
  e <- bigExpr name
  more <- optional $ do
    m_reservedOp "->"
    (,) <$> bigPat <* (m_reservedOp ";") <*> block name
  pure $ case more of
    Just (p, rest) -> (e,p) :& rest
    Nothing -> e

bigExpr :: String -> Parser (Expr String)
bigExpr name = do
  f <- smallExpr name
  args <- (m_whiteSpace *> smallExpr name) `myManyTill` end
  pure (foldl (:/) f args)
 where
  myManyTill :: Parser a -> Parser end -> Parser [a]
  myManyTill p end = ([] <$ lookAhead end) <|> try ((:) <$> p <*> (p `myManyTill` end)) <|> pure []

  end :: Parser ()
  end = m_whiteSpace *>
        (() <$ (try (string name))
         <|> try (m_identifier *> optional (m_angles (m_commaSep nat)) *> m_reservedOp ":")
         <|> (() <$ char ')')
         <|> eof
        )

smallExpr :: String -> Parser (Expr String)
smallExpr name = buildExpressionParser (binaryTable (:$) ++ unaryTable) atom <?> "expression"
 where
  atom :: Parser (Expr String)
  atom = try pair
     <|> try (m_parens (oddOr (bigExpr name) (:$)))
     <|> m_parens (block name)
     <|> try recursive
     <|> ident
     <|> literal (:$)
     <|> vec (block name) (:$)

  ident :: Parser (Expr String)
  ident = EVar <$> m_identifier

  pair :: Parser (Expr String)
  pair = m_parens $ do
    e1 <- block name
    m_comma
    e2 <- block name
    return ("pair" :$ [e1, e2])

  recursive :: Parser (Expr String)
  recursive = do
    f <- id <$> m_identifier
    nats <- m_angles (m_commaSep nat)
    return (Rec f (Just nats))

bigPat :: Parser (Pat String)
bigPat = try (oddOr medPat (:?))

medPat :: Parser (Pat String)
medPat = buildExpressionParser (binaryTable (:?)) smallPat <?> "pattern"

smallPat :: Parser (Pat String)
smallPat = try pair
   <|> m_parens bigPat
   <|> ident
   <|> literal (:?)
   <|> vec bigPat (:?)
 where
  ident :: Parser (Pat String)
  ident = PV <$> m_identifier

  pair :: Parser (Pat String)
  pair = m_parens $ do
    p1 <- bigPat
    m_comma
    p2 <- bigPat
    return ("pair" :? [p1, p2])


nat :: Parser (Nat Z String)
nat = (NVar . FV <$> m_identifier)
      <|> (m_reserved "Z" *> pure Zer)
      <|> (m_reserved "S" *> (Suc <$> nat))
      <|> (m_reserved "D" *> (Dub <$> nat))
      <|> (m_reserved "F" *> (Ful <$> nat))
      <|> try (m_reserved "2^" *> (Suc . Ful <$> nat))
      <|> numLit
 where
  numLit = (read <$> some digit) <&> \n -> nTimes n Suc Zer

clause ::  String -> Parser RawClause
clause name = do
  name <- string name
  nats <- optionMaybe $ m_angles (m_commaSep nat)
  m_whiteSpace
  pats <- many (smallPat <* m_whiteSpace)
  m_reservedOp "="
  rhs <- block name
  return (name, nats, pats, rhs)

signature :: Parser (String, RawScheme)
signature = do
  name <- m_identifier
  natVars <- m_angles (m_commaSep m_identifier) <|> pure []
  m_reservedOp ":"
  (inputs, output) <- sigTy
  pure (name, (natVars, inputs, output))
 where
  sigTy :: Parser ([RawType], RawType)
  sigTy = helper <$> bigTy

  helper :: RawType -> ([RawType], RawType)
  helper (a :-> b) = let (ins, out) = helper b in (a:ins, out)
  helper ty = ([], ty)

bigTy :: Parser RawType
bigTy = do
  s <- smallTy
  ((s :->) <$ m_reservedOp "->" <*> bigTy) <|> pure s

smallTy :: Parser RawType
smallTy = m_parens (bracketedThing =<< m_commaSep bigTy) <|> vecTy
 where
  bracketedThing :: [RawType] -> Parser RawType
  bracketedThing [] = pure Unit
  bracketedThing [x] = pure x
  bracketedThing [x, y] = pure $ Prod x y
  bracketedThing _ = fail "Too many arguments to tuple"

  vecTy :: Parser RawType
  vecTy = groundTyOrVar >>= \case
    Right ty -> pure ty
    Left (NVar v) -> optionMaybe (m_reserved "of") >>= \case
      Nothing -> pure $ TVar v
      Just () -> (:^ NVar v) <$> smallTy
    Left num -> (:^ num) <$ m_reserved "of" <*> smallTy

  -- Hack for dealing in unsigned ints
  intTy :: Parser RawType
  intTy = (Bit :^) <$ m_reserved "Int" <*> m_angles nat

  groundTyOrVar :: Parser (Either (Nat Z String) RawType)
  groundTyOrVar = try (Right ("Bit" :* []) <$ m_reserved "Bit")
                  <|> try (Right <$> intTy)
                  <|> (Left <$> nat)

defn :: Parser (String, (RawScheme, [RawClause]))
defn = do
  sig@(name, scm) <- signature
  m_whiteSpace
  cs <- many (try (clause name))
  pure (name, (scm, cs))

defns :: Parser [(String, (RawScheme, [RawClause]))]
defns = many defn

parseDefs :: String -> [(String, (RawScheme, [RawClause]))]
parseDefs str = case parse (m_whiteSpace >> defns <* m_whiteSpace <* eof) "" str of
  Left e  -> error $ show e
  Right r -> r

parseFile :: String -> IO [(String, (RawScheme, [RawClause]))]
parseFile name = do
  text <- readFile name
  return (parseDefs text)
