{-# LANGUAGE DataKinds #-}

module Dynamics where

import Data.List
import Data.Maybe (fromJust)

import Hasochism
import Syntax

import Debug.Trace

track = const id

type VTy = Type Z Integer

data Val
 = String :$: [Val]                -- non-vector value constructors
 | Vec [Val]                       -- vector values
 | Vap [Val]                       -- vector-of-functions as function-on-vectors
 | VRec String [Integer] [Type Z String] [Val]     -- partially applied global defs
 deriving (Eq, Show)

type GEnv = [(String, (RawScheme, [RawClause]))]
type NEnv = [(String, Integer)]
type VEnv = [(String, Val)]
data Env = Env
  { globals :: GEnv
  , numbers :: NEnv
  , values  :: VEnv
  }

nat :: NEnv -> Nat Z String -> Integer
nat _ n | track ("NAT: " ++ show n) False = undefined
nat nenv (NVar (FV x)) = case lookup x nenv of Just i -> i
nat _     Zer    = 0
nat nenv (Suc n) = 1 + nat nenv n
nat nenv (Dub n) = 2 * nat nenv n
nat nenv (Ful n) = 2 ^ nat nenv n - 1

expr :: Env -> Expr String -> Val
expr _ e | track ("EXPR: " ++ show e) False = undefined
expr env (EVar x) = case lookup x (values env) of Just v -> v
expr env (c :$ es) = construct c (expr env <$> es)
expr env (Rec g (Just ns)) = run (globals env) g (nat (numbers env) <$> ns) [] []
expr env (e :/ arg) = apply (globals env) (expr env e) (expr env arg)
expr env ((e, p) :& k) = case match p (expr env e) of
  Just venv -> expr (env {values = venv ++ values env}) k

construct :: String -> [Val] -> Val
construct "nil" [] = Vec []
construct "cons" [v, Vec vs] = Vec (v : vs)
construct "snoc" [Vec vs, v] = Vec (vs ++ [v])
construct "even" [Vec vs, Vec ws] | length vs == length ws = Vec (vs ++ ws)
construct "odd" [Vec vs, v, Vec ws]  | length vs == length ws = Vec (vs ++ v : ws)
construct "riffle" [Vec vs, Vec ws] | length vs == length ws
  = Vec (concat (transpose [vs, ws]))
construct "vap" [Vec fs] = Vap fs
construct c vs = c :$: vs

apply :: GEnv -> Val -> Val -> Val
apply _ f a | track ("APPLY: " ++ show (f, a)) False = undefined
apply genv (VRec g is ts vs) v = run genv g is ts (vs ++ [v])
apply genv (Vap fs) (Vec as) = Vec (applies fs as) where
  applies [] [] = []
  applies (f : fs) (a : as) = apply genv f a : applies fs as

run :: GEnv
    -> String        -- The function to run (has to be in GEnv)
    -> [Integer]     -- Ω: Nat args
    -> [Type Z String] -- Λ: Type args (parameterised by Ω)
    -> [Val]         -- term args to the function
    -> Val
run _ g is ts vs | track (show (g, is, ts, vs)) False = undefined
run genv g is ts vs
  | Just (_, cs) <- lookup g genv
  , Just v <- try cs
  = v
 where
  try :: [RawClause] -> Maybe Val
  try [] = Nothing
  try ((_, ns, ps, e) : _)
    -- TODO: Fill in the nats that we solved by typechecking :-)
    | Just nenv <- row natch (fromJust ns) is
    , Just venv <- row match ps vs
    = Just (expr (Env {globals = genv, numbers = nenv, values = venv}) e)
  try (_ : cs) = try cs
run _ g is ts vs = VRec g is ts vs

row :: Monoid m => (a -> b -> Maybe m) -> [a] -> [b] -> Maybe m
row f [] [] = Just mempty
row f (a : as) (b : bs) = do
  m <- f a b
  n <- row f as bs
  pure (m <> n)
row _ _ _ = Nothing

natch :: Nat Z String -> Integer -> Maybe [(String, Integer)]
natch (NVar (FV x)) i = Just [(x, i)]
natch  Zer    i = if i == 0 then Just [] else Nothing
natch (Suc p) i = if i > 0 then natch p (i - 1) else Nothing
natch (Dub p) i = case divMod i 2 of
  (j, 0) -> natch p j
  _ -> Nothing
natch (Ful p) i = do
  j <- luf i
  natch p j
 where
  luf i = case divMod i 2 of
    (0, 0) -> pure 0
    (j, 1) -> (1+) <$> luf j
    _ -> Nothing

match :: Pat String -> Val -> Maybe VEnv
match (PV x) v = pure [(x, v)]
match ("nil" :? []) (Vec []) = pure []
match ("cons" :? ps) (Vec (v : vs)) = row match ps [v, Vec vs]
match ("snoc" :? ps) (Vec vs@(_:_)) = row match ps [Vec (init vs), last vs]
match ("even" :? ps) (Vec vs) = case divMod (length vs) 2 of
  (n, 0) -> case splitAt n vs of (us, ws) -> row match ps [Vec us, Vec ws]
  _ -> Nothing
match ("odd" :? ps) (Vec vs) = case divMod (length vs) 2 of
  (n, 1) -> case splitAt n vs of (us, v : ws) -> row match ps [Vec us, v, Vec ws]
  _ -> Nothing
match ("riffle" :? ps) (Vec vs) = case divMod (length vs) 2 of
  (n, 0) -> case deal vs of (us, ws) -> row match ps [Vec us, Vec ws]
  _ -> Nothing
 where
  deal [] = ([], [])
  deal (x : xs) = let (ys, zs) = deal xs in (x : zs, ys)
match (c :? ps) (d :$: vs) | d == c = row match ps vs
match _ _ = Nothing

pretty :: Val -> String
pretty (c :$: []) = c
pretty (Vec vs) = "[" ++ intercalate ", " (pretty <$> vs) ++ "]"
pretty v = "(" ++ show v ++ ")"
