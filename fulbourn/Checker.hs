{-# LANGUAGE DataKinds, GADTs, LambdaCase #-}

module Checker where

import Bwd
--import Constructors
import Hasochism
import Norm
import Syntax
import Util

import Control.Applicative
import Control.Monad
import Control.Monad.Except
import Control.Monad.State
import Data.Bifunctor
import Data.Either (fromRight)
import Data.Functor
import Data.List (nub)
import Data.Maybe
import Data.Type.Equality ((:~:)(..))

import Debug.Trace

track = const id

data Scheme n = Mono (Type n Name) | Pi (Scheme (S n)) | All (Scheme (S n))
 deriving Show

elabScheme :: RawScheme -> Checking (Scheme Z)
elabScheme (ns, inTys, outTy) = do
  checkVarsDistinct
  bind All S0 typeVars $ \stk ->
    bind Pi stk ns $ \stk ->
      Mono <$> (abstractTy stk rawType)
 where
  bind :: (forall n. Scheme (S n) -> Scheme n) -- Either All or Pi
       -> Stack String i -- Accumulator
       -> [String] -- Things we want to bind
       -> (forall j. Stack String j -> Checking (Scheme j))
       -> Checking (Scheme i)
  bind q stk [] k = k stk
  bind q stk (x:xs) k = q <$> bind q (stk :<< x) xs k

  findVar :: Stack String i -> String -> Checking (VVar i)
  findVar S0 x = typeErr (Misc $ "Couldn't abstract " ++ x)
  findVar (zx :<< x) y
   | x == y = pure VZ
   | otherwise = VS <$> findVar zx y

  abstractTy :: Stack String i -> RawType -> Checking (Type i a)
  abstractTy stk (TVar (FV x)) = TVar . BV <$> findVar stk x
  abstractTy stk (c :* tys) = (c :*) <$> traverse (abstractTy stk) tys
  abstractTy stk (s :-> t) = (:->) <$> abstractTy stk s <*> abstractTy stk t
  abstractTy stk (ty :^ n) = (:^) <$> abstractTy stk ty <*> abstractNum stk n

  abstractNum :: Stack String i -> Nat Z String -> Checking (Nat i a)
  abstractNum stk (NVar (FV x)) = NVar . BV <$> findVar stk x
  abstractNum stk Zer = pure Zer
  abstractNum stk (Suc n) = Suc <$> abstractNum stk n
  abstractNum stk (Dub n) = Dub <$> abstractNum stk n
  abstractNum stk (Ful n) = Ful <$> abstractNum stk n

  rawType :: Type Z String
  rawType = foldr (:->) outTy inTys

  typeVars = nub (getTypeVars rawType)

  checkVarsDistinct :: Checking ()
  checkVarsDistinct = if length (ns ++ typeVars) == length (nub (ns ++ typeVars))
                      then pure ()
                      else typeErr (Misc "Duplicated type var")


  getTypeVars :: RawType -> [String]
  getTypeVars (TVar (FV x)) = [x]
  getTypeVars (_ :* ts) = ts >>= getTypeVars
  getTypeVars (s :-> t) = getTypeVars s ++ getTypeVars t
  getTypeVars (x :^ _) = getTypeVars x

  mkStk :: Stack a i -> [a] -> Some (Stack a)
  mkStk stk [] = Some stk
  mkStk stk (x:xs) = mkStk (stk :<< x) xs



-- TODO: Types take the type of free variables, and the number bound variables
type MonoTy = Type Z Name
type Number = VNum Name

data CtxEntry
 = Defn String (Scheme Z) -- User's name - invariant: These go at the start
 | LockNums
 | LockTyVars
 | HasTy String MonoTy -- User's name
 | HasVal String Number -- User's name
 | DeclTy Name (Maybe MonoTy)
 | DeclNum Name (Maybe Number)
 | BeginCheckClause String
 | Postponed Number Number -- They should depend on the same free variable;
 deriving Show             -- not obviously true or false

printCtx :: Ctx -> IO ()
printCtx ctx = () <$ traverse print ctx

type Ctx = Bwd CtxEntry

seek :: Ctx -> (CtxEntry -> Maybe a) -> Maybe a
seek B0 f = Nothing
seek (zx :< x) f = f x <|> seek zx f

lookupDefn :: String -> Checking (Scheme Z)
lookupDefn f = do
  ctx <- gets snd
  let msg = seek ctx $ \case
       Defn g sg | f == g -> Just sg
       _ -> Nothing
  case msg of
    Nothing -> typeErr (Misc "Defn not found in context")
    Just sg -> pure sg

type Name = Int

-- defnNat :: Name -> Nat Name -> Checking ()
-- defnNat x n = modify $ \env -> env { nats = (x,n):nats env }

typeErr :: TError -> Checking a
typeErr = throwError

data TError = Misc String deriving Show

-- Checking monad, needs to run our solver; make definitions?
type Checking = ExceptT TError (State (Int, Ctx))

-- TODO:
--  * Normalise Monotypes wrt the context
--  * And normalise other things wrt the context (incl. CtxEntry)
--  * pushing and popping bits of context for let statements
--  * Scheme instantiation - turn typescheme vars into ctx vars, list of nums & monotype out
--  * Process quantity patterns; yielding constraints on numbers in ctx
--  * Work out when to normalise numbers, and do it

-- TODO: Do this renaming in a well kinded way, instead of hoping we get lucky
-- when we look up an index in the stack
subst :: Stack (Either MonoTy Number) i -> Type i Name -> MonoTy
subst stk (TVar (BV i)) = case stk !!! i of
  Left ty -> ty
subst stk (TVar (FV v)) = TVar (FV v)
subst stk (con :* tys) = con :* (subst stk <$> tys)
subst stk (s :-> t) = subst stk s :-> subst stk t
subst stk (t :^ n) = subst stk t :^ (substNat stk n)

substNat :: Stack (Either MonoTy Number) i -> Nat i Name -> Nat Z Name
substNat stk (NVar (BV i)) = case stk !!! i of
  Right n -> denorm n
substNat stk (NVar (FV v)) = NVar (FV v)
substNat stk Zer = Zer
substNat stk (Suc n) = Suc (substNat stk n)
substNat stk (Dub n) = Dub (substNat stk n)
substNat stk (Ful n) = Ful (substNat stk n)

addToCtx :: CtxEntry -> Checking ()
addToCtx entry = modify $ \(ns, ctx) -> (ns, ctx :< entry)

guessTy :: Checking MonoTy
guessTy = do
  name <- fresh
  addToCtx (DeclTy name Nothing)
  return (TVar (FV name))

guessNum :: Checking Number
guessNum = do
  name <- fresh
  addToCtx (DeclNum name Nothing)
  return (vvar name)

initTypeScheme :: Scheme Z -> Checking ([Number], MonoTy)
initTypeScheme = worker S0
 where
  worker :: Stack (Either MonoTy Number) i -> Scheme i -> Checking ([Number], MonoTy)
  worker stk (Mono ty) = pure $ ([], subst stk ty)
  worker stk (All scm) = guessTy >>= \ty -> worker (stk :<< Left ty) scm
  worker stk (Pi scm) = do
    n <- guessNum
    (ns, ty) <- worker (stk :<< Right n) scm
    pure (n:ns, ty)

lookupNum :: Name -> Checking (Maybe Number)
lookupNum n = do
  ctx <- gets snd
  pure $ seek ctx $ \case
    DeclNum n' m | n == n' -> m
    _ -> Nothing

lookupTy :: Name -> Checking (Maybe MonoTy)
lookupTy n = do
  ctx <- gets snd
  pure $ seek ctx $ \case
    DeclTy n' m | n == n' -> m
    _ -> Nothing

lookupUserNum :: String -> Checking Number
lookupUserNum str = do
  ctx <- gets snd
  let res = seek ctx $ \case
       HasVal a n | a == str -> Just n
       _ -> Nothing
  case res of
    Nothing -> typeErr (Misc $ "Couldn't find " ++ show str ++ " in context")
    Just n -> pure n

updateNum :: Number -> Checking Number
updateNum n = case getVar n of
  Just v -> lookupNum v >>= \case
    Nothing -> pure n
    Just num -> pure $ normSubst num n
  Nothing -> pure n

-- N.B. Arguments are in normal form, but aren't necessarily normalised wrt the
-- current context, so need freshening up
constrainNum :: Number -> Number -> Checking ()
constrainNum i j = do
  i <- updateNum i
  j <- updateNum j
  case (getVar i, getVar j, i == j) of
    (_, _, True) -> pure ()
    (Nothing, Nothing, _) -> typeErr (Misc $ show i ++ " != " ++ show j)
    (Just x, Just y, _)
     | x == y -> addToCtx (Postponed i j)
    _ -> solveNum i j

updateTy :: MonoTy -> Checking MonoTy
updateTy ty@(TVar (FV v)) = lookupTy v >>= \case
  Nothing -> pure ty
  Just ty -> pure ty
updateTy (c :* ts) = (c :*) <$> traverse updateTy ts
updateTy (s :-> t) = (:->) <$> updateTy s <*> updateTy t
updateTy (ty :^ n) = do
  ty <- updateTy ty
  n <- normNatChk n >>= updateNum
  pure (ty :^ denorm n)

constrainTy :: MonoTy -> MonoTy -> Checking ()
constrainTy s t = do
  s <- updateTy s
  t <- updateTy t
  if s == t
  then pure ()
  else case (s, t) of
    (c :* tys, d :* uys) | c == d -> constrainTys tys uys
    (s :-> t, u :-> v) -> constrainTy s u *> constrainTy t v
    (t :^ n, u :^ m) -> do
      constrainTy t u
      n <- normNatChk n
      m <- normNatChk m
      constrainNum n m
    (TVar (FV al), _) -> defTy al t
    (_, TVar (FV al)) -> defTy al s
    _ -> typeErr (Misc $ "Can't unify " ++ show s ++ " and " ++ show t)
 where
  constrainTys [] [] = pure ()
  constrainTys (x:xs) (y:ys) = constrainTy x y *> constrainTys xs ys
  constrainTys _ _ = typeErr (Misc $ "Can't unify " ++ show s ++ " and " ++ show t)

pop :: Checking CtxEntry
pop = do
  (ns, ctx) <- get
  case ctx of
    B0 -> typeErr (Misc "Ctx underflow")
    (zx :< x) -> x <$ put (ns, zx)

repush :: CtxEntry -> Checking ()
repush (HasVal s n) = do
  n <- updateNum n
  addToCtx (HasVal s n)
repush (HasTy s ty) = do
  ty <- updateTy ty
  addToCtx (HasTy s ty)
repush (DeclNum j (Just n)) = do
  n <- updateNum n
  addToCtx (DeclNum j (Just n))
repush (DeclTy al (Just ty)) = do
  ty <- updateTy ty
  addToCtx (DeclTy al (Just ty))
repush (Postponed n m) = do
  n <- updateNum n
  m <- updateNum m
  if n == m
  then pure ()
  else addToCtx (Postponed n m)
repush entry = addToCtx entry

defTy :: Name -> MonoTy -> Checking ()
defTy name ty = worker []
 where
  worker :: [CtxEntry] -> Checking ()
  worker deps = pop >>= \case
    LockTyVars -> typeErr (Misc $ "Trying to instantiate a parametric type variable: " ++ show name)
    d@(DeclTy al Nothing) -> case (al == name, al `elem` ty, ty == TVar (FV al)) of
      (_, _, True) -> addToCtx (DeclTy al (Just (TVar (FV name))))
      (False, True, _) -> worker (d:deps)
      (True, True, _) -> typeErr (Misc $ "Type " ++ show ty ++ " is infinite")
      (True, False, _) -> do
        traverse addToCtx deps
        addToCtx (DeclTy al (Just ty))
      _ -> worker deps *> repush d
    d@(DeclNum j Nothing) | j `elem` ty -> worker (d:deps)
    z -> worker deps *> repush z

-- Invariant: `num` is normal and doesn't depend on `name`
defNum :: Name -> Number -> Checking ()
defNum name num = worker Nothing
 where
  -- If we find the definition of the variable that's used in `num`, we pick it up
  -- from the context and carry it in the first argument of this function. When we
  -- find the declaration of `name`, we'll put the dependency first to keep the
  -- context well scoped.
  worker :: Maybe Name -> Checking ()
  worker dep = pop >>= \case
    LockNums -> typeErr (Misc "Trying to instantiate a parametric number variable")
    DeclNum k Nothing
     | name == k -> do
        case dep of
          Nothing -> pure ()
          Just dep -> addToCtx (DeclNum dep Nothing)
        addToCtx (DeclNum k (Just num))
     | vvar k == num -> addToCtx (DeclNum k (Just (vvar name)))
     | getVar num == Just k -> worker (Just k)
    z -> worker dep *> repush z

-- Invariant: We don't have the same variable on both sides; there is a variable on both sides
solveNum :: Number -> Number -> Checking ()
solveNum (VNum up f00) (VNum wp g00)
 | up >= wp = solve00 g00 (VNum (up - wp) f00)
 | otherwise = solve00 f00 (VNum (wp - up) g00)
 where
  solve00 Const0 (VNum 0 f00) = make0F00 f00
  solve00 Const0 nv = typeErr (Misc $ show nv ++ " != 0")
  solve00 (Strict (Monotone 0 op)) nv = solveOp op nv
  solve00 (Strict (Monotone k op)) nv = do
    halfNV <- makeEven nv
    solve00 (Strict (Monotone (k - 1) op)) halfNV

  solveOp (NumVar j) nv = defNum j nv
  solveOp (Full mono) (VNum 0 (Strict (Monotone 0 (Full nono)))) = solve00 (Strict mono) (toVNum nono)
  solveOp (Full mono) (VNum 0 f00) = solve00 f00 (toVNum (Full mono))
  solveOp (Full mono) (VNum up f00) = do
    monoPred <- makeSucc mono
    solveNum (vdoub (vfull monoPred)) (VNum (up - 1) f00)

  make0F00 :: Fun00 Name -> Checking ()
  make0F00 Const0 = pure ()
  make0F00 (Strict (Monotone _ op)) = make0Op op

  make0Op (NumVar j) = defNum j vzero
  make0Op (Full (Monotone _ op)) = make0Op op

  makeEven :: Number -> Checking Number
  makeEven (VNum up f00) = case up `divMod` 2 of
    (hup, 0) -> vadd hup <$> makeEven00 f00
    (hup, 1) -> vadd (hup + 1) <$> makeOdd00 f00

  makeEven00 :: Fun00 Name -> Checking Number
  makeEven00 Const0 = pure vzero
  makeEven00 (Strict (Monotone 0 op)) = makeEvenOp op
  makeEven00 (Strict (Monotone k op)) = pure . toVNum $ Monotone (k - 1) op

  makeEvenOp :: Operator Name -> Checking Number
  makeEvenOp (NumVar j) = do
    k <- guessNum
    defNum j (vdoub k)
    pure k
  makeEvenOp (Full mono) = do
    make0F00 (Strict mono)
    pure vzero

  makeOdd00 :: Fun00 Name -> Checking Number
  makeOdd00 (Strict (Monotone 0 op)) = makeOddOp op
  makeOdd00 f00 = typeErr (Misc $ "Can't make " ++ show f00 ++ " odd")

  makeOddOp (NumVar j) = do
    k <- guessNum
    defNum j (vsucc (vdoub k))
    pure k
  makeOddOp (Full mono) = do
    monoPred <- makeSucc mono
    pure $ vfull monoPred

  makeSucc :: Mono Name -> Checking Number
  makeSucc (Monotone k op) = do
    opPred <- makeSuccOp op
    pure (vadd (full k) (vdoubs k opPred))

  makeSuccOp :: Operator Name -> Checking Number
  makeSuccOp (NumVar j) = do
    k <- guessNum
    defNum j (vsucc k)
    pure k
  makeSuccOp (Full mono) = vdoub . vfull <$> makeSucc mono

processQPats :: [Nat Z String] -> [Number] -> Checking [Nat Z Name]
processQPats [] [] = pure []
processQPats (q:qs) (n:ns) = (:) <$> processQPat q n <*> processQPats qs ns

processQPat :: Nat Z String -> Number -> Checking (Nat Z Name)
processQPat (NVar (FV "_")) n = denorm n <$ pure ()
processQPat (NVar (FV s)) n = denorm n <$ addToCtx (HasVal s n)
processQPat Zer n = Zer <$ constrainNum vzero n
processQPat (Suc q) n = do
  j <- guessNum
  constrainNum (vsucc j) n
  Suc <$> processQPat q j
processQPat (Dub q) n = do
  j <- guessNum
  constrainNum (vdoub j) n
  Dub <$> processQPat q j
processQPat (Ful q) n = do
  j <- guessNum
  constrainNum (vfull j) n
  Ful <$> processQPat q j

data PatStatus = Refutable | Irrefutable

-- Only deals with explicit types, not metavariables
processVPats :: MonoTy -> [Pat String] -> Checking MonoTy
processVPats ty [] = pure ty
processVPats (src :-> tgt) (p:ps) = do
  processVPat Refutable src p
  processVPats tgt ps

conSaturated :: String -> MonoTy -> Checking ()
conSaturated c (_ :-> _) = typeErr (Misc $ "Constructor " ++ show c ++ " not fully applied")
conSaturated _ _ = pure ()

processVPat :: PatStatus -> MonoTy -> Pat String -> Checking ()
processVPat patstat ty (PV x) = addToCtx (HasTy x ty)
processVPat patstat ty (c :? pargs) = case lookup c ctorTbl of
  Just scm | permitted patstat c -> do
    (_, argsTy) <- initTypeScheme scm
    outTy <- processVPArgs argsTy pargs
    conSaturated c outTy
    constrainTy ty outTy
  _ -> typeErr (Misc $ "Couldn't match constructor " ++ show c)
 where
  permitted :: PatStatus -> String -> Bool
  permitted Irrefutable c | c `elem` ["tt", "ff"] = False
  permitted _ _ = True

  processVPArgs :: MonoTy -> [Pat String] -> Checking MonoTy
  processVPArgs ty [] = pure ty
  processVPArgs (s :-> t) (p:ps) = do
    processVPat patstat s p
    processVPArgs t ps

normNatChk :: Nat Z Name -> Checking Number
normNatChk = normaliseNat f
 where
  f :: Name -> Checking Number
  f j = lookupNum j <&> \case
    Nothing -> vvar j
    Just n -> n

demandVecTy :: MonoTy -> Checking (MonoTy, Number)
demandVecTy ty = updateTy ty >>= \case
  (ty :^ n) -> (ty,) <$> normNatChk n
  ty -> do
    elemTy <- guessTy
    len <- guessNum
    constrainTy ty (elemTy :^ denorm len)
    pure (elemTy, len)

demandArr :: MonoTy -> Checking (MonoTy, MonoTy)
demandArr ty = updateTy ty >>= \case
  (s :-> t) -> pure (s, t)
  ty -> do
    s <- guessTy
    t <- guessTy
    constrainTy ty (s :-> t)
    pure (s, t)


win :: Checking ()
win = pure ()

fresh :: Checking Name
fresh = do
  (ns, ctx) <- get
  put (ns + 1, ctx)
  pure ns

ctorTbl :: [(String, Scheme Z)]
ctorTbl =
 [("nil", All (Mono (TVar (BV VZ) :^ Zer)))
 ,("cons", All (Pi (Mono (
           TVar (BV (VS VZ))
           :->
           (TVar (BV (VS VZ)) :^ NVar (BV VZ))
           :->
           (TVar (BV (VS VZ)) :^ Suc (NVar (BV VZ)))
           ))))
 ,("snoc", All (Pi (Mono (
           (TVar (BV (VS VZ)) :^ NVar (BV VZ))
           :->
           TVar (BV (VS VZ))
           :->
           (TVar (BV (VS VZ)) :^ Suc (NVar (BV VZ)))
           ))))
 ,("even", All (Pi (Mono (
           (TVar (BV (VS VZ)) :^ NVar (BV VZ))
           :->
           (TVar (BV (VS VZ)) :^ NVar (BV VZ))
           :->
           (TVar (BV (VS VZ)) :^ Dub (NVar (BV VZ)))
           ))))
 ,("riffle", All (Pi (Mono (
           (TVar (BV (VS VZ)) :^ NVar (BV VZ))
           :->
           (TVar (BV (VS VZ)) :^ NVar (BV VZ))
           :->
           (TVar (BV (VS VZ)) :^ Dub (NVar (BV VZ)))
           ))))
 ,("odd", All (Pi (Mono (
           (TVar (BV (VS VZ)) :^ NVar (BV VZ))
           :->
           TVar (BV (VS VZ))
           :->
           (TVar (BV (VS VZ)) :^ NVar (BV VZ))
           :->
           (TVar (BV (VS VZ)) :^ Suc (Dub (NVar (BV VZ))))
           ))))
 ,("pair", All (All (Mono (
           TVar (BV (VS VZ))
           :->
           TVar (BV VZ)
           :->
           ("Prod" :* [TVar (BV (VS VZ)), TVar (BV VZ)])
           ))))
 ,("tt", Mono Bit)
 ,("ff", Mono Bit)
 ]

checkArgs :: MonoTy -> [Expr String] -> Checking ([Expr (Either Name String)], MonoTy)
checkArgs ty args | track ("checkArgs\n  " ++ show ty ++ "\n  " ++ show args) False = undefined
checkArgs ty [] = pure ([], ty)
checkArgs ty (e:es) = do
  (s, t) <- demandArr ty
  e <- check s e
  (es, tau) <- checkArgs t es
  pure (e:es, tau)

-- Returns syntax with the hidden arguments in function calls filled in
-- Invariant: `Rec`s in output never contain `Nothing`, instead has only Left vars
-- Invariant: Term variables are Right String; type args are Left Name
check :: MonoTy -> Expr String -> Checking (Expr (Either Name String))
check ty (EVar x) = do
  ctx <- gets snd
  let mty = seek ctx $ \case
       HasTy y ty | x == y -> Just (Right ty)
       Defn str _ | str == x -> Just (Left ())
       _ -> Nothing
  case mty of
    Nothing -> typeErr (Misc $ "No type found in context for " ++ show x)
    Just (Right ty') -> EVar (Right x) <$ constrainTy ty ty'
    Just (Left ()) -> check ty (Rec x Nothing)
check ty ("vap" :$ [f]) = do
  fTys <- guessTy
  f <- check fTys f
  (fTy, len) <- demandVecTy fTys
  (s, t) <- demandArr fTy
  (ss, ts) <- demandArr ty
  (s', len') <- demandVecTy ss
  constrainTy s' s
  constrainNum len len'
  pure ("vap" :$ [f])
check ty (con :$ args) = case lookup con ctorTbl of
  Nothing -> typeErr (Misc $ "Constructor not found " ++ show con)
  -- TODO: Put a fence around this in the context and get rid of it?
  Just scm -> do
    (_, argsTy) <- initTypeScheme scm
    (args, outTy) <- checkArgs argsTy args
    conSaturated con outTy
    constrainTy ty outTy
    pure (con :$ args)
check ty (e :/ arg) = do
  fTy <- guessTy
  e <- check fTy e
  (s, t) <- demandArr fTy
  arg <- check s arg
  constrainTy ty t
  pure (e :/ arg)
check ty (Rec f nargs) = do
  scm <- lookupDefn f
  (ns, monoTy) <- initTypeScheme scm
  ns <- checkNums ns (natArgs nargs ns)
  constrainTy ty monoTy
  pure (Rec f (Just (fmap Left <$> ns)))
check ty ((e, p) :& body) = do
  t <- guessTy
  e <- check t e
  processVPat Irrefutable t p
  body <- check ty body
  pure ((e, Right <$> p) :& body)

checkNums :: [Number] -> [Nat Z String] -> Checking [Nat Z Name]
checkNums [] [] = pure []
checkNums (j:js) (n:ns) = do
  n <- checkNum j n
  ns <- checkNums js ns
  pure (n:ns)
 where
  checkNum :: Number -> Nat Z String -> Checking (Nat Z Name)
  checkNum j (NVar (FV "_")) = pure (denorm j)
  checkNum j (NVar (FV str)) = do
    m <- lookupUserNum str
    constrainNum j m
    pure (denorm j)
  checkNum j Zer = Zer <$ constrainNum j vzero
  checkNum j (Suc n) = do
    k <- guessNum
    constrainNum (vsucc k) j
    n <- checkNum k n
    pure (Suc n)
  checkNum j (Dub n) = do
    k <- guessNum
    constrainNum (vdoub k) j
    n <- checkNum k n
    pure (Dub n)
  checkNum j (Ful n) = do
    k <- guessNum
    constrainNum (vfull k) j
    n <- checkNum k n
    pure (Ful n)
checkNums _ _ = typeErr (Misc $ "Not enough type args given to function call")

cleanupClause :: Checking ()
cleanupClause = pop >>= \case
  BeginCheckClause _ -> pure ()
  Postponed i j -> typeErr (Misc $ "Couldn't solve " ++ show i ++ " = " ++ show j)
  _ -> cleanupClause


-- Invariant: The nat pats in the output are never Nothing
elabClause :: RawClause -> Checking RawClause
elabClause (f, qs, ps, e) = do
  addToCtx (BeginCheckClause f)
  sg <- lookupDefn f
  (ns, tau) <- initTypeScheme sg
  addToCtx LockTyVars
  qs <- processQPats (natArgs qs ns) ns
  tau <- processVPats tau ps
  addToCtx LockNums
  e <- check tau e
  qs <- reabstractQPats qs
  e <- reabstractExpr e
  cleanupClause
  pure (f, Just qs, ps, e)

instantiateNumVar :: [(Name, Nat Z String)] -> (a -> Name) -> Nat Z a -> Nat Z String
instantiateNumVar m getName (NVar (FV var)) = fromJust (lookup (getName var) m)
instantiateNumVar m _ Zer = Zer
instantiateNumVar m f (Suc n) =  Suc (instantiateNumVar m f n)
instantiateNumVar m f (Dub n) =  Dub (instantiateNumVar m f n)
instantiateNumVar m f (Ful n) =  Ful (instantiateNumVar m f n)


reabstractQPats :: [Nat Z Name] -> Checking [Nat Z String]
reabstractQPats ns = do
  m <- getNameMap
  pure $ instantiateNumVar m id <$> ns

getNameMap :: Checking [(Name, Nat Z String)]
getNameMap = do
  ctx <- gets snd
  pure $ catMaybes ((getThing <$> ctx) <>> [])
 where
  getThing :: CtxEntry -> Maybe (Name, Nat Z String)
  --getThing (HasTy str (TVar (FV name))) = Just (name, str)
  --getThing (HasTy str (TVar (FV name))) = Just (name, str)
  -- TODO: We can invert the numval, it shouldn't be hard
  getThing (HasVal str (VNum 0 (Strict (Monotone 0 (NumVar name))))) = Just (name, NVar (FV str))
  getThing (DeclNum name (Just num)) = Just (name, denorm $ fmap (('?':) . show) num)
  getThing (DeclNum name Nothing) = Just (name, NVar (FV ('?':show name)))
  getThing _ = Nothing

-- Expressions come out of the elaborator either with variables that are either
-- strings, or `Name`s that we need to update to be strings. We wait until after
-- typechecking to update the `Name`s so that we've solved all the ones we can
reabstractExpr :: Expr (Either Name String) -> Checking (Expr String)
reabstractExpr (EVar (Right x)) = pure (EVar x)
reabstractExpr (c :$ args) = (c :$) <$> traverse reabstractExpr args
reabstractExpr (f :/ arg) = (:/) <$> reabstractExpr f <*> reabstractExpr arg
reabstractExpr (Rec f (Just args)) = do
 defs <- getNameMap
 pure . Rec f . Just $ (worker' defs) <$> args
  where
   worker' :: [(Name, Nat Z String)] ->  Nat Z (Either Name String) -> Nat Z String
   worker' m = instantiateNumVar m $ \case
     Left name -> name

   -- Numbers should all have left thingys, but exprs should have rights
   worker :: [(Name, String)] -> Either Name String -> String
   worker m (Left name) = fromJust $ lookup name m
   worker m (Right str) = str

reabstractExpr ((e, p) :& body) = do
  e <- reabstractExpr e
  body <- reabstractExpr body
  pure ((e, myFromRight <$> p) :& body)
 where
  myFromRight (Right x) = x

testSolveNum :: ((Number, Number) -> (Number, Number)) -> Either TError Ctx
testSolveNum f = flip evalState (0, B0) $ runExceptT go
 where
  go :: Checking Ctx
  go = do
    j <- guessNum
    k <- guessNum
    let (m, n) = f (j, k)
    constrainNum m n
    gets snd

testCtx :: Ctx
testCtx = B0 :<
 Defn "sort"
 (All
  (Pi
   (Mono
    (let al = TVar (BV (VS VZ)); i = NVar (BV VZ) in
     (Prod al al :-> Prod al al)
     :->
     ((al :^ Suc (Ful i)) :-> (al :^ Suc (Ful i)))
    )))) :<
 Defn "merge"
 (All
  (Pi
   (Mono
    (let al = TVar (BV (VS VZ)); i = NVar (BV VZ) in
     (Prod al al :-> Prod al al)
     :->
     (al :^ Suc (Ful i))
     :->
     (al :^ Suc (Ful i))
     :->
     (al :^ Suc (Ful (Suc i)))
    ))))

testClause1 = ("sort", Just [Zer], [PV "cas", PV "in"], EVar "in")
testClause2 = ("sort", Nothing, [PV "cas", "cons" :? [PV "x", "nil" :? []]]
              ,Cons (EVar "x") Nil)
testClause2b = ("sort", Nothing, [PV "cas", "odd" :? [PV "xs", PV "x", PV "ys"]]
               ,Cons (EVar "x") Nil)
testClause3 = ("sort", Just [Suc (NVar (FV "n"))], [PV "cas", "even" :? [PV "xs", PV "ys"]]
              ,Rec "merge" (Just [NVar (FV "n")])
               :/ EVar "cas"
               :/ (Rec "sort" (Just [(NVar (FV "n"))])
                   :/ EVar "cas"
                   :/ EVar "xs"
                  )
               :/ (Rec "sort" (Just [(NVar (FV "n"))])
                   :/ EVar "cas"
                   :/ EVar "ys"
                  )
              )
testClause4 = ("sort", Nothing, [PV "cas", "even" :? [PV "xs", PV "ys"]]
              ,Rec "merge" Nothing
               :/ EVar "cas"
               :/ (Rec "sort" Nothing
                   :/ EVar "cas"
                   :/ EVar "xs"
                  )
               :/ (Rec "sort" Nothing
                   :/ EVar "cas"
                   :/ EVar "ys"
                  )
              )

{-
testSort :: RawClause -> IO ()
testSort c = case flip evalState (0, testCtx) $ runExceptT $ (checkClause c *> gets snd) of
  Right ctx -> printCtx ctx
  Left terr -> print terr
-}
