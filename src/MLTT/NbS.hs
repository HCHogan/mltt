module MLTT.NbS where

import Data.Map qualified as Map
import Effectful
import Effectful.Error.Static
import Effectful.Reader.Static

type Name = String

data Expr
  = Var Name
  | Type Int
  | Pi Name Expr Expr
  | Lam Name Expr Expr
  | App Expr Expr
  deriving (Show, Eq)

-- We can define some built-in type in the free variable context:
-- [("Nat", Type 0), ("Zero", Var "Nat"), ("Succ", ...)]

type Env = Map.Map Name Expr

infer :: (Error String :> es, Reader Env :> es) => Expr -> Eff es Expr
infer = \case
  Var x -> do
    env <- ask
    case Map.lookup x env of
      Just expr -> pure expr
      Nothing -> throwError $ "Variable not found: " ++ x
  Type u -> return $ Type $ u + 1
  Pi x a b -> do
    u1 <- isType a
    u2 <- local (Map.insert x a) $ isType b
    return $ Type $ max u1 u2
  Lam x a b -> do
    _ <- isType a
    _ <- local (Map.insert x a) $ isType b
    return $ Pi x a b
  App a b -> do
    t1 <- infer a
    nt1 <- normalize t1
    t2 <- infer b
    case nt1 of
      Pi x a' b' -> do
        if a' == t2
          then subst x b b'
          else throwError $ "Type mismatch in application: " ++ show t1 ++ " and " ++ show t2
      _ -> throwError $ "Expected a function type, but got: " ++ show t1

isType :: (Error String :> es, Reader Env :> es) => Expr -> Eff es Int
isType expr = do
  t <- infer expr
  case t of
    Type u -> return u
    _ -> throwError $ "Expected a type, but got: " ++ show t

-- stupid subst implementation, throwerror if name occur
subst :: (Error String :> es) => Name -> Expr -> Expr -> Eff es Expr
subst n s = \case
  Var x | x == n -> return s
  Var v -> return $ Var v
  Type t -> return $ Type t
  Lam x a b
    | x == n -> Lam x <$> subst n s a <*> return b
  Lam x a b -> do
    checkOccur n a
    checkOccur n b
    Lam x <$> subst n s a <*> subst n s b
  Pi x a b
    | x == n -> Pi x <$> subst n s a <*> return b
  Pi x a b -> do
    checkOccur n a
    checkOccur n b
    Pi x <$> subst n s a <*> subst n s b
  App a b -> do
    App <$> subst n s a <*> subst n s b

normalize :: (Error String :> es) => Expr -> Eff es Expr
normalize = \case
  Var x -> return $ Var x
  Type u -> return $ Type u
  Pi x a b -> Pi x <$> normalize a <*> normalize b
  Lam x a b -> Lam x <$> normalize a <*> normalize b
  App f arg -> do
    nf <- normalize f
    narg <- normalize arg
    case nf of
      Lam x _ b -> subst x narg b
      _ -> return $ App nf narg

checkOccur :: (Error String :> es) => Name -> Expr -> Eff es ()
checkOccur n expr = do
  nexpr <- normalize expr
  case nexpr of
    Var x | x == n -> throwError $ "Variable occurs in itself: " ++ n
    Var _ -> return ()
    Type _ -> return ()
    Pi x a b -> do
      if x == n
        then return ()
        else do
          checkOccur n a
          checkOccur n b
    Lam x a b -> do
      if x == n
        then return ()
        else do
          checkOccur n a
          checkOccur n b
    App f arg -> do
      checkOccur n f
      checkOccur n arg

exprAreEqual :: (Error String :> es) => Expr -> Expr -> Eff es Bool
exprAreEqual e1 e2 = do
  e1' <- normalize e1
  e2' <- normalize e2
  return $ alphaEq Map.empty e1' e2'

alphaEq :: Map.Map Name Name -> Expr -> Expr -> Bool
alphaEq m e1 e2 = case (e1, e2) of
  (Var x, Var y) -> case Map.lookup x m of
    Just y' -> y == y'
    Nothing -> x == y
  (Type u1, Type u2) -> u1 == u2
  (Pi x a b, Pi y c d) -> alphaEq m a c && alphaEq (Map.insert x y m) b d
  (App f1 x1, App f2 x2) -> alphaEq m f1 f2 && alphaEq m x1 x2
  _ -> False
