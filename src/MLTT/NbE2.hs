{-# LANGUAGE TemplateHaskell #-}

module MLTT.NbE2 where

import Control.Lens
import Data.Map qualified as Map
import Effectful
import Effectful.Error.Static
import Effectful.Reader.Static
import Effectful.State.Static.Local
import MLTT.Syntax

data PValue
  = PNe PNeutral
  | PType Int
  | PPi PValue (PValue -> PValue)
  | PLam PValue (PValue -> PValue)

data PNeutral
  = PNVar Name
  | PNApp PNeutral PValue

type VEnv = Map.Map Name PValue

type EvalEff es = (Reader VEnv :> es, Error String :> es)

eval :: (EvalEff es) => Expr -> Eff es PValue
eval = \case
  Var x -> do
    env <- ask @(Map.Map Name PValue)
    case Map.lookup x env of
      Just v -> pure v
      Nothing -> throwError $ "Variable not found: " ++ x
  Type u ->
    pure (PType u)
  Pi x ta tb -> do
    ta' <- eval ta
    env <- ask @(Map.Map Name PValue)
    let body v =
          case runEval (Map.insert x v env) tb of
            Right v' -> v'
            Left e -> error e
    pure (PPi ta' body)
  Lam x ta tb -> do
    ta' <- eval ta
    env <- ask @(Map.Map Name PValue)
    let body v =
          case runEval (Map.insert x v env) tb of
            Right v' -> v'
            Left e -> error e
    pure (PLam ta' body)
  App a b -> do
    f <- eval a
    v <- eval b
    case f of
      PLam _ body ->
        pure (body v)
      PNe ne ->
        pure (PNe (PNApp ne v))
      _ ->
        throwError "Expected a function"

runEval :: VEnv -> Expr -> Either String PValue
runEval env e = runPureEff $ runErrorNoCallStack $ runReader env $ eval e

type ReifyEff es = State [Name] :> es

runReify :: [Name] -> Eff '[State [Name]] Expr -> Expr
runReify names eff = runPureEff $ evalState names eff

reify :: (ReifyEff es) => PValue -> Eff es Expr
reify = \case
  PNe ne ->
    neutralToExprEff ne
  PType u ->
    pure (Type u)
  PPi ta body -> do
    taE <- reify ta
    x <- fresh
    let v = PNe (PNVar x)
        bVal = body v
    bE <- reify bVal
    pure (Pi x taE bE)
  PLam ta body -> do
    taE <- reify ta
    x <- fresh
    let v = PNe (PNVar x)
        bVal = body v
    bE <- reify bVal
    pure (Lam x taE bE)

neutralToExprEff :: (ReifyEff es) => PNeutral -> Eff es Expr
neutralToExprEff = \case
  PNVar x -> pure (Var x)
  PNApp n v -> do
    neE <- neutralToExprEff n
    vE <- reify v
    pure (App neE vE)

fresh :: (ReifyEff es) => Eff es Name
fresh = do
  used <- get @[Name]
  let go (i :: Int) =
        let x = "x" ++ show i
         in if x `elem` used then go (i + 1) else x
  let x = go 0
  modify (x :)
  pure x

type Env = Map.Map Name Expr

data Ctxt = Ctxt {_values :: VEnv, _names :: [Name], _types :: VEnv}

makeLenses ''Ctxt

addVar :: Name -> PValue -> Ctxt -> Ctxt
addVar n typ ctx =
  let v = PNe $ PNVar n
   in ctx
        & values %~ Map.insert n v
        & types %~ Map.insert n typ
        & names %~ (n :)

infer :: (Reader Ctxt :> es, Error String :> es) => Expr -> Eff es PValue
infer = \case
  Var x -> do
    typs <- asks (^. types)
    case Map.lookup x typs of
      Just t -> return t
      Nothing -> throwError $ "Variable not found: " ++ x
  Type u -> return (PType $ u + 1)
  Pi x a b -> do
    ua <- isType a
    vals <- asks (^. values)
    case runEval vals a of
      Right va -> do
        ub <- local (addVar x va) $ isType b
        return $ PType $ max ua ub
      Left err -> throwError err
  Lam x a b -> do
    _ <- isType a
    vals <- asks (^. values)
    case runEval vals a of
      Right va -> do
        vb <- local (addVar x va) $ infer b
        ns <- asks (^. names)
        let exprb = runReify ns $ reify vb
        return $
          PPi
            va
            ( \v -> case runEval (Map.insert x v vals) exprb of
                Right v' -> v'
                Left err -> error err
            )
      Left err -> throwError err
  App a b -> do
    ta <- infer a
    tb <- infer b
    case ta of
      PPi vta vb -> do
        flag <- valuesAreEqual vta tb
        vals <- asks (^. values)
        if flag
          then case runEval vals b of
            Right v -> return $ vb v
            Left err -> throwError err
          else
            throwError "Type mismatch"
      _ -> throwError "Expected a function type"

valuesAreEqual :: (Error String :> es, Reader Ctxt :> es) => PValue -> PValue -> Eff es Bool
valuesAreEqual v1 v2 = do
  ns <- asks (^. names)
  let e1 = runReify ns $ reify v1
  let e2 = runReify ns $ reify v2
  return $ e1 == e2

isType :: (Error String :> es, Reader Ctxt :> es) => Expr -> Eff es Int
isType expr = do
  t <- infer expr
  case t of
    PType u -> return u
    _ -> throwError "Expected a type"

normalize :: (Error String :> es) => VEnv -> [Name] -> Expr -> Eff es Expr
normalize env n expr = case runEval env expr of
  Right v -> return $ runReify n $ reify v
  Left err -> throwError $ "Evaluation error: " ++ err
