module MLTT.NbE where

import Data.Map qualified as Map
import Effectful
import Effectful.Error.Static
import Effectful.Reader.Static
import MLTT.Syntax

type VEnv es = Map.Map Name (Value es)

data Value es where
  VNe :: Neutural es -> Value es
  VType :: Int -> Value es
  VPi :: Value es -> (Value es -> Eff es (Value es)) -> Value es
  VLam :: Value es -> (Value es -> Eff es (Value es)) -> Value es

-- stuck
data Neutural es where
  NVar :: Name -> Neutural es
  NApp :: Neutural es -> Value es -> Neutural es

eval :: (Reader (VEnv es) :> es, Error String :> es) => Expr -> Eff es (Value es)
eval = \case
  Var x -> do
    env <- ask
    case Map.lookup x env of
      Just expr -> return expr
      Nothing -> throwError $ "Variable not found: " ++ x
  Type u -> return $ VType u
  Pi x ta tb -> do
    ta' <- eval ta
    let tb' v = local (Map.insert x v) $ eval tb
    return $ VPi ta' tb'
  Lam x ta tb -> do
    ta' <- eval ta
    let tb' v = local (Map.insert x v) $ eval tb
    return $ VLam ta' tb'
  App a b -> do
    f <- eval a
    case f of
      VLam _ tb -> do
        v <- eval b
        tb v
      VNe ne -> do
        v <- eval b
        return $ VNe $ NApp ne v
      _ -> throwError "Expected a function type"

valueToExpr :: (Reader [Name] :> es) => Value es -> Eff es Expr
valueToExpr = \case
  VNe ne -> neutralToExpr ne
  VType u -> return $ Type u
  VPi ta tb -> do
    taExpr <- valueToExpr ta
    x <- freshName
    bVal <- tb (VNe $ NVar x)
    bExpr <- local (x :) (valueToExpr bVal)
    return $ Pi x taExpr bExpr
  VLam ta tb -> do
    taExpr <- valueToExpr ta
    x <- freshName
    bVal <- tb (VNe (NVar x))
    bExpr <- local (x :) (valueToExpr bVal)
    pure (Lam x taExpr bExpr)

neutralToExpr :: (Reader [Name] :> es) => Neutural es -> Eff es Expr
neutralToExpr = \case
  NVar x -> return $ Var x
  NApp ne v -> App <$> neutralToExpr ne <*> valueToExpr v

freshName :: (Reader [Name] :> es) => Eff es Name
freshName = do
  go 0
  where
    go :: (Reader [Name] :> es) => Int -> Eff es Name
    go i = do
      names <- ask @[Name]
      let name = "x_" ++ show i
      if name `elem` names
        then go (i + 1)
        else return name
