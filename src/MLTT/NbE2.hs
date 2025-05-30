module MLTT.NbE2 where

import Data.Map qualified as Map
import Effectful
import Effectful.Error.Static    (Error, runError, throwError)
import Effectful.Reader.Static   (Reader, runReader, ask)
import Effectful.State.Static    (State, runState, get, modify)
import MLTT.Syntax               (Expr(..), Name)

-- 1. 纯中间值和中性项
data PValue
  = PNe   PNeutral
  | PType Int
  | PPi   PValue (PValue -> PValue)
  | PLam  PValue (PValue -> PValue)

data PNeutral
  = PNVar Name
  | PNApp PNeutral PValue

-- 2. 评估：只用 Reader（环境）+ Error
type EvalEff es = ( Reader (Map.Map Name PValue) :> es
                  , Error String               :> es )

evalPureEff :: EvalEff es => Expr -> Eff es PValue
evalPureEff = \case
  Var x -> do
    env <- ask @(Map.Map Name PValue)
    case Map.lookup x env of
      Just v  -> pure v
      Nothing -> throwError $ "Variable not found: " ++ x

  Type u ->
    pure (PType u)

  Pi x ta tb -> do
    ta' <- evalPureEff ta
    env <- ask @(Map.Map Name PValue)
    let body v =
          case runEval (Map.insert x v env) tb of
            Right v' -> v'
            Left  e  -> error e
    pure (PPi ta' body)

  Lam x ta tb -> do
    ta' <- evalPureEff ta
    env <- ask @(Map.Map Name PValue)
    let body v =
          case runEval (Map.insert x v env) tb of
            Right v' -> v'
            Left  e  -> error e
    pure (PLam ta' body)

  App a b -> do
    f <- evalPureEff a
    v <- evalPureEff b
    case f of
      PLam _ body ->
        pure (body v)
      PNe ne ->
        pure (PNe (PNApp ne v))
      _ ->
        throwError "Expected a function"

