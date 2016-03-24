--------------------------------------------------------------------------------
-- Copyright © 2011 National Institute of Aerospace / Galois, Inc.
--------------------------------------------------------------------------------

-- | A tagless interpreter for Copilot specifications.

{-# LANGUAGE Trustworthy #-} -- Because of Data.Map (Containers)
{-# LANGUAGE GADTs, BangPatterns, DeriveDataTypeable #-}

module Copilot.Core.Interpret.Eval
  ( --ExtEnv (..)
    Env
  , Output
  , ExecTrace (..)
  , eval
  ) where

import Copilot.Core
import Copilot.Core.Type.Dynamic
import Copilot.Core.Type.Show (showWithType, ShowType)

import Prelude hiding (id)
import qualified Prelude as P

import Data.List (transpose)
import qualified Data.Map as M
import Data.Map (Map)
import Data.Maybe (fromJust)
import Data.Bits
import Control.Exception (Exception, throw)
import Data.Typeable

--------------------------------------------------------------------------------

data InterpException
  = ArrayWrongSize Name Int
  | ArrayIdxOutofBounds Name Int Int
  | MatrixWrongRowSize Name Int
  | MatrixRowIdxOutofBounds Name Int Int
  | MatrixWrongColSize Name Int
  | MatrixColIdxOutofBounds Name Int Int
  | DivideByZero
  | NotEnoughValues Name Int
  | NoExtsInterp Name
--  | NoExtFunEval Name
--  | NoValues Name
--  | BadType Name
  deriving Typeable

instance Show InterpException where
  ---------------------------------------
  -- show (NoValues name)                                                         =
  --   badUsage $ "you need to supply a list of values for interpreting "
  --     ++ "external element " ++ name ++ "."
  ---------------------------------------

  -- -- Should always be caught by Analyze.hs in copilot-language.
  -- show (BadType name)                                                          =
  --   badUsage $ "you probably gave the wrong type for external element "
  --     ++ name ++ ".  Recheck your types and re-evaluate."
  ---------------------------------------
  show (ArrayWrongSize name expectedSize) =
    badUsage $ "in the environment for external array " ++ name
      ++ ", we expect a list of length " ++ show expectedSize
      ++ ", but the length of the array you supplied is of a different length."
  ---------------------------------------
  show (ArrayIdxOutofBounds name index size) =
    badUsage $ "in the environment for external array " ++ name
      ++ ", you gave an index of " ++ show index
      ++ " where the size of the array is " ++ show size ++ "; the size must "
      ++ " be strictly greater than the index."
  ---------------------------------------
  show (MatrixWrongRowSize name expectedRowSize) =
    badUsage $ "in the environment for external matrix " ++ name
      ++ ", we expect a matrix with " ++ show expectedRowSize ++ " rows"
      ++ ", but the matrix you supplied has a different number of rows."
  ---------------------------------------
  show (MatrixRowIdxOutofBounds name index rows) =
    badUsage $ "in the environment for external matrix " ++ name
      ++ ", you gave a row index of " ++ show index
      ++ " where the number of rows in the matrix is " ++ show rows ++ "; the number of rows must "
      ++ " be strictly greater than the index."
    ---------------------------------------
  show (MatrixWrongColSize name expectedColSize) =
    badUsage $ "in the environment for external matrix " ++ name
      ++ ", we expect a matrix with " ++ show expectedColSize ++ " columns"
      ++ ", but the matrix you supplied has a different number of columns."
  ---------------------------------------
  show (MatrixColIdxOutofBounds name index cols) =
    badUsage $ "in the environment for external matrix " ++ name
      ++ ", you gave a column index of " ++ show index
      ++ " where the number of columns in the matrix is " ++ show cols ++ "; the number of columns must "
      ++ " be strictly greater than the index."
  ---------------------------------------
  show DivideByZero =
    badUsage "divide by zero."
  ---------------------------------------
  show (NotEnoughValues name k) =
    badUsage $ "on the " ++ show k ++ "th iteration, we ran out of "
      ++ "values for simulating the external element " ++ name ++ "."
  ---------------------------------------
  show (NoExtsInterp name) =
    badUsage $ "in a call of external symbol " ++ name ++ ", you did not "
      ++ "provide an expression for interpretation.  In your external "
      ++ "declaration, you need to provide a 'Just strm', where 'strm' is "
      ++ "some stream with which to simulate the function."
  ---------------------------------------

instance Exception InterpException

--------------------------------------------------------------------------------

type Env nm = [(nm, DynamicF [] Type)]

-- -- | External arrays environment.
-- type ArrEnv = [(Name, [DynamicF [] Type])]

-- -- | Environment for simulation.
-- data ExtEnv = ExtEnv { varEnv  :: Env Name
--                      , arrEnv  :: ArrEnv
-- --                     , funcEnv :: [(Name, Spec)]
--                      }

--------------------------------------------------------------------------------

type Output = String

data ExecTrace = ExecTrace
    -- map from trigger names to their maybe output, which is a list of strings
    -- representing their values.  (Nothing output if the guard for the trigger
    -- is false).  The order is important, since we compare the arg lists
    -- between the interpreter and backends.
  { interpTriggers  :: Map String [Maybe [Output]]
    -- map from observer names to their outputs.  We also show observer outputs.
  , interpObservers :: Map String [Output] }
  deriving Show

--------------------------------------------------------------------------------

{-
eval :: Int -> Env Name -> Spec -> ExecTrace
eval k exts spec =
  let
    strms = fmap (evalStream     exts strms) (specStreams   spec)
    trigs = fmap (evalTrigger  k exts strms) (specTriggers  spec)
    obsvs = fmap (evalObserver k exts strms) (specObservers spec)
  in
    ExecTrace
      { interpTriggers  = M.fromList $
          zip (fmap triggerName  (specTriggers  spec)) trigs
      , interpObservers = M.fromList $
          zip (fmap observerName (specObservers spec)) obsvs
      }
-}

-- We could write this in a beautiful lazy style like above, but that creates a
-- space leak in the interpreter that is hard to fix while maintaining laziness.
-- We take a more brute-force appraoch below.
eval :: ShowType -> Int -> Spec -> ExecTrace
eval showType k spec =
  let initStrms = map initStrm (specStreams spec) in

  let strms = evalStreams k (specStreams spec) initStrms in

  let trigs = map (evalTrigger showType k strms) (specTriggers spec) in

  let obsvs = map (evalObserver showType k strms) (specObservers spec) in

  strms `seq` ExecTrace { interpTriggers  = M.fromList $ zip (map triggerName  (specTriggers  spec)) trigs
                        , interpObservers = M.fromList $ zip (map observerName (specObservers spec)) obsvs }

--------------------------------------------------------------------------------

type LocalEnv = [(Name, Dynamic Type)]

evalExpr :: Int -> Expr a -> LocalEnv -> Env Id -> a
evalExpr k e locs strms = case e of

  Const _ x -> x

  Matrix _ m -> m

  Drop t i strId ->
    let Just xs = lookup strId strms >>= fromDynF t in
    reverse xs !! (fromIntegral i + k)

  Local t1 _ name e1 e2 ->
    x `seq` locs' `seq` evalExpr k e2 locs' strms
    where
      x = evalExpr k e1 locs strms
      locs' = (name, toDyn t1 x) : locs

  Var t name -> fromJust $ lookup name locs >>= fromDyn t

  ExternVar _ name xs -> evalExternVar k name xs

  ExternFun _ name _ e1 _ -> case e1 of
                              Nothing -> throw (NoExtsInterp name)
                              Just expr -> evalExpr k expr locs strms

  ExternArray _ _ name size idx xs _ -> evalArray k name evalIdx xs size
    where
      evalIdx = evalExpr k idx locs strms

  ExternMatrix _ _ name rows cols idxr idxc xs _ -> evalMatrix k name evalIdxr evalIdxc xs rows cols
    where
      evalIdxr = evalExpr k idxr locs strms
      evalIdxc = evalExpr k idxc locs strms

  ExternStruct _ _ _ _   -> error "unimplemented"
  GetField _ _ _ _       -> error "unimplemented"

  Op1 op e1 -> ev1 `seq` op1 `seq` op1 ev1
    where
      ev1 = evalExpr k e1 locs strms
      op1 = evalOp1 op

  Op2 op e1 e2 -> ev1 `seq` ev2 `seq` op2 `seq` op2 ev1 ev2
    where
      ev1 = evalExpr k e1 locs strms
      ev2 = evalExpr k e2 locs strms
      op2 = evalOp2 op

  Op3 op e1 e2 e3 -> ev1 `seq` ev2 `seq` ev3 `seq` op3 `seq` op3 ev1 ev2 ev3
    where
      ev1 = evalExpr k e1 locs strms
      ev2 = evalExpr k e2 locs strms
      ev3 = evalExpr k e3 locs strms
      op3 = evalOp3 op

  Label _ _ e1 -> evalExpr k e1 locs strms

--------------------------------------------------------------------------------

evalExternVar :: Int -> Name -> Maybe [a] -> a
evalExternVar k name exts =
  case exts of
    Nothing -> throw (NoExtsInterp name)
    Just xs ->
      case safeIndex k xs of
        Nothing -> throw (NotEnoughValues name k)
        Just x  -> x

--------------------------------------------------------------------------------

-- evalFunc :: Int -> Type a -> Name -> Expr a -> ExtEnv -> a
-- evalFunc k t name expr exts  =
--   evalExpr k expr

--   case lookup name (funcEnv exts) of
--     Nothing -> throw (NoValues name)

--     -- We created this spec in Interpreter.hs, copilot-language, so it should
--     -- contain no triggers and exactly one observer.
--     Just Spec { specStreams   = specStrms
--               , specObservers = obsLs }  ->
--      let initStrms = map initStrm specStrms             in
--      let strms = evalStreams k exts specStrms initStrms in
--      case obsLs of
--        [Observer { observerExpr     = expr_
--                  , observerExprType = t1 }] ->
--          let dyn = toDynF t1 expr_ in
--            case fromDynF t dyn of
--              Nothing    -> throw (BadType name)
--              Just expr  -> evalExpr_ k expr exts [] strms
--        _ -> throw (BadType name)

--------------------------------------------------------------------------------

evalArray :: Integral b => Int -> Name -> b -> Maybe [[a]] -> Int -> a
evalArray k name idx exts size =
  case exts of
    Nothing -> throw (NoExtsInterp name)
    Just xs ->
      case safeIndex k xs of
        Nothing  -> throw (NotEnoughValues name k)
        Just arr -> -- convoluted form in case the array is env of infinite
                    -- length.
                    if length (take size arr) == size && length (take (size+1) arr) == size
                    then case safeIndex (fromIntegral idx) arr of
                           Nothing -> throw (ArrayIdxOutofBounds name (fromIntegral idx) size)
                           Just x  -> x
                    else throw (ArrayWrongSize name size)

--------------------------------------------------------------------------------

evalMatrix :: Integral b => Int -> Name -> b -> b -> Maybe [[[a]]] -> Int -> Int -> [[a]]
evalMatrix k name idxr idxc exts rows cols =
  case exts of
    Nothing -> throw (NoExtsInterp name)
    Just xs ->
      case safeIndex k xs of
        Nothing  -> throw (NotEnoughValues name k)
        Just matr -> matr

        --if length (take rows matr) == rows && length (take (rows+1) matr) == rows
        --             then case safeIndex (fromIntegral idxr) matr of
        --                    Nothing -> throw (MatrixRowIdxOutofBounds name (fromIntegral idxr) rows)
        --                    Just row -> if length (take cols row) == cols && length (take (cols+1) row) == cols
        --                                then case safeIndex (fromIntegral idxc) row of
        --                                      Nothing -> throw (MatrixColIdxOutofBounds name (fromIntegral idxc) cols)
        --                                      Just x  -> x
        --                                else throw (MatrixWrongColSize name cols)
        --             else throw (MatrixWrongRowSize name rows)

--------------------------------------------------------------------------------

evalOp1 :: Op1 a b -> (a -> b)
evalOp1 op = case op of
  Not        -> P.not
  Abs _      -> P.abs
  Sign _     -> P.signum
  Recip _    -> P.recip
  Exp _      -> P.exp
  Sqrt _     -> P.sqrt
  Log _      -> P.log
  Sin _      -> P.sin
  Tan _      -> P.tan
  Cos _      -> P.cos
  Asin _     -> P.asin
  Atan _     -> P.atan
  Acos _     -> P.acos
  Sinh _     -> P.sinh
  Tanh _     -> P.tanh
  Cosh _     -> P.cosh
  Asinh _    -> P.asinh
  Atanh _    -> P.atanh
  Acosh _    -> P.acosh
  BwNot _    -> complement
  Cast _ _   -> P.fromIntegral

--------------------------------------------------------------------------------

evalOp2 :: Op2 a b c -> (a -> b -> c)
evalOp2 op = case op of
  And          -> (&&)
  Or           -> (||)
  Add _        -> (+)
  Sub _        -> (-)
  Mul _        -> (*)
  Mod _        -> (catchZero P.mod)
  Div _        -> (catchZero P.div)
  Fdiv _       -> (P./)
  Pow _        -> (P.**)
  Logb _       -> P.logBase
  Eq _         -> (==)
  Ne _         -> (/=)
  Le _         -> (<=)
  Ge _         -> (>=)
  Lt _         -> (<)
  Gt _         -> (>)
  BwAnd _      -> (.&.)
  BwOr  _      -> (.|.)
  BwXor _      -> (xor)
  BwShiftL _ _ -> ( \ !a !b -> shiftL a $! fromIntegral b )
  BwShiftR _ _ -> ( \ !a !b -> shiftR a $! fromIntegral b )

catchZero :: Integral a => (a -> a -> a) -> (a -> a -> a)
catchZero _ _ 0 = throw DivideByZero
catchZero f x y = f x y

--------------------------------------------------------------------------------

evalOp3 :: Op3 a b c d -> (a -> b -> c -> d)
evalOp3 (Mux _) = \ !v !x !y -> if v then x else y

--------------------------------------------------------------------------------

initStrm :: Stream -> (Id, DynamicF [] Type)
initStrm Stream { streamId       = id
                , streamBuffer   = buffer
                , streamExprType = t } = (id, toDynF t (reverse buffer))

-- XXX actually only need to compute until shortest stream is of length k
-- XXX this should just be a foldl' over [0,1..k]
evalStreams :: Int -> [Stream] -> Env Id -> Env Id
evalStreams top specStrms initStrms = evalStreamsAux 0 initStrms
  where
    evalStreamsAux :: Int -> Env Id -> Env Id
    evalStreamsAux k strms | k == top  = strms
                           | otherwise = evalStreamsAux (k+1) $! map (evalStream k strms) specStrms
    evalStream :: Int -> Env Id -> Stream -> (Id, DynamicF [] Type)
    evalStream k strms Stream { streamId       = id
                              , streamExpr     = e
                              , streamExprType = t } = (id, toDynF t ls)
      where
        xs = fromJust $ lookup id strms >>= fromDynF t
        x  = evalExpr k e [] strms
        ls = x `seq` (x:xs)

--------------------------------------------------------------------------------

evalTrigger ::
  ShowType -> Int -> Env Id -> Trigger -> [Maybe [Output]]
evalTrigger showType k strms Trigger { triggerGuard = e
                                     , triggerArgs  = args }
  = map tag (zip bs vs)

  where
    tag :: (Bool, a) -> Maybe a
    tag (True,  x) = Just x
    tag (False, _) = Nothing

    -- Is the guard true?
    bs :: [Bool]
    bs = evalExprs k e strms

    -- The argument outputs.
    vs :: [[Output]]
    vs = if null args then replicate k []  -- might be 0 args.
           else transpose $ map evalUExpr args

    evalUExpr :: UExpr -> [Output]
    evalUExpr (UExpr t e1) =
      map (showWithType showType t) (evalExprs k e1 strms)

--------------------------------------------------------------------------------
evalObserver :: ShowType -> Int -> Env Id -> Observer -> [Output]
evalObserver showType k strms Observer { observerExpr     = e
                                       , observerExprType = t }
  = map (showWithType showType t) (evalExprs k e strms)

--------------------------------------------------------------------------------

evalExprs :: Int -> Expr a -> Env Id -> [a]
evalExprs k e strms = map (\i -> evalExpr i e [] strms) [0..(k-1)]

--------------------------------------------------------------------------------

-- | Safe indexing (!!) on possibly infinite lists.
safeIndex :: Int -> [a] -> Maybe a
safeIndex i ls = let ls' = take (i+1) ls in
  if length ls' > i then Just (ls' !! i)
    else Nothing

--------------------------------------------------------------------------------
