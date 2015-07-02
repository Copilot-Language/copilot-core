--------------------------------------------------------------------------------
-- Copyright © 2011 National Institute of Aerospace / Galois, Inc.
--------------------------------------------------------------------------------

-- | Sets a unique tags for each external array/function/struct call.

{-# LANGUAGE Safe #-}

module Copilot.Core.MakeTags (makeTags) where

import Copilot.Core.Expr
import Copilot.Core.Spec
import Control.Monad.State
import Data.Maybe(fromJust)
import Prelude hiding (id)

next :: State Int Int
next = do
  k <- get
  put (succ k)
  return k

makeTags :: Spec -> Spec
makeTags spec = evalState (mkTagsSpec spec) 0

mkTagsSpec :: Spec -> State Int Spec
mkTagsSpec
  Spec
    { specStreams    = strms
    , specObservers  = obsvs
    , specTriggers   = trigs
    , specProperties = props
    , specStructs    = strs
    } =
  liftM5 Spec
    (mkTagsStrms strms)
    (mkTagsObsvs obsvs)
    (mkTagsTrigs trigs)
    (mkTagsProps props)
    (mkTagsStrs  strs)

mkTagsStrms :: [Stream] -> State Int [Stream]
mkTagsStrms = mapM mkTagsStrm

  where
    mkTagsStrm Stream
      { streamId         = id
      , streamBuffer     = xs
      , streamExpr       = e
      , streamExprType   = t } =
        do
          e' <- mkTagsExpr e
          return $ Stream
            { streamId         = id
            , streamBuffer     = xs
            , streamExpr       = e'
            , streamExprType   = t }

mkTagsObsvs :: [Observer] -> State Int [Observer]
mkTagsObsvs = mapM mkTagsObsv

  where
    mkTagsObsv Observer
      { observerName     = name
      , observerExpr     = e
      , observerExprType = t } =
        do
          e' <- mkTagsExpr e
          return $ Observer
            { observerName     = name
            , observerExpr     = e'
            , observerExprType = t }

mkTagsTrigs :: [Trigger] -> State Int [Trigger]
mkTagsTrigs = mapM mkTagsTrig

 where
   mkTagsTrig Trigger
     { triggerName      = name
     , triggerGuard     = g
     , triggerArgs      = args } =
       do
         g' <- mkTagsExpr g
         args' <- mapM mkTagsUExpr args
         return $ Trigger
           { triggerName      = name
           , triggerGuard     = g'
           , triggerArgs      = args' }

mkTagsProps :: [Property] -> State Int [Property]
mkTagsProps = mapM mkTagsProp

  where mkTagsProp p = do
          e' <- mkTagsExpr (propertyExpr p)
          return $ p { propertyExpr = e' }

mkTagsStrs  :: [StructData] -> State Int [StructData]
mkTagsStrs  = mapM $ fromJust . mkTagsStr

  where
    mkTagsStr :: StructData -> Maybe (State Int StructData)
    mkTagsStr StructData
      { structName = name
      , structInst = inst } =
        case inst of
          ExternStruct x y sargs z -> Just $ do
            sargs' <- mapM mkTagsSExpr sargs
            return $ StructData
              { structName = name
              , structInst = ExternStruct x y sargs' z }
          _                        -> Nothing

mkTagsUExpr :: UExpr -> State Int UExpr
mkTagsUExpr UExpr { uExprExpr = e, uExprType = t } =
  do
    e' <- mkTagsExpr e
    return $ UExpr { uExprExpr = e', uExprType = t }

mkTagsSExpr :: SExpr -> State Int SExpr
mkTagsSExpr SExpr { sname = n, uexpr = u } =
  do
    u' <- mkTagsUExpr u
    return $ SExpr { sname = n, uexpr = u' }

mkTagsExpr :: Expr a -> State Int (Expr a)
mkTagsExpr e0 = case e0 of
  Const t x                      -> return $ Const t x
  Drop t k id                    -> return $ Drop t k id
  Local t1 t2 name e1 e2         -> liftM2 (Local t1 t2 name) (mkTagsExpr e1) (mkTagsExpr e2)
  Var t name                     -> return $ Var t name
  ExternVar t name e             -> return $ ExternVar t name e
  ExternFun t name args expr _   -> do args' <- mapM mkTagsUExpr args
                                       k <- next
                                       return $ ExternFun t name args' expr (Just k)
  ExternArray t1 t2 name 
              size idx e _       -> do idx' <- mkTagsExpr idx
                                       k <- next
                                       return $ ExternArray t1 t2 name size idx' e (Just k)
  ExternStruct t name sargs _    -> do args' <- mapM mkTagsSExpr sargs
                                       k <- next
                                       return $ ExternStruct t name args' (Just k)
  Op1 op e                       -> liftM  (Op1 op) (mkTagsExpr e)
  Op2 op e1 e2                   -> liftM2 (Op2 op) (mkTagsExpr e1) (mkTagsExpr e2)
  Op3 op e1 e2 e3                -> liftM3 (Op3 op) (mkTagsExpr e1) (mkTagsExpr e2) (mkTagsExpr e3)
