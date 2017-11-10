{-# LANGUAGE OverloadedStrings #-}
  
module Lib where

import Control.Monad.Trans.State.Strict
import Data.Text (Text)
import Data.Monoid ((<>))
import TextShow

type Gen = State Int

nextName :: Name -> Gen Name
nextName n = do
  i <- get
  put (i+1)
  return (n <> showt i)

evalGen :: Gen a -> Int -> a
evalGen = evalState

data Type
  = IntType
  | StringType
  | BoolType
  | RecordType [(Label, Type)]
  deriving (Show)

type Name = Text
type Label = Text

data Constant
  = IntLiteral Int
  | StringLiteral Text
  | BoolLiteral Bool
  deriving (Show)

data Expr a
  = Variable    a Name
  | Constant    a Constant
  | Lambda      a Name (Expr a)
  | Application a (Expr a) (Expr a)
  | IfThenElse  a (Expr a) (Expr a) (Expr a)
  | Record      a [(Label, Expr a)]
  | Projection  a (Expr a) Label
  | List        a [Expr a]
  | Concat      a (Expr a) (Expr a)
  | For         a Name (Expr a) (Expr a)
  | Constructor a Label (Expr a)
  | Case        a (Expr a) [(Label, Expr a)]
  | Table       a Text Type
  deriving (Show)

trace :: Monoid a => Expr a -> Gen (Expr a)
trace x@(Variable _ _) = do
  t <- nextName "t"
  return $ Lambda mempty t (Application mempty (Variable mempty t) x)
trace c@(Constant _ _) = do
  t <- nextName "t"
  return $ Lambda mempty t (Application mempty (Variable mempty t) (Constructor mempty "Lit" c))
trace (Lambda _ _ _) = error "we assume normalized query terms -- no lambda!"
trace (Application _ _ _) = error "we assume normalized query terms -- no application!"
trace (IfThenElse _ l m n) = do
  t <- nextName "t"
  tl <- trace l
  mm <- nextName "m"
  tm <- trace m
  nn <- nextName "n"
  tn <- trace n
  return $ Lambda mempty t (IfThenElse mempty
                              (Application mempty (Variable mempty "value") (Application mempty tl (Variable mempty "id")))
                              (Application mempty tm (Lambda mempty mm (Application mempty (Variable mempty t) (Constructor mempty "IfThen" (Record mempty [("cond", tl), ("then", (Variable mempty mm))])))))
                              (Application mempty tn (Lambda mempty nn (Application mempty (Variable mempty t) (Constructor mempty "IfElse" (Record mempty [("cond", tl), ("else", (Variable mempty nn))]))))))
trace (Record _ r) = do
  t <- nextName "t"
  r <- traverse (\(l, e) -> do
                    e <- trace e
                    x <- nextName "x"
                    return $ (l, Application mempty e (Lambda mempty x (Application mempty (Variable mempty t) (Constructor mempty "Record" (Variable mempty x)))))) r
  return $ Lambda mempty t (Record mempty r)
trace (Projection _ m l) = do
  t <- nextName "t"
  m <- trace m
  mm <- nextName "m"
  return $ Lambda mempty t (Application mempty m (Lambda mempty mm (Application mempty (Variable mempty t) (Constructor mempty "Proj" (Record mempty [ ("label", Constant mempty (StringLiteral l))
                                                                                                                                                     , ("field", Projection mempty (Variable mempty mm) l) ])))))
trace (List _ l) = do
  t <- nextName "t"
  l <- traverse (\m -> do
                    m <- trace m
                    x <- nextName "x"
                    return $ Application mempty m (Lambda mempty x (Application mempty (Variable mempty t) (Constructor mempty "List" (Variable mempty x))))) l
  return $ Lambda mempty t (List mempty l)
trace (Concat _ m n) = do
  t <- nextName "t"
  mm <- nextName "m"
  m <- trace m
  x <- nextName "x"
  nn <- nextName "n"
  n <- trace n
  y <- nextName "y"
  return $ Lambda mempty t (Concat mempty
                             (For mempty mm (Application mempty m (Lambda mempty x (Application mempty (Variable mempty t) (Constructor mempty "UnionLeft" (Variable mempty x))))) (List mempty [Variable mempty mm]))
                             (For mempty nn (Application mempty n (Lambda mempty y (Application mempty (Variable mempty t) (Constructor mempty "UnionRight" (Variable mempty y))))) (List mempty [Variable mempty nn])))
trace (For _ x m n) = do
  t <- nextName "t"
  m <- trace m
  x <- nextName "x"
  n <- trace n
  nn <- nextName "n"
  return $ Lambda mempty t (For mempty x (Application mempty m (Lambda mempty x (Variable mempty x)))
                            (Application mempty n (Lambda mempty nn (Application mempty (Variable mempty t) (Constructor mempty "For" (Record mempty [("in", Variable mempty x), ("out", Variable mempty nn)]))))))
trace (Constructor _ _ _) = error "we assume normalized query terms -- no constructor!"
trace (Case _ _ _) = error "we assume normalized query terms -- no case!"
trace tbl@(Table a n (RecordType row)) = do
  t <- nextName "t"
  x <- nextName "x"
  row <- traverse (\(l, _) -> return $ (l, Constructor mempty "Row" (Record mempty [("table", Constant mempty (StringLiteral n)), ("column", Constant mempty (StringLiteral l)), ("data", Projection mempty (Variable mempty x) l)]))) row
  return $ Lambda mempty t (For mempty x tbl (List mempty [Application mempty (Variable mempty t) (Record mempty row)]))


someFunc :: IO ()
someFunc = putStrLn "someFunc"
