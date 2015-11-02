module Main

import data.Vect
import Data.Matrix
import Data.List
import Data.Fin

%default total

-- Aliases

Queen : Type
Queen = (Nat, Nat)

MaybeValidQueen : Type
MaybeValidQueen = Maybe Queen

ValidQueen : Queen -> MaybeValidQueen
ValidQueen queen = Just queen

InvalidQueen : MaybeValidQueen
InvalidQueen = Nothing

Queens : Nat -> Type
Queens n = Vect n Queen

-- Helper methods

forAllPairsWithList : List a -> a -> (a -> a -> Bool) -> Bool
forAllPairsWithList [] element p =
  True
forAllPairsWithList (x :: xs) element p =
  if p element x then forAllPairsWithList xs element p else False

-- ValidQueens

getMaybeValidQueenInQueens : Queens n -> Queen -> MaybeValidQueen
getMaybeValidQueenInQueens queens queen =
  let
    queenList = toList queens
    isAllDifferentRows = forAllPairsWithList queenList queen isDifferentRows
    isAllDifferentCols = forAllPairsWithList queenList queen isDifferentCols
    isAllDifferentDiags = forAllPairsWithList queenList queen isDifferentDiags
  in
    if isAllDifferentRows && isAllDifferentCols && isAllDifferentDiags then ValidQueen queen else InvalidQueen
  where
    isDifferentRows : Queen -> Queen -> Bool
    isDifferentRows (a1, a2) (b1, b2) = a1 /= b1

    isDifferentCols : Queen -> Queen -> Bool
    isDifferentCols (a1, a2) (b1, b2) = a2 /= b2

    isDifferentDiags : Queen -> Queen -> Bool
    isDifferentDiags ((S a1), (S a2)) b = assert_total (isDifferentDiags (a1, a2) b) -- meh
    isDifferentDiags a ((S b1), (S b2)) = assert_total (isDifferentDiags a (b1, b2)) -- meh
    isDifferentDiags (a1, a2) (b1, b2) = if (a1 == b1 && a2 == b2) then False else True

data ValidQueenAddition : Queens n -> MaybeValidQueen -> Type where
  MkValidQueenAddition : (queens: Queens n) -> (queen: Queen) ->
    let
      maybeValidQueen = getMaybeValidQueenInQueens queens queen
    in
      ValidQueenAddition queens maybeValidQueen

data ValidQueens : Queens n -> Type where
  EmptyValidQueens :
    ValidQueens []
  ExtendValidQueens :
    (validQueens: ValidQueens queens) ->
    (validQueenAddition: (ValidQueenAddition queens (ValidQueen queen))) ->
      ValidQueens (queen :: queens)

-- (Compile) Tests

queen1 : Queen
queen1 = (3, 2)

queen2 : Queen
queen2 = (2, 0)

queen3 : Queen
queen3 = (1, 3)

queen4 : Queen
queen4 = (0, 1)

validQueens1 : ValidQueens [queen1]
validQueens1 = ExtendValidQueens EmptyValidQueens (MkValidQueenAddition [] queen1)

validQueens2 : ValidQueens [queen2, queen1]
validQueens2 = ExtendValidQueens validQueens1 (MkValidQueenAddition [queen1] queen2)

validQueens3 : ValidQueens [queen3, queen2, queen1]
validQueens3 = ExtendValidQueens validQueens2 (MkValidQueenAddition [queen2, queen1] queen3)

validQueens4 : ValidQueens [queen4, queen3, queen2, queen1]
validQueens4 = ExtendValidQueens validQueens3 (MkValidQueenAddition [queen3, queen2, queen1] queen4)

--Error! :-)
--errorValidQueens4 : ValidQueens [(0, 3), queen3, queen2, queen1]
--errorValidQueens4 = ExtendValidQueens validQueens3 (MkValidQueenAddition [queen3, queen2, queen1] (0, 3))

-- Constructing NQueens

data BoundQueen : (n: Nat) -> MaybeValidQueen -> Type where
  MkBoundQueen : (n: Nat) -> (queen: Queen)  ->
    let
      a = fst queen
      b = snd queen
      maybeBoundQueen = if a < n && b < n then ValidQueen queen else InvalidQueen
    in
      BoundQueen n maybeBoundQueen

data ValidBoundQueens : Nat -> Queens n -> Type where
  EmptyValidBoundQueens :
    (bound: Nat) ->
    ValidBoundQueens bound []
  ExtendValidBoundQueens :
    (bound: Nat) ->
    (validBoundQueens: ValidBoundQueens bound boundQueens) ->
    (validBoundQueenAddition: (ValidQueenAddition boundQueens (ValidQueen queen))) ->
    (validBoundQueen: BoundQueen bound (ValidQueen queen)) ->
      ValidBoundQueens bound (queen :: boundQueens)

data NQueens : Queens n -> Type where
  MkNQueens :
    {n: Nat} ->
    {queens: Queens n} ->
    (validBoundQueens: ValidBoundQueens n queens) ->
      NQueens queens

-- (Compile) Tests

validBoundQueens1 : ValidBoundQueens 4 [queen1]
validBoundQueens1 = ExtendValidBoundQueens _ (EmptyValidBoundQueens _) (MkValidQueenAddition _ _) (MkBoundQueen _ queen1)

validBoundQueens2 : ValidBoundQueens 4 [queen2, queen1]
validBoundQueens2 = ExtendValidBoundQueens _ validBoundQueens1 (MkValidQueenAddition _ queen2) (MkBoundQueen _ queen2)

validBoundQueens3 : ValidBoundQueens 4 [queen3, queen2, queen1]
validBoundQueens3 = ExtendValidBoundQueens _ validBoundQueens2 (MkValidQueenAddition _ queen3) (MkBoundQueen _ queen3)

validBoundQueens4 : ValidBoundQueens 4 [queen4, queen3, queen2, queen1]
validBoundQueens4 = ExtendValidBoundQueens _ validBoundQueens3 (MkValidQueenAddition _ queen4) (MkBoundQueen _ queen4)

-- Error! :-)
--validBoundQueens5 : ValidBoundQueens 4 [(99, 44), queen4, queen3, queen2, queen1]
--validBoundQueens5 = ExtendValidBoundQueens _ validBoundQueens4 (MkValidQueenAddition _ (99, 44)) (MkBoundQueen _ (99, 44))

nQueens4 : NQueens [queen4, queen3, queen2, queen1]
nQueens4 = MkNQueens validBoundQueens4

-- Error! :-)
--nQueens3 : NQueens [queen3, queen2, queen1]
--nQueens3 = MkNQueens validBoundQueens3

