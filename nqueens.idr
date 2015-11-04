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

getMaybeValidQueenInQueens : Nat -> Queens n -> Queen -> MaybeValidQueen
getMaybeValidQueenInQueens boardsize queens queen =
  let
    isOnBoard = isOnBoard boardsize queen
    queenList = toList queens
    isAllDifferentRows = forAllPairsWithList queenList queen isDifferentRows
    isAllDifferentCols = forAllPairsWithList queenList queen isDifferentCols
    isAllDifferentDiags = forAllPairsWithList queenList queen isDifferentDiags
  in
    if isOnBoard && isAllDifferentRows && isAllDifferentCols && isAllDifferentDiags then ValidQueen queen else InvalidQueen
  where
    isOnBoard : Nat -> Queen -> Bool
    isOnBoard boardsize (a, b) = a < boardsize && b < boardsize

    isDifferentRows : Queen -> Queen -> Bool
    isDifferentRows (a1, a2) (b1, b2) = a1 /= b1

    isDifferentCols : Queen -> Queen -> Bool
    isDifferentCols (a1, a2) (b1, b2) = a2 /= b2

    isDifferentDiags : Queen -> Queen -> Bool
    isDifferentDiags ((S a1), (S a2)) b = assert_total (isDifferentDiags (a1, a2) b) -- meh
    isDifferentDiags a ((S b1), (S b2)) = assert_total (isDifferentDiags a (b1, b2)) -- meh
    isDifferentDiags (a1, a2) (b1, b2) = if (a1 == b1 && a2 == b2) then False else True

data ValidQueenAddition : Nat -> Queens n -> MaybeValidQueen -> Type where
  MkValidQueenAddition : (boardsize: Nat) -> (queens: Queens n) -> (queen: Queen) ->
    let
      maybeValidQueen = getMaybeValidQueenInQueens boardsize queens queen
    in
      ValidQueenAddition boardsize queens maybeValidQueen

-- Constructing NQueens

data ValidQueens : Nat -> Queens n -> Type where
  EmptyValidBoundQueens :
    (boardsize: Nat) ->
    ValidQueens boardsize []
  ExtendValidBoundQueens :
    (boardsize: Nat) ->
    (validQueens: ValidQueens boardsize queens) ->
    (validQueenAddition: (ValidQueenAddition boardsize queens (ValidQueen queen))) ->
      ValidQueens boardsize (queen :: queens)

data NQueens : Queens n -> Type where
  MkNQueens :
    {n: Nat} ->
    {queens: Queens n} ->
    (validQueens: ValidQueens n queens) ->
      NQueens queens

-- (Compile) Tests

queen1 : Queen
queen1 = (3, 2)

queen2 : Queen
queen2 = (2, 0)

queen3 : Queen
queen3 = (1, 3)

queen4 : Queen
queen4 = (0, 1)

validQueens1 : ValidQueens 4 [queen1]
validQueens1 = ExtendValidBoundQueens _ (EmptyValidBoundQueens _) (MkValidQueenAddition _ _ queen1)

validQueens2 : ValidQueens 4 [queen2, queen1]
validQueens2 = ExtendValidBoundQueens _ validQueens1 (MkValidQueenAddition _ _ queen2)

validQueens3 : ValidQueens 4 [queen3, queen2, queen1]
validQueens3 = ExtendValidBoundQueens _ validQueens2 (MkValidQueenAddition _ _ queen3)

validQueens4 : ValidQueens 4 [queen4, queen3, queen2, queen1]
validQueens4 = ExtendValidBoundQueens _ validQueens3 (MkValidQueenAddition _ _ queen4)

-- Error! :-)
--validQueens5 : ValidQueens 4 [(99, 44), queen4, queen3, queen2, queen1]
--validQueens5 = ExtendValidBoundQueens _ validQueens4 (MkValidQueenAddition _ _ (99, 44))

nQueens4 : NQueens [queen4, queen3, queen2, queen1]
nQueens4 = MkNQueens validQueens4

-- Error! :-)
--nQueens3 : NQueens [queen3, queen2, queen1]
--nQueens3 = MkNQueens validQueens3

