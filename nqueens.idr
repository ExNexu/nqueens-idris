module Main

import data.Vect
import Data.List

%default total

-- Aliases

Queen : Type
Queen = (Nat, Nat)

IsValid : Type
IsValid = Bool

Valid : IsValid
Valid = True

Invalid : IsValid
Invalid = False

Boardsize : Type
Boardsize = Nat

Queens : Nat -> Type
Queens n = Vect n Queen

-- Helper methods

forAllPairsWithList : List a -> a -> (a -> a -> Bool) -> Bool
forAllPairsWithList [] element p = True
forAllPairsWithList (x :: xs) element p = if p element x then forAllPairsWithList xs element p else False

forAllPairsInList : List a -> (a -> a -> Bool) -> Bool
forAllPairsInList [] p = True
forAllPairsInList (x :: xs) p = (forAllPairsWithList xs x p) && forAllPairsInList xs p

-- NQueens

isValidNQueens : {n : Boardsize} -> Queens n -> IsValid
isValidNQueens {n=boardsize} queens =
  let
    queenList = toList queens
    isAllOnBoard = all (isOnBoard boardsize) queenList
    isAllDifferentRows = forAllPairsInList queenList isDifferentRows
    isAllDifferentCols = forAllPairsInList queenList isDifferentCols
    isAllDifferentDiags = forAllPairsInList queenList isDifferentDiags
  in
    isAllOnBoard && isAllDifferentRows && isAllDifferentCols && isAllDifferentDiags
  where
    isOnBoard : Boardsize -> Queen -> Bool
    isOnBoard boardsize (a, b) = a < boardsize && b < boardsize

    isDifferentRows : Queen -> Queen -> Bool
    isDifferentRows (a1, a2) (b1, b2) = a1 /= b1

    isDifferentCols : Queen -> Queen -> Bool
    isDifferentCols (a1, a2) (b1, b2) = a2 /= b2

    isDifferentDiags : Queen -> Queen -> Bool
    isDifferentDiags ((S a1), (S a2)) b = assert_total (isDifferentDiags (a1, a2) b) -- meh
    isDifferentDiags a ((S b1), (S b2)) = assert_total (isDifferentDiags a (b1, b2)) -- meh
    isDifferentDiags (a1, a2) (b1, b2) = if (a1 == b1 && a2 == b2) then False else True

data NQueens : Boardsize -> IsValid -> Type where
  MkNQueens : (queens : Queens n) -> NQueens n (isValidNQueens queens)

-- (Compile) Tests

queen1 : Queen
queen1 = (3, 2)

queen2 : Queen
queen2 = (2, 0)

queen3 : Queen
queen3 = (1, 3)

queen4 : Queen
queen4 = (0, 1)

invalidNQueens1 : NQueens 1 Valid
invalidNQueens1 = MkNQueens [(0, 0)]

nQueens4 : NQueens 4 Valid
nQueens4 = MkNQueens [queen1, queen2, queen3, queen4]

invalidNQueens4 : NQueens 4 Invalid
invalidNQueens4 = MkNQueens [queen1, (3, 3), queen3, queen4]

---- Does not compile! :-)
--invalidNQueens1Error : NQueens 1 Invalid
--invalidNQueens1Error = MkNQueens [(0, 0)]

--invalidNQueens2Error : NQueens 2 Valid -- Does not even compile as Invalid!
--invalidNQueens2Error = MkNQueens [(0, 0)]

--invalidNQueens4Error : NQueens 4 Valid
--invalidNQueens4Error = MkNQueens [queen1, (3, 3), queen3, queen4]

