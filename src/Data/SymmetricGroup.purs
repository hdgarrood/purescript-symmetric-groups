module Data.SymmetricGroup
  ( Sym
  , symmetric
  , alternating
  , asCycles
  , setSize
  , unSym
  , inversions
  , sgn
  ) where

import Prelude
import Control.MonadPlus (guard)
import Data.Monoid (mempty)
import Data.Maybe
import Data.Tuple
import Data.Int as Int
import Data.String as String
import Data.Foldable (foldl, foldMap)
import Data.Map (Map)
import Data.Map as Map
import Data.List (List(..), (:))
import Data.List as List
import Data.Typelevel.Num ()
import Partial.Unsafe (unsafePartial)

-- | The type `Sym` represents the symmetric group on some set {1,2,...n}; a
-- | value of this type represents a bijection on this set.
newtype Sym = Sym (List Int)
-- Invariant: the array should contain each int from 1 to n exactly once for
-- some n.

instance showSym :: Show Sym where
  show s =
    let cs = asCycles s
        showCycle c =
          "(" <>
          String.joinWith " " (map show (List.toUnfoldable c)) <>
          ")"
     in if List.null cs
          then "ι"
          else foldMap showCycle cs

newtype Set a = Set (Map a Unit)

oneUpTo :: Int -> Set Int
oneUpTo n = Set (Map.fromFoldable (map (flip Tuple unit) (List.range 1 n)))

popMin :: Set Int -> Maybe (Tuple Int (Set Int))
popMin (Set m) =
  map (\r -> Tuple r.key (Set (Map.delete r.key m))) (Map.findMin m)

delete :: forall a. Ord a => a -> Set a -> Set a
delete k (Set m) = Set (Map.delete k m)

asCycles :: Sym -> List (List Int)
asCycles s = List.sort (go Nil (oneUpTo n))
  where
  n = setSize s
  go cycles points =
    case popMin points of
      Nothing ->
        cycles
      Just (Tuple i points') ->
        let c = unsafePartial (cycleOf s i)
            cycles' = if List.null c then cycles else c : cycles
         in go cycles' (foldl (flip delete) points' c)

-- Compute the cycle containing a given point.
cycleOf :: Partial => Sym -> Int -> List Int
cycleOf s init =
  if f init == init
    then Nil
    else List.reverse (go (init : Nil) init)
  where
  f i = fromJust (applySym s i)
  go cyc i =
    let fi = f i
     in if fi == init
          then cyc
          else go (fi : cyc) fi

applySym :: Sym -> Int -> Maybe Int
applySym (Sym xs) i = List.index xs (i - 1)

-- | The number of elements in the underlying set of a bijection.
setSize :: Sym -> Int
setSize (Sym xs) = List.length xs

unSym :: Sym -> List Int
unSym (Sym xs) = xs

-- | `symmetric n` gives you the entire group S_n.
symmetric :: Int -> List Sym
symmetric 0 = Nil
symmetric 1 = Sym (1 : Nil) : Nil
symmetric n | n < 0 = Nil
symmetric n = do
  s <- symmetric (n - 1)
  i <- List.range 0 (n - 1)
  maybe Nil (pure <<< Sym) (List.insertAt i n (unSym s))

-- | `alternating n` gives you the entire group A_n.
alternating :: Int -> List Sym
alternating = List.filter ((_ == 1) <<< sgn) <<< symmetric

-- | The inversions of a permutation, i.e. pairs of points x, y such that x <
-- | y and s x > s y.
inversions :: Sym -> List (Tuple Int Int)
inversions s =
  let n = setSize s
      f i = unsafePartial (fromJust (applySym s i))
   in do x <- List.range 1 (n-1)
         y <- List.range (x+1) n
         guard (x < y)
         if f x > f y then pure (Tuple x y) else mempty

-- | The sign of a permutation; 1 if there are an even number of inversions,
-- | -1 otherwise.
sgn :: Sym -> Int
sgn s = if Int.even (List.length (inversions s)) then 1 else -1
