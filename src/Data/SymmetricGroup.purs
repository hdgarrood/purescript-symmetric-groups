module Data.SymmetricGroup where
--  ( Sym
--  , symmetric
--  , alternating
--  , permutations
--  , asCycles
--  , minN
--  , unSym
--  , inversions
--  , sgn
--  , order
--  ) where

import Prelude
import Control.MonadPlus (guard)
import Data.Monoid (class Monoid, mempty)
import Data.Group (class Group)
import Data.Maybe
import Data.Tuple
import Data.Int as Int
import Data.String as String
import Data.Foldable (foldl, foldMap, maximum)
import Data.Map (Map)
import Data.Map as Map
import Data.Array as Array
import Data.List (List(..), (:))
import Data.List as List

-- | The type `Sym` represents the group of bijections f on the set of natural
-- | numbers, for which there exists some natural N such that for all n >= N,
-- | n is a fixed point of f; that is, f m /= m only for finitely many naturals
-- | m. The group operation is composition, and the identity element is the
-- | identity function.
-- |
-- | This slightly strange representation allows us to easily consider, eg, S_5
-- | as a group in its own right (by identifying it with the subgroup of
-- | bijections which fix all n >= 6), or as a subgroup of S_6, or of S_7, and
-- | so on.
-- |
-- | In particular, every finite symmetric group S_n can be identified with a
-- | subgroup of the `Sym` group in the above way.
newtype Sym = Sym (Array Int)

-- A value of type `Sym` is represented by an array of integers such that the
-- bijection can be converted to a standard PureScript function as follows:
--
--   asFunction (Sym xs) i = fromMaybe i (Array.index xs (i - 1))
--
-- The array should therefore contain each integer from 1 to n exactly once for
-- some n; if any integer appeared twice then the function would not be
-- injective. The array should also be the shortest array representing that
-- bijection. For example, the arrays [2,1,3] and [2,1] represent the same
-- bijection: the one which swaps 1 and 2 and fixes everything else. Therefore
-- the latter representation is the only valid representation of this
-- bijection.

-- Drop a superfluous tail in a bijection, if any. The given array must not
-- have any repeated elements.
reduce :: Array Int -> Array Int
reduce xs = Array.take (n - tailLength) xs
  where
  n = Array.length xs
  tailLength = go 0 n
  go count m = if Array.index xs (m - 1) == Just m
                 then go (count + 1) (m - 1)
                 else count

derive newtype instance eqSym :: Eq Sym
derive newtype instance ordSym :: Ord Sym

instance showSym :: Show Sym where
  show s =
    let cs = asCycles s
        showCycle c =
          "(" <>
          String.joinWith " " (map show (List.toUnfoldable c)) <>
          ")"
     in if List.null cs
          then "e"
          else foldMap showCycle cs

instance semigroupSym :: Semigroup Sym where
  append = composeSym

instance monoidSym :: Monoid Sym where
  mempty = Sym []

instance groupSym :: Group Sym where
  ginverse = invertSym

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
  n = minN s
  go cycles points =
    case popMin points of
      Nothing ->
        cycles
      Just (Tuple i points') ->
        let c = cycleOf s i
            cycles' = if List.null c then cycles else c : cycles
         in go cycles' (foldl (flip delete) points' (i : c))

-- Compute the cycle containing a given point.
cycleOf :: Sym -> Int -> List Int
cycleOf s init =
  if f init == init
    then Nil
    else List.reverse (go (init : Nil) init)
  where
  f = asFunction s
  go cyc i =
    let fi = f i
     in if fi == init
          then cyc
          else go (fi : cyc) fi

asFunction :: Sym -> Int -> Int
asFunction (Sym xs) i = fromMaybe i (Array.index xs (i - 1))

fromCycles :: List (List Int) -> Sym
fromCycles = foldMap fromCycle

-- | Generate a permutation given a single cycle. If the given list includes
-- | nonpositive elements they will be ignored.
fromCycle :: List Int -> Sym
fromCycle is =
  let js = List.filter (_ > 0) is
      n = fromMaybe 1 (maximum js)
      orig = Array.range 1 n
      graph = cycleGraph js
   in Sym $ reduce $
        foldl (flip (\(Tuple ix m) ->
                        fromMaybe [] <<< Array.updateAt (ix - 1) m))
              orig
              graph

-- | Generate the graph of a cycle (omitting fixed points).
cycleGraph :: List Int -> List (Tuple Int Int)
cycleGraph Nil          = Nil
cycleGraph (_:Nil)      = Nil
cycleGraph (i1:i2:tail) = List.reverse $ go (pure (Tuple i1 i2)) i2 tail
  where
  go acc im Nil        = Tuple im i1 : acc
  go acc im (im1:rest) = go (Tuple im im1 : acc) im1 rest

-- | The minimum natural number N for which the given bijection fixes all n >=
-- | N.
minN :: Sym -> Int
minN (Sym xs) = max 1 (Array.length xs)

unSym :: Sym -> Array Int
unSym (Sym xs) = xs

-- | Returns all permutations of the array with elements from 1 up to n.
permutations :: Int -> Array (Array Int)
permutations n | n <= 0 = []
permutations 1 = [[1]]
permutations n = do
  p <- permutations (n - 1)
  i <- Array.range 0 (n - 1)
  maybe [] pure (Array.insertAt i n p)

-- | `symmetric n` gives you the entire group S_n.
symmetric :: Int -> Array Sym
symmetric = map (Sym <<< reduce) <<< permutations

-- | `alternating n` gives you the entire group A_n.
alternating :: Int -> Array Sym
alternating = Array.filter ((_ == 1) <<< sgn) <<< symmetric

composeSym :: Sym -> Sym -> Sym
composeSym s1 s2 =
  let n = max (minN s1) (minN s2)
      f = asFunction s1 <<< asFunction s2
   in Sym (reduce (map (f $ _) (Array.range 1 n)))

invertSym :: Sym -> Sym
invertSym =
  -- no need to reduce here since minN is unchanged
  Sym
  <<< map snd
  <<< Array.sort
  <<< Array.mapWithIndex (flip Tuple)
  <<< unSym

-- | The order of a permutation; the smallest positive integer n such that s^n
-- | is the identity.
order :: Sym -> Int
order = foldl lcm 1 <<< map List.length <<< asCycles

-- | The inversions of a permutation, i.e. pairs of points x, y such that x <
-- | y and s x > s y.
inversions :: Sym -> Array (Tuple Int Int)
inversions s =
  let n = minN s
      f = asFunction s
   in do x <- Array.range 1 (n - 1)
         y <- Array.range (x + 1) n
         if f x > f y then pure (Tuple x y) else mempty

-- | The sign of a permutation; 1 if there are an even number of inversions,
-- | -1 otherwise.
sgn :: Sym -> Int
sgn s = if Int.even (Array.length (inversions s)) then 1 else -1
