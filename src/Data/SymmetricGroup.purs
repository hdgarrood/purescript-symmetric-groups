module Data.SymmetricGroup
  ( Sym
  -- construction
  , fromCycle
  , fromCycles

  -- elimination
  , asCycles
  , asFunction

  -- attributes of permutations
  , cycleOf
  , minN
  , inversions
  , parity
  , order

  -- subgroups
  , permutations
  , symmetric
  , alternating
  , trivialSubgroup
  , subgroup
  , actLeft
  , cosets
  , module ReExports
  ) where

import Prelude
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.Tuple (Tuple(..), snd)
import Data.Monoid (class Monoid, mempty, power)
import Data.Group (class Group)
import Data.Int as Int
import Data.Int (Parity(..))
import Data.Int (Parity(..)) as ReExports
import Data.String as String
import Data.Set (Set)
import Data.Set as Set
import Data.Foldable (foldl, foldMap, maximum, sum)
import Data.Array as Array
import Data.List (List(..), (:))
import Data.List as List

-- | The type `Sym` represents the group of bijections f on the set of natural
-- | numbers, which fix all but finitely many points. Equivalently, there
-- | exists some natural N such that for all n >= N, n is a fixed point of f.
-- | The group operation is composition, and the identity element is the
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
reduce xs =
  if tailLength == 0
    then xs
    else Array.take (n - tailLength) xs
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

-- | Represent a permutation as a list of cycles. Note that
-- | `asCycles <<< fromCycles` is not equal to `id`, because the cycles might
-- | come out in a different order. However, `fromCycles <<< asCycles` is equal
-- | to `id`.
-- |
-- | ```purescript
-- | asCycles (fromCycles ((1 : 2 : 3 : Nil) : Nil))
-- |  == (1 : 2 : 3 : Nil) : Nil
-- | ```
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
         in go cycles' (foldl (flip Set.delete) points' (i : c))

-- | Compute the cycle containing a given point.
-- |
-- | ```purescript
-- | f = fromCycles ((1 : 3 : Nil) : (2 : 4 : Nil) : Nil)
-- |
-- | cycleOf f 1 == 1 : 3 : Nil
-- | cycleOf f 2 == 2 : 4 : Nil
-- | cycleOf f 5 == Nil
-- | ```
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

-- | Convert a permutation into a regular function.
-- |
-- | ```purescript
-- | f = asFunction (fromCycles ((1 : 2 : 3 : Nil) : Nil))
-- |
-- | f 1 == 2
-- | f 2 == 3
-- | f 3 == 1
-- | f 4 == 4
-- | f (-1) == (-1)
-- | ```
asFunction :: Sym -> Int -> Int
asFunction (Sym xs) i = fromMaybe i (Array.index xs (i - 1))

-- | Construct a permutation from a list of cycles.
-- |
-- | ```purescript
-- | f = fromCycles ((1 : 3 : Nil) : (2 : 4 : Nil) : Nil)
-- |
-- | f 1 == 3
-- | f 2 == 4
-- | f 3 == 1
-- | f 4 == 2
-- | ```
fromCycles :: List (List Int) -> Sym
fromCycles = foldMap fromCycle

-- | Generate a permutation given a single cycle. If the given list includes
-- | nonpositive or duplicate elements they will be ignored.
fromCycle :: List Int -> Sym
fromCycle is =
  let js = List.nub $ List.filter (_ > 0) is
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

-- | The minimum natural number N for which the given permutation fixes all n
-- | >= N.
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
alternating = Array.filter ((_ == Even) <<< parity) <<< symmetric

composeSym :: Sym -> Sym -> Sym
composeSym s1 s2 =
  let n = max (minN s1) (minN s2)
      f = asFunction s1 <<< asFunction s2
   in Sym (reduce (map (f $ _) (Array.range 1 n)))

invertSym :: Sym -> Sym
invertSym =
  -- no need to reduce here since minN is unchanged
  Sym
  <<< map ((_ + 1) <<< snd)
  <<< Array.sort
  <<< Array.mapWithIndex (flip Tuple)
  <<< unSym

-- | The order of a permutation; the smallest positive integer n such that s^n
-- | is the identity.
order :: Sym -> Int
order = foldl lcm 1 <<< map List.length <<< asCycles

-- | The inversions of a permutation, i.e. for a permutation f, this function
-- | returns all pairs of points x, y such that `x < y` and `f x > f y`.
-- |
-- | The parity of the number of inversions of a permutation is equal to the
-- | parity of the permutation itself.
inversions :: Sym -> Array (Tuple Int Int)
inversions s =
  let n = minN s
      f = asFunction s
   in do x <- Array.range 1 (n - 1)
         y <- Array.range (x + 1) n
         if f x > f y then pure (Tuple x y) else mempty

-- | The parity of a permutation. All permutations can be expressed as products
-- | of 2-cycles: for example (1 2 3) can be written as (2 3)(1 3). The parity
-- | of a permutation is defined as the parity of the number of 2-cycles when
-- | it is written as a product of 2-cycles, so e.g. (1 2 3) is even.
-- |
-- | This function is a group homomorphism from the group Sym to the additive
-- | group of the field of two elements (here represented by the `Parity`
-- | type); that is,
-- |
-- | ```purescript
-- | parity f + parity g = parity (f <> g)
-- | ```
-- |
-- | holds for all permutations `f`, `g`.
-- |
-- | The parity of a permutation is sometimes also called the "sign" or
-- | "signature".
parity :: Sym -> Parity
parity = sum <<< map cycleSgn <<< asCycles
  where
  cycleSgn :: List Int -> Parity
  cycleSgn Nil = Even
  cycleSgn xs = if Int.odd (List.length xs) then Even else Odd

trivialSubgroup :: Set Sym
trivialSubgroup = Set.fromFoldable [mempty]

-- | Given a subgroup H and a permutation s, form the subgroup generated by the
-- | union of H with {s}.
extendSubgroup :: Sym -> Set Sym -> Set Sym
extendSubgroup s h =
  let n = order s
      h' = Array.fromFoldable h
   in Set.fromFoldable do
        t <- h'
        i <- Array.range 0 (n - 1)
        let si = power s i
        [ si <> t, t <> si ]

-- | Given a set of permutations, form the subgroup generated by that set.
subgroup :: Set Sym -> Set Sym
subgroup = foldl (flip extendSubgroup) trivialSubgroup <<< Array.fromFoldable

-- | If `h` is a subgroup, then `actLeft s h` gives the coset formed by
-- | applying `s` to each element of `h` on the left.
actLeft :: forall a. Ord a => Group a => a -> Set a -> Set a
actLeft s = Set.map (s <> _)

-- | If `h` is a subgroup of `g`, then `cosets h g` gives the set of cosets of
-- | `h` in `g`. Otherwise, the behaviour of this function is undefined.
cosets :: forall a. Ord a => Group a => Set a -> Set a -> Set (Set a)
cosets h = Set.map (\t -> actLeft t h)

-- Utilities
oneUpTo :: Int -> Set Int
oneUpTo n = Set.fromFoldable (List.range 1 n)

popMin :: Set Int -> Maybe (Tuple Int (Set Int))
popMin s = map (\x -> Tuple x (Set.delete x s)) (Set.findMin s)
