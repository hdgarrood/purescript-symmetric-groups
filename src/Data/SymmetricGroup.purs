-- | One important example of a group which arises very often in group theory
-- | and its applications is the *symmetric group* on some set X, which is
-- | the group of bijective functions from X to itself. The group operation
-- | here is function composition and the identity element is the identity
-- | function. (If I've lost you by this point, the first few of chapters of
-- | the [PureScript numeric hierarchy
-- | guide](https://a-guide-to-the-purescript-numeric-hierarchy.readthedocs.io/en/latest/)
-- | should help.)
-- |
-- | We often restrict our attention to just the symmetric groups on finite
-- | sets, since they are a little easier to deal with. Since we are dealing
-- | with a finite set, we might as well label the elements of the set from 1
-- | up to n (where n is the size of the set); the group structure will be
-- | the same no matter how we have labelled the elements of the underlying
-- | set. The symmetric group on a set X can be written S(X); if X is the set
-- | {1,2,...,n} we often abuse notation and write the group S(X) as just
-- | S(n).
-- |
-- | Some vocabulary first: if f is a function from the set X to itself, we
-- | say that x is a *fixed point* of f if and only if f(x) = x. We sometimes
-- | say that "f *fixes* x" instead, since this is less of a mouthful than "x
-- | is a fixed point of f".
-- |
-- | When attempting to represent the group S(n) in PureScript, one approach
-- | might be to define a type constructor of kind `Type -> Type`, where the
-- | argument is a type-level natural number representing n. This approach
-- | quickly runs into a problem, though, which is that there is no
-- | (ergonomic) type for natural numbers less than or equal to a certain
-- | number. For example, Idris has `Fin n`, which is the type of integers
-- | between 0 and n-1. Of course, it is possible to define a similar type in
-- | PureScript, but without dependent types it will not be nearly as
-- | comfortable to use as Idris' `Fin`. However, we want to have some way of
-- | converting elements of this set to standard PureScript functions\*, but
-- | without an ergonomic type `Fin` we will need to use `Partial`
-- | constraints (yuck).
-- |
-- | We also would like to be able to do things like embed S(n) into S(n+1)
-- | without too much effort (that is, without having to convert between two
-- | different types): note that every permutation f on a set of n elements
-- | can be extended to a permutation f' on a set of n+1 elements just by
-- | saying that f' fixes n+1 and does the same as f for everything else,
-- | i.e. f'(k) = f(k) for all k ≤ n.
-- |
-- | There is a simple trick we can use to address this. We say that a
-- | permutation is *finitary* if and only if it fixes all but finitely many
-- | points. For example, the permutation on the set of natural numbers which
-- | swaps 1 and 2 and fixes everything else is finitary; the permutation
-- | which swaps every even number with the odd number preceding it is not.
-- | It turns out that the product of two finitary permutations is itself
-- | finitary, and also that the inverse of a finitary permutation is
-- | finitary (exercise!). Therefore the set of finitary permutations on a
-- | set X is a group (in fact a subgroup of S(X)), which we will refer to as
-- | FS(X).
-- |
-- | The design adopted by this library is to define a type representing the
-- | group FS(ℕ) of finitary permutations on the natural numbers. Then, for
-- | any natural number n, there is a natural embedding of S(n) into FS(ℕ)
-- | by just fixing everything greater than or equal to n; in the same way
-- | there is a natural embedding of S(k) into S(n) (within FS(ℕ)) whenever k
-- | < n.
-- |
-- | Perhaps surprisingly, [Cayley's
-- | Theorem](https://en.wikipedia.org/wiki/Cayley's_theorem) tells us that
-- | any finite group is isomorphic to a subgroup of S(n), so we can in fact
-- | represent any finite group at all using this library (although this
-- | fact might mostly just be a curiosity).
-- |
-- | ---
-- |
-- | \*note: we don't use standard PureScript functions directly, as it is
-- | not an efficient representation for many of the operations we would like
-- | to be able to do, and also it is harder to guarantee that the function
-- | in question is bijective.
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
import Control.Monad.ST (pureST)
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
import Data.Foldable (for_, foldl, foldMap, maximum, sum)
import Data.Array as Array
import Data.Array.ST (thaw, unsafeFreeze, pokeSTArray)
import Data.Array.ST.Iterator as Iter
import Data.List (List(..), (:))
import Data.List as List

-- | The type `Sym` represents the group FS(ℕ) of finitary permutations of the
-- | set of natural numbers. Values of this type cannot be constructed from
-- | functions of type `Int -> Int`, because we cannot easily verify that these
-- | are bijective. Instead, use `fromCycle` or `fromCycles`.
-- |
-- | The runtime representation of a value of this type is an array with k
-- | elements, where k is the largest number which is not a fixed point of f;
-- | if k is very large this may be a problem.
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
-- | `asCycles <<< fromCycles` is not equal to `id`, because in general there
-- | are lots of different ways to write any given permutation as a product of
-- | cycles. However, `fromCycles <<< asCycles` is equal to `id`.
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

-- | Convert a finitary permutation into a regular function. The resulting
-- | function fixes all negative numbers.
-- |
-- | ```purescript
-- | f = asFunction (fromCycle (1 : 2 : 3 : Nil))
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
-- | f = asFunction (fromCycles ((1 : 3 : Nil) : (2 : 4 : Nil) : Nil))
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
-- |
-- | ```purescript
-- | fromCycle (1:2:Nil) == fromCycle (1:2:1:Nil)
-- | fromCycle (1:2:Nil) == fromCycle (1:2:0:Nil)
-- | fromCycle (1:2:Nil) == fromCycle (1:2:(-1):Nil)
-- | ```
fromCycle :: List Int -> Sym
fromCycle is =
  let js = List.nub $ List.filter (_ > 0) is
      n = fromMaybe 1 (maximum js)
      graph = cycleGraph js
   in Sym (reduce (pureST do
        arr <- thaw (Array.range 1 n)
        for_ graph \(Tuple x y) ->
          void (pokeSTArray arr (x - 1) y)
        unsafeFreeze arr))

-- | O(n), where n is the length of the input list/cycle. Generate the graph of
-- | a cycle (omitting fixed points).
cycleGraph :: List Int -> List (Tuple Int Int)
cycleGraph Nil          = Nil
cycleGraph (_:Nil)      = Nil
cycleGraph (i1:i2:tail) = List.reverse $ go (pure (Tuple i1 i2)) i2 tail
  where
  go acc im Nil        = Tuple im i1 : acc
  go acc im (im1:rest) = go (Tuple im im1 : acc) im1 rest

-- | The smallest natural number N for which the given permutation fixes all
-- | numbers greater than or equal to N.
-- |
-- | ```purescript
-- | minN (fromCycle (1:2:Nil)) == 3
-- | ```
minN :: Sym -> Int
minN (Sym xs) = Array.length xs + 1

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

-- | `symmetric n` gives you every element of the group S(n) in an array.
symmetric :: Int -> Array Sym
symmetric = map (Sym <<< reduce) <<< permutations

-- | `alternating n` gives you every element of the group A(n) -- that is, the
-- | subgroup of S(n) given by the even permutations -- in an array.
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
-- | is the identity. Restricting `Sym` to finitary permutations ensures that
-- | this is always finite.
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

-- | The set containing just the identity element of a group (i.e. `mempty`).
trivialSubgroup :: forall a. Ord a => Group a => Set a
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

-- | Given a set of permutations, form the subgroup generated by that set. This
-- | function is idempotent, that is, `subgroup (subgroup a) = subgroup a`.
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
