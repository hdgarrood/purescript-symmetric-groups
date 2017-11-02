module Main where

-- We seek to answer the question: given a group G and subgroup H of G of index
-- t > 1, what is the kernel of the homomorphism phi : G -> S_t given by
-- labelling each of the cosets of H from 1 up to t and defining phi(g) as the
-- function that takes the coset aH to the coset (ga)H?

import Prelude
import Data.SymmetricGroup
import Data.Set (Set)
import Data.Set as Set
import Data.Foldable (all)
import Data.List ((:), List(..))
import Data.Array as Array
import Control.Monad.Eff.Console (log)
import Partial.Unsafe (unsafePartial)
import Data.Maybe (Maybe(..), fromJust)
import Data.Tuple (Tuple(..), snd, fst)
import Data.Foldable (traverse_, for_)
import Test.Assert (assert)
import Data.Monoid (mempty)

testWith _H _G =
  let cosets_ = Array.fromFoldable (cosets _H _G)
      labelCoset c = map (_ + 1) (Array.elemIndex c cosets_)
      unlabelCoset i = Array.index cosets_ (i - 1)
      t = Array.length cosets_
      phi g = unsafePartial $ Sym $ reduce $
                Array.range 1 t
                # map (\i -> fromJust do
                   aH <- unlabelCoset i
                   let gaH = actLeft g aH
                   labelCoset gaH)
      graph = map (\g -> Tuple g (phi g)) (Array.fromFoldable _G)
  in do
    for_ _G \g ->
      for_ cosets_ \aH ->
        assert (Just (actLeft g aH) == (labelCoset aH >>= (unlabelCoset <<< asFunction (phi g))))
    -- traverse_ (log <<< show) graph
    log "kernel:"
    traverse_ (log <<< show) (map fst (Array.filter (snd >>> (_ == mempty)) graph))

-- The Klein four-group; isomorphic to C_2 x C_2.
_V4 =
  Set.fromFoldable [ mempty
                  , fromCycles ((1:2:Nil):(3:4:Nil):Nil)
                  , fromCycles ((1:3:Nil):(2:4:Nil):Nil)
                  , fromCycles ((1:4:Nil):(2:3:Nil):Nil)
                  ]


main =
  -- Note: V4 is normal in this S4, i.e. S4 is not simple and the kernel of phi
  -- in the case where H = V4 and G = S4 can be (in fact is) nontrivial.
  let _S4 = Set.fromFoldable (symmetric 4)
      _A4 = Set.fromFoldable (alternating 4)
      _A5 = Set.fromFoldable (alternating 5)
  in do
    log "=== V4 <= S4 ==="
    testWith _V4 _S4
    log "=== V4 <= A5 ==="
    testWith _V4 _A5
    log "=== A4 <= A5 ==="
    testWith _A4 _A5
