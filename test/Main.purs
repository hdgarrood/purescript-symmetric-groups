module Test.Main where

import Prelude
import Data.SymmetricGroup

import Data.Int as Int
import Data.List as List
import Data.List (List(..), (:))
import Data.Monoid (mempty, power)
import Data.Group (ginverse)
import Data.Foldable (for_, product, all)
import Data.Array as Array
import Test.Assert (assert)
import Control.Monad.Eff.Console (log)

fact n = product (Array.range 1 n)

main = do
  for_ (Array.range 2 6) \n -> do
     log $ "testing `symmetric` and `alternating` (n=" <> show n <> ")"
     let sn = symmetric n
         an = alternating n

     assert (Array.nub sn == sn)
     assert (Array.length sn == fact n)
     assert (Array.length an == fact n / 2)

  let s4 = symmetric 4
  let s5 = symmetric 5

  log "associativity"
  for_ s4 \a ->
    for_ s4 \b ->
      for_ s4 \c ->
        assert ((a <> b) <> c == a <> (b <> c))

  log "identity"
  for_ s5 \a -> do
    assert (a <> mempty == a)
    assert (mempty <> a == a)

  log "inverses"
  for_ s5 \a -> do
    assert (a <> ginverse a == mempty)
    assert (ginverse a <> a == mempty)

  log "parity = parity of inversions"
  for_ s5 \a ->
    assert (parity a == Int.parity (Array.length (inversions a)))

  log "parity is a group homomorphism"
  for_ s4 \a ->
    for_ s4 \b ->
      assert (parity a + parity b == parity (a <> b))

  log "fromCycles <<< asCycles = id"
  for_ s5 \a ->
    assert (fromCycles (asCycles a) == a)

  log "order"
  for_ s5 \a ->
    let n = order a
    in if n > 1
         then assert (all (_ /= mempty) (map (power a) (List.range 1 (n - 1))))
         else assert (a == mempty)

  log "fromCycle ignores duplicates"
  assert (fromCycle (1:2:Nil) == fromCycle (1:2:1:Nil))

  log "fromCycle ignores nonpositives"
  assert (fromCycle (1:2:Nil) == fromCycle (1:2:0:Nil))
  assert (fromCycle (1:2:Nil) == fromCycle (1:2:(-1):Nil))

  log "minN"
  assert (minN mempty == 1)
  assert (minN (fromCycle (1:2:Nil)) == 3)
  for_ s5 \a -> assert (minN a <= 6)

  log "asFunction"
  for_ s4 \a ->
    for_ s4 \b ->
      for_ (Array.range 1 4) \i ->
        assert (asFunction a (asFunction b i) == asFunction (a <> b) i)
