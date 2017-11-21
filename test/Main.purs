module Test.Main where

import Prelude
import Data.SymmetricGroup

import Data.Int as Int
import Data.Monoid (mempty)
import Data.Group (ginverse)
import Data.Foldable (for_, product)
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

  log "sgn = parity of inversions"
  for_ s4 \a ->
    assert (sgn a == if Int.even (Array.length (inversions a)) then 1 else -1)

  log "sgn homomorphism"
  for_ s4 \a ->
    for_ s4 \b ->
      assert (sgn a * sgn b == sgn (a <> b))

  log "fromCycles <<< asCycles = id"
  for_ s5 \s ->
    assert (fromCycles (asCycles s) == s)
