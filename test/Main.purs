module Test.Main where

import Prelude
import Data.SymmetricGroup

import Data.Monoid (mempty)
import Data.Group (ginverse)
import Data.Foldable (for_)
import Data.Array as Array
import Test.Assert (assert)
import Control.Monad.Eff.Console (log)

main = do
  let s4 = symmetric 4
  let a4 = alternating 4

  log "nub s4 == s4"
  assert (Array.nub s4 == s4)

  log "length s4 == 24"
  assert (Array.length s4 == 24)

  log "associativity holds in s4"
  for_ s4 \a ->
    for_ s4 \b ->
      for_ s4 \c ->
        assert ((a <> b) <> c == a <> (b <> c))

  log "identity in s4"
  for_ s4 \a -> do
    assert (a <> mempty == a)
    assert (mempty <> a == a)

  log "length a4 == 12"
  assert (Array.length a4 == 12)

  log "sgn homomorphism"
  for_ s4 \a ->
    for_ s4 \b ->
      assert (sgn a * sgn b == sgn (a <> b))

  log "fromCycles <<< asCycles = id"
  for_ s4 \s ->
    assert (fromCycles (asCycles s) == s)

  -- log "inverses in s4"
  -- for_ s4 \a -> do
  --   assert (ginverse a <> a == mempty)
  --   assert (a <> ginverse a == mempty)
