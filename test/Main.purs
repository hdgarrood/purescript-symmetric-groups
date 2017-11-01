module Test.Main where

import Prelude
import Data.SymmetricGroup
import Test.Assert (assert)
import Control.Monad.Eff.Console (log)

main = do
  log $ show $ symmetric 3
