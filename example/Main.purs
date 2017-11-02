module Main where

-- We seek to answer the question: given a subgroup H of A_5 of index t > 1,
-- what is the kernel of the homomorphism phi : A_5 -> S_t given by labelling
-- each of the cosets of H from 1 up to t and defining phi(g) as the function
-- that takes the coset aH to the coset (ga)H?

import Prelude
import Data.SymmetricGroup
import Data.Foldable (all)
import Data.List ((:), List(..))
import Data.Array (filter)
import Control.Monad.Eff.Console (log)

main =
  let h = subgroup (setFromFoldable [fromCycle (1:2:3:4:Nil)])
      g = symmetric 4
      cosets_ = cosets h (setFromFoldable g)
      phi = actLeft
      isInKernel s = all (\c -> phi s c == c) (setToArray cosets_)
      kernel = filter isInKernel g
  in
    log $ show $ kernel

