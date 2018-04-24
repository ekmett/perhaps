-----------------------------------------------------------------------------
-- |
-- Copyright   :  (c) Edward Kmett 2018
-- License     :  BSD3
-- Maintainer  :  ekmett@gmail.com
-- Stability   :  stable
-- Portability :  portable
--
-----------------------------------------------------------------------------

module Data.Perhaps
  ( 
  -- * Maybe with an undisclosed error
    Perhaps(..)
  , believe
  , mayhap
  , excuse
  ) where

import Control.Monad.Perhaps
