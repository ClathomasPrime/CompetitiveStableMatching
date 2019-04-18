module RandUtils where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Control.Lens
import Data.Maybe
import Control.Monad.Random
import Data.Foldable
import System.Random.Shuffle

import Utils

basicStats :: (MonadRandom m, Floating n) => Int -> m n -> m (n, n)
basicStats n gen = onlineAvgStDev <$> replicateM n gen

