module RandUtils where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Control.Lens
import Data.Maybe
import Control.Monad.Random
import Data.Foldable
import System.Random.Shuffle

import Utils

newtype NoOrder a = NoOrder { getNoOrder :: a}

instance Eq (NoOrder a) where
  _ == _ = True
instance Ord (NoOrder a) where
  compare _ _ = EQ

basicStats :: (MonadRandom m, Floating n) => Int -> m n -> m (n, n)
basicStats n gen = onlineAvgStDev <$> replicateM n gen

maximizer :: (MonadRandom m, Ord t) => (r -> t) -> Int -> m r -> m r
maximizer func n gen = maxWith <$> replicateM n gen
  where maxWith = getNoOrder . snd . maximum . fmap phi
        phi r = (func r, NoOrder r)
