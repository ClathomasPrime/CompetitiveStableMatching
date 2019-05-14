module Rand where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Control.Lens
import Data.Maybe
import Control.Monad.Random
import Data.Foldable
import System.Random.Shuffle
import Data.List

import Main
import RandUtils
import Utils

-- newtype W = W Int
--   deriving(Eq, Ord, Show)
--
-- newtype M = M Int
--   deriving(Eq, Ord, Show)

randomFullLengthList :: (Enum t, MonadRandom m) => Int -> t -> m [t]
randomFullLengthList len t = shuffleM [t..toEnum (fromEnum t + len - 1)]

randomPrefSet :: (Enum s, Ord s, Enum t, MonadRandom m)
  => Int -> s -> Int -> t -> m (Map s [t])
randomPrefSet numMen s numWomen t =
  M.fromList . zip [s..toEnum (fromEnum s + numMen)] <$>
    replicateM numMen (randomFullLengthList numWomen t)

unbalancedRandomMarketFrom :: (Enum s, Ord s, Enum t, Ord t, MonadRandom m) =>
  Int -> s -> Int -> t -> m (Map s [t], Map t [s])
unbalancedRandomMarketFrom nmen s nwomen t =
  (,) <$> randomPrefSet nmen s nwomen t <*> randomPrefSet nwomen t nmen s

unbalancedRandomMarket :: MonadRandom m =>
  Int -> Int -> m (Map Int [Int], Map Int [Int])
unbalancedRandomMarket nmen nwomen =
  (,) <$> randomPrefSet nmen 1 nwomen 1 <*> randomPrefSet nwomen 1 nmen 1

balancedRandomMarket :: MonadRandom m => Int -> m (Map Int [Int], Map Int [Int])
balancedRandomMarket num = unbalancedRandomMarket num num





nFixedVsStableBalanced :: IO (Int,Int)
nFixedVsStableBalanced = do
  let nMen = 20
      nWomen = nMen - 1
  (m, w) <- unbalancedRandomMarket nMen nWomen
  let unbalancedScore = numNonfixed m w

      balancedMarkets =
        [(M.delete i m, M.map (filter (/=i)) w)
        | i <- M.keys m]
      minBalancedScore = minimum . fmap (uncurry numNonfixed) $ balancedMarkets

  return (unbalancedScore, minBalancedScore)


experim1 :: IO ()
experim1 = do
  let convt :: Int -> Double
      convt = fromIntegral
  s1 <- basicStats 1000 (convt . fst <$> nFixedVsStableBalanced)
  print s1
  s2 <- basicStats 1000 (convt . snd <$> nFixedVsStableBalanced)
  print s2
  s3 <- basicStats 1000 (convt . uncurry numNonfixed <$> balancedRandomMarket 19)
  print s3
  return ()

-----------------------------------------------------------------------



womenTruncate :: Int -> IO [Double]
womenTruncate k = do
  fmap (over mapped avg . transpose) . replicateM 1000 $ do
    let numMen = 20
        numWomen = numMen
    (menPrefs, womanPrefs) <- balancedRandomMarket numMen
    let womanPrefs' = fmap (take k) womanPrefs
        (menRanks, womenRanks) = avgRanksManOpt menPrefs womanPrefs'
        (menMatched, womenMatched) = numUnmatchedInStable menPrefs womanPrefs'
    return [menMatched / fromIntegral numMen, menRanks,
      womenRanks, womenMatched / fromIntegral numWomen]
