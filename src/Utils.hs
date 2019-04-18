module Utils where

import Control.Lens
import Data.List
import Data.Maybe
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

invert :: (Ord a, Ord b) => Map a b -> Map b a
invert map1 = M.foldlWithKey inserto (M.empty) map1
  where inserto m k v = M.insert v k m

deleteOnes :: Ord a => Map a b -> [Map a b]
deleteOnes m = map (\i -> M.delete i m) $ M.keys m

deleteNth :: Int -> [a] -> [a]
deleteNth _ [] = []
deleteNth 0 (a:as) = as
deleteNth i (a:as) = a : deleteNth (i-1) as

prefIndexOf :: (Ord a, Ord b, Num n) => Map b [a] -> b -> a -> n
prefIndexOf womenPrefs woman man =
  let Just prefList = womenPrefs ^. at woman
   in case elemIndex man prefList of
        Nothing -> error "pref against someone not on list"
        Just i -> 1 + fromIntegral i

avg :: Floating n => [n] -> n
avg = fst . onlineAvgStDev

onlineAvgStDev :: Floating n => [n] -> (n,n)
onlineAvgStDev ns = over _2 sqrt $ onlineAvgStDev' 0 0 0 ns
  where onlineAvgStDev' xbar sumVar count [] =
          (xbar, sumVar / (count - 1))
        onlineAvgStDev' xbar sumVar count (x:xs) =
          let count' = count + 1
              xbar' = xbar + (x - xbar) / count'
              sumVar' = sumVar + (x - xbar) * (x - xbar')
           in onlineAvgStDev' xbar' sumVar' count' xs

topAfter :: (Ord a, Ord b) => Map a [b] -> a -> b -> Maybe b
topAfter prefs man woman = do
  manPrefs <- M.lookup man prefs
  w <- listToMaybe . drop 1 . dropWhile (/= woman) $ manPrefs
  return w

