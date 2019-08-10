module Utils where

import Control.Lens
import Data.List
import Data.Maybe
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import Control.Monad.RWS
import Data.Functor.Contravariant

record :: (a -> b) -> a -> (a, b)
record f a = (a, f a)

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

--------------------------------------------------------------------------------

whileAvailable :: Monad m => m (Maybe a) -> (a -> m b) -> m [b]
whileAvailable p m = do
  r <- p
  case r of
    Nothing -> return []
    Just a -> do { b <- m a ; (b:) <$> whileAvailable p m }

takeAccumWhileM :: Monad m => [a] -> b -> (a -> b -> m (Bool, b)) -> m ([a], b)
takeAccumWhileM [] b _ = return ([], b)
takeAccumWhileM (a:as) b act = do
  (res, b') <- act a b
  if res
    then do (as',b'') <- takeAccumWhileM as b' act
            return (a:as', b'')
    else return ([], b')

takeWhileM :: Monad m => (a -> m Bool) -> [a] -> m [a]
takeWhileM p [] = return []
takeWhileM p (a:as) = do
  b <- p a
  if b then (a:) <$> takeWhileM p as else return []

whileM_ :: Monad m => m Bool -> m a -> m ()
whileM_ p m = do
  v <- p
  if v then m >> whileM_ p m else return ()

doWhileM_ :: Monad m => m Bool -> m ()
doWhileM_ m = do
  b <- m
  if b then doWhileM_ m else return ()

-- note: asumes predicate will be satisfied at most once in the list
betweenPredicatesMap :: (a -> Bool) -> (a -> Bool) -> (a -> a) -> [a] -> [a]
betweenPredicatesMap _ _ _ [] = []
betweenPredicatesMap aftThis befThis phi (a:as)
  | aftThis a = a : btwMap' as
  | befThis a = a:as
  | otherwise = a : betweenPredicatesMap aftThis befThis phi as
  where btwMap' [] = []
        btwMap' (a:as)
          | befThis a = a:as
          | otherwise = phi a : btwMap' as

performIfSucceeds :: MonadState s m => m (Maybe a) -> m (Maybe a)
performIfSucceeds m = do
  s <- get
  res <- m
  case res of
    Nothing -> put s >> return Nothing
    Just a -> return (Just a)

halfs :: [a] -> ([a], [a])
halfs list = (take k list, drop k list)
  where k = length list `div` 2

nproduct :: Int -> [a] -> [[a]]
nproduct 0 _ = [ [] ]
nproduct n as = (:) <$> as <*> nproduct (n-1) as

splits :: [a] -> [([a], [a])]
splits [] = [([], [])]
splits (a:as) = ([],a:as) : fmap (\(u,v) -> (a:u, v)) (splits as)

rotate :: Int -> [a] -> [a]
rotate _ [] = []
rotate n xs = zipWith const (drop n (cycle xs)) xs

-- Fold (Map k v) k = forall f. (Contravariant f, Applicative f) =>
--   (a -> f a) -> Map k v -> f (Map k v)
keysF :: Fold (Map k v) k
keysF f = M.traverseWithKey (\k v -> phantom (f k))
--                     :: (k -> v -> f v)           -> Map k v -> f (Map k b)
-- phantom is kinda like ``f puts my key in a container with no values, convert it to have the correct type''
--   (phantom takes a contravariant and covariant - these can't meaningfully hold stuff)
-- [21:55] <Solonarv> the rest of the explanation is: optics tend to have a type that looks a bit like that of 'traverse'
-- [21:55] <Solonarv> traverse     :: forall f.  Applicative f                   => (a -> f a) -> t a -> f (t a)
-- [21:55] <Solonarv> type Fold s a = forall f. (Applicative f, Contravariant f) => (a -> f a) -> s   -> f  s
-- [21:56] <Solonarv> and there is a function in Data.Map with a type that looks very close to what we want - namely, traverseWithKey
