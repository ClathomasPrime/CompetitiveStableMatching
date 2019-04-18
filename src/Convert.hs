module Convert where

import Data.Set (Set)
import qualified Data.Set as S
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Control.Lens
import Data.Maybe

import Control.Monad.State
import Control.Monad.Except

import Utils
import Main



--------------------------------------------------------------------------------
-- Monad
--------------------------------------------------------------------------------

data MatchingInput a b = MatchingInput
  { womenPrefs :: Map a [b]
  , menPrefs :: Map b [a]
  } deriving(Show, Read, Eq, Ord)

data MatchingState a b = MatchingState
  { unmatchedWomen :: Set b
  , menProposalStatus :: Map a ([b], Set b)
  , stableMatching :: Map b a
  , experimentalMatching :: Map b a
  } deriving(Show, Read, Eq, Ord)

performIfSucceeds :: MonadState s m => m (Maybe a) -> m (Maybe a)
performIfSucceeds m = do
  s <- get
  res <- m
  case res of
    Nothing -> put s >> return Nothing
    Just a -> return (Just a)

performIfSucceeds :: MonadState s m => m (Maybe a) -> m (Maybe a)
performIfSucceeds m = do
  s <- get
  res <- m
  case res of
    Nothing -> put s >> return Nothing
    Just a -> return (Just a)



--------------------------------------------------------------------------------
-- Algorithm as in the paper
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Constructing the full latice
--------------------------------------------------------------------------------

iic :: (Ord a, Ord b) =>
  Map a [b] -> Map b [a] -> Map b a -> b -> Maybe (Map a b)
iic menPrefs womanPrefs mu0 w0 = do
  man <- M.lookup w0 mu0
  iicManStep menPrefs womanPrefs mu0 man w0

iicManStep :: (Ord a, Ord b) =>
  Map a [b] -> Map b [a] -> Map b a -> a -> b -> Maybe (Map a b)
iicManStep menPrefs womanPrefs mu0 man w0 = do
  let mu' = M.delete w0 mu0
  nextWomen <- drop 1 . dropWhile (/= w0) <$> M.lookup man menPrefs
  undefined -- proposeDownList nextWomen
