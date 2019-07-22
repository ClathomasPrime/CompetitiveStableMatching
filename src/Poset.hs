{-# LANGUAGE FlexibleContexts, ConstraintKinds, TemplateHaskell,
  TupleSections, TypeFamilies, ScopedTypeVariables #-}
module Poset where

import qualified Data.Bimap as BM
import Data.Bimap (Bimap)
import Data.Set (Set)
import Data.Tuple
import qualified Data.Set as S
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Control.Lens
import Data.List
import Data.Maybe
import Data.Function
import Control.Monad.RWS

import Convert
import RandUtils
import Utils

-- independent / redone version of Convert. Because this is the good stuff.

import Debug.Trace


-- men: a, women: b
data RotationPoset a b = RotationPoset
  { _psManOptMatching :: Map b a
  , _psWomanOptMatching :: Map b a
  , _psRotations :: Bimap (Rotation b a) Int
  , _psCoveringRelation :: Map Int (Set Int)
  , _psMaxIndex :: Int -- ^increment after spitting it out (so it's 1 + `actual used max`)
  -- second: set of elems that cover index
  } deriving(Show, Read, Eq, Ord)
makeLenses 'RotationPoset

emptyPoset :: RotationPoset a b
emptyPoset = RotationPoset M.empty M.empty BM.empty M.empty 0

matchRotationsF :: (Show a, Show b, Ord a, Ord b)
  => MatchingInput a b -> (Map b a, Map b a, [Rotation a b])
matchRotationsF
