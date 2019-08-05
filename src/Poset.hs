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
  , _psRotations :: Bimap (Rotation a b) Int
  , _psCoveringRelation :: Map Int (Set Int)
  , _psMaxIndex :: Int -- ^increment after spitting it out (so it's 1 + `actual used max`)
  -- second: set of elems that cover index
  } deriving(Show, Read, Eq, Ord)
makeLenses 'RotationPoset

emptyPoset :: RotationPoset a b
emptyPoset = RotationPoset M.empty M.empty BM.empty M.empty 0

matchRotations :: (Show a, Show b, Ord a, Ord b)
  => MatchingInput a b -> (Map b a, Map b a, [Rotation a b])
matchRotations prefs =
  let ((), st, wr) = runRWS mosmToWosm prefs (initialMatchingState prefs)
   in (view _1 $ head wr, view stableMatching st,
     drop 1 $ fmap (\(_,_,v) -> v) $ wr)
   -- NOTE: if you change the order stable matches are logged in, you'll break this.

data RotationLabel = Type1 | Type2
  deriving(Show, Eq, Ord)

type LabeledPrefs a b = Map a [(b, Maybe (RotationLabel, Int))]

womanSwaps :: Rotation a b -> [(b, (a,a))]
womanSwaps (Rotation rot)
  = (w, (m1,m2))
  : [ (b, (m1, m2)) | (m1,b):(m2,_):_ <- tails rot ]
  where (m1,w) = last rot
        (m2,_) = head rot

-- better than m1 and worse than m2 (strictly)
womansStrictInterval :: forall a b. (Ord a, Ord b)
  => MatchingInput a b -> b -> a -> a -> [a]
womansStrictInterval input w m1 m2 =
  let Just wPref = view (womenPrefs . at w) input
   in drop 1 $ dropWhile (/= m2) $ takeWhile (/= m1) $ wPref

buildLabeledPrefs :: forall a b. (Show a, Show b, Ord a, Ord b)
  => MatchingInput a b -> [Rotation a b]-> LabeledPrefs a b
buildLabeledPrefs prefs rotationsList =
  let nRot = length rotationsList
      indexedRotations = flip zip [0..nRot-1] $ rotationsList

      unlabeledPrefs = fmap (fmap (,Nothing)) . view menPrefs $ prefs
      labeledPrefs :: LabeledPrefs a b
      labeledPrefs = foldl labelRotation unlabeledPrefs indexedRotations

      labelRotation labPref (rot, rotIndex) =
        foldl (labelWomanRot rotIndex) labPref (womanSwaps rot)
      labelWomanRot :: Int -> LabeledPrefs a b
                    -> (b, (a,a)) -> LabeledPrefs a b
      labelWomanRot rotIndex lab (w,(m1,m2)) =
        foldl (addLabType Type2 rotIndex w)
          (addLabType Type1 rotIndex w lab m1)
          (womansStrictInterval prefs w m1 m2)


      addLabType :: RotationLabel -> Int -> b -> LabeledPrefs a b -> a -> LabeledPrefs a b
      addLabType labType rotIndex w labeledPrefs m =
        over (at m) (fmap . fmap $ setIfW) labeledPrefs
        where setIfW (w', prev)
                | w == w' = (w', Just (labType, rotIndex))
                | otherwise = (w', prev)
   in labeledPrefs


buildRotationPoset :: forall a b. (Show a, Show b, Ord a, Ord b)
  => MatchingInput a b -> RotationPoset a b
buildRotationPoset prefs =
   let (manOpt, womanOpt, rotationsList) = matchRotations prefs
       indexedRotations = flip zip [0..] $ rotationsList
       labeledPrefs = buildLabeledPrefs prefs rotationsList
       rotationsCovering = undefined
    in RotationPoset manOpt womanOpt (BM.fromList indexedRotations)
         rotationsCovering (length rotationsList)

