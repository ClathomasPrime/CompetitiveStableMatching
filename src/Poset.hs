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

data RotationLabel = Type1Start | Type1End | Type2
  deriving(Show, Eq, Ord)
type RotationIndex = Int

type LabeledPrefs a b = Map a [(b, [(RotationLabel, RotationIndex)])]

-- woman_i goes from man_i to man_(i-1) mod r. => (w_i, (m_i, m_(i-1)))
womanSwaps :: Rotation a b -> [(b, (a,a))]
womanSwaps (Rotation rot)
  = (w, (m1,m2))
  : [ (b, (m1, m2)) | (m2,_):(m1,b):_ <- tails rot ]
  where (m1,w) = head rot
        (m2,_) = last rot

-- man_i goes from woman_i to woman_(i+1) mod r. => (m_i, (w_i, w_(i+1)))
manSwaps :: Rotation a b -> [(a, (b,b))]
manSwaps (Rotation rot)
  = (m, (w1,w2))
  : [ (m, (w1, w2)) | (m,w1):(_,w2):_ <- tails rot ]
  where (m,w1) = last rot
        (_,w2) = head rot

-- better than m1 and worse than m2 (strictly)
womansStrictInterval :: forall a b. (Ord a, Ord b)
  => MatchingInput a b -> b -> a -> a -> [a]
womansStrictInterval input w m1 m2 =
  let Just wPref = view (womenPrefs . at w) input
   in drop 1 $ dropWhile (/= m2) $ takeWhile (/= m1) $ wPref

-- NOTE: I think I'll have no real garuntee that this will work until I
-- understand the possibility of multiple labels in a single cell.
buildLabeledPrefs :: forall a b. (Show a, Show b, Ord a, Ord b)
  => MatchingInput a b -> [Rotation a b]-> LabeledPrefs a b
buildLabeledPrefs prefs rotationsList =
  let nRot = length rotationsList
      indexedRotations = flip zip [0..nRot-1] $ rotationsList

      unlabeledPrefs = fmap (fmap (,[])) . view menPrefs $ prefs
      labeledPrefs :: LabeledPrefs a b
      labeledPrefs = foldl labelRotation unlabeledPrefs indexedRotations

      labelRotation labPref (rot, rotIndex) =
        foldl (labelManRot rotIndex)
          (foldl (labelWomanRot rotIndex) labPref (womanSwaps rot))
          (manSwaps rot)
      labelWomanRot :: RotationIndex -> LabeledPrefs a b
                    -> (b, (a,a)) -> LabeledPrefs a b
      labelWomanRot rotIndex lab (w,(m1,m2)) =
        foldl (addLabType Type2 rotIndex w)
          lab (womansStrictInterval prefs w m1 m2)
      -- subtle thing: you need the earlier end points to come after
      -- the later start points in these lists, because that case is okay and
      -- we should draw that edge.
      labelManRot :: RotationIndex -> LabeledPrefs a b
                    -> (a, (b,b)) -> LabeledPrefs a b
      labelManRot rotIndex lab (man, (w1, w2)) =
          addLabType Type1Start rotIndex w1
            (addLabType Type1End rotIndex w2 lab man) man

      addLabType :: RotationLabel -> RotationIndex -> b
        -> LabeledPrefs a b -> a -> LabeledPrefs a b
      addLabType labType rotIndex w labeledPrefs m =
        over (at m) (fmap . fmap $ setIfW) labeledPrefs
        where setIfW (w', prev)
                | w == w' = (w', (labType, rotIndex):prev)
                | otherwise = (w', prev)
   in labeledPrefs

type RI = RotationIndex

buildRotationPoset :: forall a b. (Show a, Show b, Ord a, Ord b)
  => MatchingInput a b -> RotationPoset a b
buildRotationPoset prefs =
   let (manOpt, womanOpt, rotationsList) = matchRotations prefs
       nRot = length rotationsList
       indexedRotations = flip zip [0..nRot-1] $ rotationsList
       labeledPrefs = buildLabeledPrefs prefs rotationsList

       emptyCovMap = M.fromList $ zip [0..nRot-1] (repeat S.empty)
       rotationsCovering = M.foldlWithKey
         (\covRel man labPref
            -> view _1 $ foldl (accum man) (covRel,Nothing, S.empty)
              (concatMap (\(w,labs) -> fmap (w,) labs) labPref))
         emptyCovMap labeledPrefs
       accum :: a -> (Map RI (Set RI), Maybe RI, Set RI) ->
         (b, (RotationLabel, RI)) -> (Map RI (Set RI), Maybe RI, Set RI)
       accum man (covMap, prev, prevSeen) (woman, (Type1Start, rho))
         = (maybe covMap (\rhoPrev -> insertEdge rhoPrev rho covMap) prev,
            Just rho, rho `S.insert` prevSeen)
       accum man (covMap, prev, prevSeen) (woman, (Type1End, rho))
         | Just rho == prev = (covMap, Nothing, prevSeen)
         | otherwise = (covMap, prev, prevSeen)
       accum man (covMap, prev, prevSeen) (woman, (Type2, rho))
         | rho `S.member` prevSeen = (covMap, prev, prevSeen)
         | otherwise =
           (maybe covMap (\rhoPrev -> insertEdge rho rhoPrev covMap) prev,
            -- ^ this should never fail... maybe change accordingly?
            prev, rho `S.insert` prevSeen)

    in RotationPoset manOpt womanOpt (BM.fromList indexedRotations)
         rotationsCovering (length rotationsList)

insertEdge :: RI -> RI -> Map RI (Set RI) -> Map RI (Set RI)
insertEdge base target covMap =
  over (ix base) (S.insert target) covMap

posetBreaksExample :: MatchingInput Int Int
posetBreaksExample = MatchingInput
  ( M.fromList
    [ (1, [1,2,3])
    , (2, [2,1,3])
    , (3, [3,5,1])
    , (4, [4,3,5])
    , (5, [5,4])
    ] )
  ( M.fromList
    [ (1, [3,2,1])
    , (2, [1,2])
    , (3, [2,4,1,3])
    , (4, [5,4])
    , (5, [4,3,5])
    ] )
