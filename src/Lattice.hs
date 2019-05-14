{-# LANGUAGE FlexibleContexts, ConstraintKinds, TemplateHaskell,
  TupleSections, TypeFamilies, ScopedTypeVariables #-}
module Lattice where

import qualified Data.Bimap as BM
import Data.Bimap (Bimap)
import Data.Set (Set)
import qualified Data.Set as S
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Control.Lens
import Data.List
import Data.Maybe

import Convert
import RandUtils
import Utils

import Debug.Trace

type LatticeFrontier b = Map Int (Set b)

  -- , _matchingFrontier :: Set (Int, [b]) -- ^ only used for full lattice
  -- , _matchingLattice :: MatchingLattice a b -- ^ only used for full lattice
data MatchingLattice a b = MatchingLattice
  { _matchingsFound :: Bimap (Map b a) Int
  , _coveringRelation :: Map Int (Set Int)
  , _maxIndex :: Int -- ^increment after spitting it out (so it's 1 + `actual used max`)
  -- second: set of elems that cover index
  } deriving(Show, Eq, Ord)
makeLenses 'MatchingLattice


fullLattice :: (Ord a, Ord b, Show a, Show b) =>
  MatchingInput a b -> MatchingLattice a b
fullLattice input
  = fst $ until (null . snd) (uncurry $ fullLatticeFrontier input) initial
  where initial = (lattice , M.fromList [(0, S.empty)])
        lattice = MatchingLattice (BM.fromList [(mosm, 0)]) M.empty 1
        mosm = mosmF input

fullLatticeFrontier :: (Ord a, Ord b, Show a, Show b) =>
  MatchingInput a b -> MatchingLattice a b -> LatticeFrontier b
  -> (MatchingLattice a b, LatticeFrontier b)
fullLatticeFrontier input lattice frontier
  = M.foldlWithKey step (lattice, M.empty) frontier
  where step (lattice, nextFrontier) baseI womenAtTop
          = let (succs, womenAtTop')
                  = successors input (findMatch baseI lattice) womenAtTop
                iter mu' = insertAdjustMatchPair baseI mu' womenAtTop'
             in foldr iter (lattice, nextFrontier) succs

successors :: forall a b. (Ord a, Ord b, Show a, Show b) =>
  MatchingInput a b -> Map b a -> Set b -> ([Map b a], Set b)
successors input muZero womenAtTopMatch
  = foldl accum ([], S.empty) $ unfoldr iter (allWomen S.\\ womenAtTopMatch)
  where allWomen = M.keysSet $ view womenPrefs input
        accum (matches, ws) (Left match) = (match:matches, ws)
        accum (matches, ws) (Right ws') = (matches, ws `S.union` ws')
        -- While accumuating the set of women that can (attomically) improve here,
        -- Either generate new matches or sets of women at top match
        iter :: Set b -> Maybe (Either (Map b a) (Set b), Set b)
        iter s
          | Nothing <- S.lookupMin $ s = Nothing
          | Just w <- S.lookupMin $ s
            = let (newMatchMaybe, ws) = iic input muZero w womenAtTopMatch
                  newConsideredSet = s S.\\ S.fromList (w:ws)
               in case newMatchMaybe of
                    Nothing -> Just $ (Right $ S.fromList ws, newConsideredSet)
                    Just newMatch -> Just $ (Left newMatch, newConsideredSet)
 -- NOTE: IF newMatchMaybe == Nothing, you
 -- know that all those ws have reached their best stable match,
 -- so you could store this information and optimize further up the lattice.

findMatch :: (Ord a, Ord b) => Int -> MatchingLattice a b -> Map b a
findMatch index lattice = fromJust $ BM.lookupR index (lattice^.matchingsFound)

insertAdjustMatchPair :: (Show a, Show b, Ord a, Ord b) => Int -> Map b a -> Set b ->
  (MatchingLattice a b, LatticeFrontier b) -> (MatchingLattice a b, LatticeFrontier b)
insertAdjustMatchPair baseIndex mu womenAtTop (lattice, frontier)
  = (lattice'', frontier')
  where (muIndex, lattice') = insertOrFind lattice mu
        frontier'
          = if muIndex == lattice^.maxIndex || muIndex `M.member` frontier
              then M.insertWith S.union muIndex womenAtTop frontier
              -- ^ mu' goes into frontier if he's new; union womenAtTop if already there
              else frontier -- ^ otherwise he's already been _considered_ in frontier
        lattice'' = lattice' & coveringRelation
          %~ M.insertWith S.union baseIndex (S.singleton muIndex)

insertOrFind :: (Ord a, Ord b) =>
  MatchingLattice a b -> Map b a -> (Int, MatchingLattice a b)
insertOrFind lattice mu
  = case BM.lookup mu (lattice^.matchingsFound) of
      Just i -> (i, lattice)
      Nothing ->
        let ind = lattice^.maxIndex
            lattice' = lattice & maxIndex +~ 1
              & matchingsFound %~ BM.insert mu ind
         in (ind, lattice')


testCase :: IO (MatchingInput Int Char, MatchingLattice Int Char)
testCase = maximizer (view $ _2 . maxIndex) 20 $ do
  prefs <- unbalancedAlphaMarket 10 10
  -- print prefs
  -- print ""
  let matchWalk = mosmToWosmF prefs
  -- print matchWalk >> print ""
  let u = map (checkStable' prefs) matchWalk
  -- print u
  let wosm = invert $ mosmF (swapGenders prefs)
  -- print $ wosm == matchWalk !! (length matchWalk - 1)

  let lat = fullLattice prefs
  -- print lat
  return (prefs, lat)

latticeBreaksHere :: MatchingInput Int Char
latticeBreaksHere = MatchingInput
  { _menPrefs = M.fromList [(1,"abc"),(2,"cab"),(3,"bac")]
  , _womenPrefs = M.fromList [('a',[2,3,1]),('b',[2,1,3]),('c',[3,2,1])]
  }

