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
  let matchWalk = fmap fst $ mosmToWosmF prefs
  -- print matchWalk >> print ""
  let u = map (checkStable' prefs) matchWalk
  -- print u
  let wosm = invert $ mosmF (swapGenders prefs)
  -- print $ wosm == matchWalk !! (length matchWalk - 1)

  let lat = fullLattice prefs
  -- print lat
  return (prefs, lat)

-- an old bug caused this to be wrong.
-- I think the wrong women were being marked as ``reaching optimal'' in
--   the function iic.
latticeBreaksHere :: MatchingInput Int Char
latticeBreaksHere = MatchingInput
  { _menPrefs = M.fromList [(1,"abc"),(2,"cab"),(3,"bac")]
  , _womenPrefs = M.fromList [('a',[2,3,1]),('b',[2,1,3]),('c',[3,2,1])]
  }

irvingLowerBound :: Int -> MatchingInput Int Int
irvingLowerBound k = MatchingInput m w
  where mList = fmap (combobulate [1..2^k]) bitstrings
        combobulate elems [] = elems
        combobulate elems (a:as) =
          let (left, right) = halfs elems
           in case a of
                0 -> combobulate left as ++ combobulate right as
                1 -> combobulate right as ++ combobulate left as
                _ -> error "not a bitstring"
        bitstrings = nproduct k [0,1]
        wList = fmap reverse mList
        m = M.fromList $ zip [1..2^k] mList
        w = M.fromList $ zip [1..2^k] wList

-- Stable marriage: structure and algs Figure 2.1
mediumPosetEx :: MatchingInput Int Int
mediumPosetEx = MatchingInput
  { _menPrefs = M.fromList $ zip [1..8]
    [ [5,7,1,2,6,8,4,3]
    , [2,3,7,5,4,1,8,6]
    , [8,5,1,4,6,2,3,7]
    , [3,2,7,4,1,6,8,5]
    , [7,2,5,1,3,6,8,4]
    , [1,6,7,5,8,4,2,3]
    , [2,5,7,6,3,4,8,1]
    , [3,8,4,5,7,2,6,1]
    ]
  , _womenPrefs = M.fromList $ zip [1..8]
    [ [5,3,7,6,1,2,8,4]
    , [8,6,3,5,7,2,1,4]
    , [1,5,6,2,4,8,7,3]
    , [8,7,3,2,4,1,5,6]
    , [6,4,7,3,8,1,2,5]
    , [2,8,5,3,4,6,7,1]
    , [7,5,2,1,8,6,4,3]
    , [7,4,1,5,2,3,6,8]
    ]
  }

somewhatBigger :: MatchingInput Int Int
somewhatBigger = MatchingInput
  { _menPrefs = M.fromList
      [(1,[6,3,9,5,10,2,7,4,1,8])
      ,(2,[8,7,9,1,4,5,3,2,6,10])
      ,(3,[10,8,1,4,3,5,2,6,9,7])
      ,(4,[2,6,3,9,7,8,1,5,10,4])
      ,(5,[10,1,3,2,7,8,6,9,4,5])
      ,(6,[1,9,8,5,3,7,4,10,2,6])
      ,(7,[6,9,1,4,5,10,3,7,8,2])
      ,(8,[4,7,3,8,5,10,6,1,2,9])
      ]
  , _womenPrefs = M.fromList
      [(1,[3,7,2,10,4,1,6,5,8,9])
      ,(2,[9,3,1,5,2,4,7,6,8,10])
      ,(3,[5,3,2,4,9,10,8,7,1,6])
      ,(4,[3,9,10,4,1,6,5,2,8,7])
      ,(5,[7,3,1,5,9,10,6,8,4,2])
      ,(6,[8,5,2,7,10,3,1,6,4,9])
      ,(7,[6,1,3,8,2,4,5,7,10,9])
      ,(8,[8,10,6,3,7,1,4,2,5,9])
      ,(9,[5,7,4,1,6,3,2,9,8,10])
      ,(10,[9,10,4,1,2,5,8,7,3,6])
      ]
  }

hossyUnit :: MatchingInput Int Int
hossyUnit = MatchingInput
  { _menPrefs = M.fromList
      [(1,[16,1,15,2,10,8,7,6,18,11,5,3,12,13,9,4,17,20,14,19])
      ,(2,[10,15,2,4,12,20,7,8,3,1,14,17,9,11,16,18,5,19,6,13])
      ,(3,[1,20,9,7,15,11,3,17,12,19,6,10,14,2,18,8,4,5,13,16])
      ,(4,[10,12,20,15,17,4,1,18,7,14,19,16,9,3,5,8,6,2,13,11])
      ,(5,[4,17,6,1,13,3,5,19,11,8,10,7,2,20,15,14,9,12,16,18])
      ,(6,[1,18,11,14,5,4,13,16,17,19,2,10,7,3,8,20,9,12,6,15])
      ,(7,[10,11,4,16,3,5,7,2,14,17,6,19,18,15,1,8,9,12,13,20])
      ,(8,[13,6,1,14,5,16,2,8,18,17,20,3,7,19,15,9,4,11,12,10])
      ,(9,[16,11,4,9,6,1,2,15,8,3,14,19,13,20,12,10,18,5,7,17])
      ,(10,[5,4,14,6,11,17,10,15,3,18,1,13,7,2,20,12,19,9,8,16])
      ,(11,[3,2,12,13,11,1,7,18,17,4,9,10,19,16,14,5,8,20,6,15])
      ,(12,[12,9,1,5,6,19,20,7,8,13,11,18,3,17,4,14,16,10,15,2])
      ,(13,[19,2,14,11,10,7,5,18,1,20,13,16,12,3,15,4,8,17,6,9])
      ,(14,[19,17,7,8,9,20,11,4,18,10,13,14,16,15,12,5,2,1,6,3])
      ,(15,[13,4,10,9,5,16,11,15,3,2,19,6,12,1,7,17,8,18,20,14])
      ,(16,[15,5,19,13,12,9,17,18,16,14,1,8,20,7,6,10,3,4,11,2])
      ,(17,[18,12,11,1,5,8,15,13,17,20,4,3,16,14,2,19,9,6,7,10])
      ,(18,[18,1,3,14,6,8,2,7,15,9,4,11,20,19,5,17,13,16,10,12])
      ,(19,[3,10,7,8,12,16,18,15,13,6,11,20,9,19,14,17,2,1,4,5])
      ,(20,[20,15,6,18,3,14,19,1,5,8,17,11,12,2,7,4,13,9,16,10])
      ]
  , _womenPrefs = M.fromList
      [(1,[18,6,10,17,14,13,11,9,7,3,2,20,16,5,1,15,19,4,8,12])
      ,(2,[11,4,14,15,5,8,6,13,12,10,3,7,18,20,17,9,2,16,1,19])
      ,(3,[4,2,3,8,14,7,18,9,5,20,11,13,1,10,17,12,15,19,16,6])
      ,(4,[16,7,15,6,2,9,19,12,4,13,8,5,18,20,14,17,1,11,3,10])
      ,(5,[1,2,20,3,11,13,10,18,9,14,7,5,15,19,6,17,16,8,12,4])
      ,(6,[19,13,6,8,4,14,5,16,18,20,9,7,12,15,10,2,17,1,11,3])
      ,(7,[3,4,12,2,6,9,8,10,18,13,1,15,14,5,7,17,19,11,20,16])
      ,(8,[10,12,17,13,16,15,2,5,7,9,6,19,11,3,20,14,18,4,1,8])
      ,(9,[3,16,10,4,18,15,20,7,2,14,9,17,12,5,19,8,6,13,1,11])
      ,(10,[1,3,17,19,9,10,13,6,12,20,2,11,5,8,14,7,15,4,18,16])
      ,(11,[19,1,5,13,8,17,6,3,15,7,11,20,2,14,4,10,18,12,9,16])
      ,(12,[15,5,3,6,20,16,7,8,17,9,4,13,18,11,12,1,19,2,14,10])
      ,(13,[20,16,3,2,18,4,5,15,11,1,14,7,8,12,9,6,13,10,19,17])
      ,(14,[16,9,8,13,1,18,15,4,12,20,2,6,5,19,11,7,3,14,17,10])
      ,(15,[4,11,12,20,13,18,5,8,1,19,10,16,2,6,7,14,9,15,3,17])
      ,(16,[19,5,1,15,13,2,16,14,20,8,9,4,6,12,3,7,18,10,11,17])
      ,(17,[15,3,7,6,16,1,18,17,5,4,10,9,19,14,8,12,11,13,20,2])
      ,(18,[16,8,3,1,17,7,6,20,19,5,11,13,15,9,10,18,2,12,14,4])
      ,(19,[17,11,12,6,15,10,1,16,13,7,19,9,5,3,20,18,2,14,8,4])
      ,(20,[1,10,11,2,12,17,16,13,20,19,8,18,9,15,4,14,3,6,5,7])
      ]
  }
