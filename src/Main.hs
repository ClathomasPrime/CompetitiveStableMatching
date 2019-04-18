module Main where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Control.Lens
import Data.Maybe

import Utils

main :: IO ()
main = do
  putStrLn "hello world"

avgRanksManOpt :: (Floating n, Ord a, Ord b)
  => Map a [b] -> Map b [a] -> (n, n)
avgRanksManOpt men women =
  avgRanks men women (menOptimal men women)

avgRanks :: (Floating n, Ord a, Ord b)
  => Map a [b] -> Map b [a] -> Map b a -> (n, n)
avgRanks men women match =
  over both (avg . fmap fromIntegral) (ranks men women match)

-- in the MAN OPTIMAL matching
ranks :: (Num n, Ord a, Ord b)
  => Map a [b] -> Map b [a] -> Map b a -> ([n], [n])
ranks men women match =
  let menOptimalMatch = menOptimal men women -- ^ woman-indexed
      womenRanks = M.mapWithKey (prefIndexOf women) menOptimalMatch
      menOptimalMatch' = invert menOptimalMatch -- ^ man-indexed
      menRanks = M.mapWithKey (prefIndexOf men) menOptimalMatch'
      convt = fmap snd . M.toList
   in (convt menRanks, convt womenRanks)

-- same number in *all* stable outcomes, because (math)
numUnmatchedInStable :: (Ord a, Ord b, Num n)
  => Map a [b] -> Map b [a] -> (n, n)
numUnmatchedInStable men women =
  let menOptimalMatch = menOptimal men women -- ^ woman-indexed
      womenUnmatched = M.size $ women `M.difference` menOptimalMatch
      menOptimalMatch' = invert menOptimalMatch -- ^ man-indexed
      menUnmatched = M.size $ men `M.difference` menOptimalMatch'
   in (fromIntegral menUnmatched, fromIntegral womenUnmatched)

-- among all stable matchings
numNonfixed :: (Ord a, Ord b) => Map a [b] -> Map b [a] -> Int
numNonfixed men women =
  let menOptimalMatch = menOptimal men women -- ^ woman-indexed
      menOptimalMatch' = invert menOptimalMatch -- ^ man-indexed
      womenOptimalMatch = menOptimal women men -- ^ man-indexed
      -- womenOptimalMatch' = invert womenOptimalMatch -- ^ woman-indexed
      diffIndexer m1 m2 = M.size $ M.filterWithKey
        (\m w -> Just w /= M.lookup m m2) m1
   in diffIndexer menOptimalMatch' womenOptimalMatch
        -- diffIndexer womenOptimalMatch' menOptimalMatch)
      -- Note: by rural hospital, same men matched/unmatched in either case.


--------------------------------------------------------------------------------

menOptimal :: (Ord a, Ord b) => Map a [b] -> Map b [a] -> Map b a
menOptimal men women =
  let init = (M.empty, men, M.keys men)
   in view _1 $ until (null . view _3) (proposeRound women) init

proposeRound :: (Ord a, Ord b)
  => Map b [a] -> (Map b a, Map a [b], [a]) -> (Map b a, Map a [b], [a])
proposeRound women (partialMatch, remainingMenProposals, freeMen)
  = foldl (proposeMan women) (partialMatch, remainingMenProposals, []) freeMen

proposeMan :: (Ord a, Ord b)
  => Map b [a] -> (Map b a, Map a [b], [a]) -> a -> (Map b a, Map a [b], [a])
proposeMan womenPrefs (partialMatch, remainingMenProposals, newFreeMen) man =
  case remainingMenProposals ^. at man of
    Nothing -> error "man not found in map"
    Just [] -> (partialMatch, remainingMenProposals, newFreeMen)
      -- ^ Man has ran down his pref list. He'll be unmatched
    Just (nextChoice:restChoice) ->
      let proposals' = remainingMenProposals & at man .~ Just restChoice
          (partialMatch', rejectedMan)
            = womanUpgrades nextChoice womenPrefs partialMatch man
       in (partialMatch', proposals', maybeToList rejectedMan ++ newFreeMen)

womanUpgrades :: (Ord a, Ord b)
  => b -> Map b [a] -> Map b a -> a -> (Map b a, Maybe a)
  -- Return: (updatedMap, rejectedMan (if present))
womanUpgrades woman womenPrefs partialMatch proposingMan =
  let Just womanPref = womenPrefs ^. at woman
      preferedTo x y = x `elem` takeWhile (/= y) womanPref
   in case partialMatch ^. at woman of
        Nothing -> -- woman not yet proposed to
          if proposingMan `elem` womanPref
             then (partialMatch & at woman .~ Just proposingMan, Nothing)
             else (partialMatch, Just proposingMan)
        Just previousMan ->
          if proposingMan `preferedTo` previousMan
             then (partialMatch & at woman .~ Just proposingMan, Just previousMan)
             else (partialMatch, Just proposingMan)
        -- note: could combine these branches like with ``rankedAbove'' in
        -- checkStable... but this is more clear anyway


--------------------------------------------------------------------------------

checkStable :: (Ord a, Ord b) => Map a [b] -> Map b [a] -> Map b a -> Bool
checkStable men women matchingWI
  = all nonblocking $ (,) <$> M.keys men <*> M.keys women
  where matchingMI = invert matchingWI

        rankedAbove as Nothing = as
        rankedAbove as (Just b) = takeWhile (/= b) as
        -- ^ somewhat trick way to define this

        nonblocking (a,b) =
          let matchA = M.lookup a matchingMI
              Just aList = men ^. at a
              prefA my x = x `notElem` rankedAbove aList my

              matchB = M.lookup b matchingWI
              Just bList = women ^. at b
              prefB my x = x `notElem` rankedAbove bList my

           in (matchA == Just b) || (matchA `prefA` b) || (matchB `prefB` a)

--------------------------------------------------------------------------------

strategicCase :: (Map Int [Char], Map Char [Int])
strategicCase =
  ( M.fromList
    [ (1, "abc")
    , (2, "bac")
    , (3, "bac")
    ]
  , M.fromList
    [ ('a', [2,1,3])
    , ('b', [1,2,3])
    , ('c', [1,2,3])
    ]
  )
