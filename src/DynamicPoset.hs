{-# LANGUAGE FlexibleContexts, ConstraintKinds, TemplateHaskell,
  TupleSections, TypeFamilies, ScopedTypeVariables, LambdaCase #-}
module DynamicPoset where

import qualified Data.Bimap as BM
import Data.Bimap (Bimap)
import Data.Set (Set)
import Data.Tuple
import qualified Data.Set as S
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Control.Lens
import Data.Set.Lens
import Data.List
import Data.Maybe
import Data.Function
import Control.Monad.RWS
import Control.Monad

import Utils

import Debug.Trace

instance (Ord a, Ord b, Read a, Read b) => Read (Bimap a b) where
  readsPrec _ str = [(BM.fromList . read $ str, "")]

-- read as: ... (a1,b1), (a2,b2),... ==>
--   man a1 goes from b1 to b2. This holds cyclically.
newtype Rotation a b = Rotation { _getRotation :: [(a,b)] }
  deriving(Show, Read, Eq, Ord)
makeLenses 'Rotation

-- canonicalize rotations by putting the smallest-indexed man first.
makeRotation :: (Ord b, Ord a) => [(a,b)] -> Rotation a b
makeRotation [] = Rotation []
makeRotation rot = Rotation .  uncurry (++) . swap
  . minimumBy (compare `on` fst . head . snd) . init . splits $ rot

data MatchingInput a b = MatchingInput
  { _menPrefs :: Map a [b]
  , _womenPrefs :: Map b [a]
  } deriving(Show, Read, Eq, Ord)
makeLenses 'MatchingInput

data RotationPoset a b = RotationPoset
  { _psManOptMatching :: Map b a
  , _psWomanOptMatching :: Map b a
  , _psRotations :: Bimap (Rotation a b) Int
  , _psPredecessors :: Map Int (Set Int, Set Int) -- ^ T1 and T2
  , _psCoveringRelation :: Map Int (Set Int)
  , _psMaxIndex :: Int -- ^increment after spitting it out (so it's 1 + `actual used max`)
  -- second: set of elems that cover index
  } deriving(Show, Read, Eq, Ord)
makeLenses 'RotationPoset

emptyRotationPoset :: RotationPoset a b
emptyRotationPoset = RotationPoset M.empty M.empty BM.empty M.empty M.empty 0

insertNew :: (Ord a, Ord b) => Rotation a b -> RotationPoset a b -> RotationPoset a b
insertNew rot poset =
  let newRots = BM.insert rot (poset ^. psMaxIndex) (poset ^. psRotations)
   in poset & psMaxIndex +~ 1 & psRotations .~ newRots

--------------------------------------------------------------------------------
-- Monad
--------------------------------------------------------------------------------

data MatchingState a b = MatchingState
  { _womenAtTopMatch :: Set b -- ^ unused during MPDA
  , _improvingWomen :: Set b -- ^ unused during MPDA
  -- after mpda, set of women is (disj) union of womenAtTop,
  --  improvingWomen, {notMember stableMatching}
  , _proposalsRecieved :: Map b Int

  , _floatingMan :: Maybe a -- ^ unused during MPDA
  , _rejectionStack :: [(a,b,Maybe Int,[Int])] -- ^ unused during MPDA
    -- ^ [ (m, w, [rotation bringing m where he is],
    --      [rotations which would've been triggered in the proccess of m_(i-1)
    --      going from w_(i-1) to w_i] ) ]

  , _rotationsFound :: RotationPoset a b
  , _rotationsMovingMan :: Map a Int -- ^ unused during MPDA
    -- ^ stores the most recent rotation that moved m.
  , _rotationLabeledWomenPrefs :: Map b [(a, Maybe Int)]
    -- if a rotation moved a woman from below to above some man on her list,
    --   write that here.

  , _singleProposingMen :: Set a -- ^ unused during convert to WOSM
  , _singleUnmatchedMen :: Set a -- ^ unused during convert to WOSM
  , _menProposalStatus :: Map a ([b], Set b)
  -- First element: remaining proposals; second: women already proposed to
  --
  --  Another funny thing: after a terminal phase rejection chain, there is
  --    ``one too many'' element in rejected set (the worst stable partner)

  , _stableMatching :: Map b a
  , _experimentalMatching :: Map b a -- ^ unused during MPDA
  } deriving(Show, Read, Eq, Ord)
makeLenses 'MatchingState

initialMatchingState :: (Ord a, Ord b) => MatchingInput a b -> MatchingState a b
initialMatchingState (MatchingInput menPrefs womenPrefs) =
  MatchingState S.empty S.empty (fmap (const 0) womenPrefs)
    Nothing [] emptyRotationPoset
    M.empty (fmap (fmap (,Nothing)) womenPrefs)
    men S.empty (fmap (,S.empty) menPrefs) M.empty M.empty
  where women = M.keysSet womenPrefs
        men = M.keysSet menPrefs

swapGenders :: MatchingInput a b -> MatchingInput b a
swapGenders (MatchingInput u v) = MatchingInput v u

type MatchingMonad m a b
  = (Show a, Show b, Ord a, Ord b,
    MonadState (MatchingState a b) m,
    MonadReader (MatchingInput a b) m)
    -- MonadWriter [(Map b a, [b], Rotation a b)] m)
    -- the writer instance holds the stable matches, and also
    -- the volatile women when the match was found. Admitedly, this is hacky
    -- and just because I want those volatile women for a very specific reason.
    -- TODO: use a different writer type to avoid quadratic time appends.

--------------------------------------------------------------------------------
-- Algorithm as in the paper
--------------------------------------------------------------------------------

findRotationsF :: forall a b. (Show a, Ord a, Show b, Ord b) =>
               MatchingInput a b -> RotationPoset a b
findRotationsF prefs = view rotationsFound . view _2
  $ (runRWS findRotations prefs (initialMatchingState prefs)
    :: ((), MatchingState a b, ()))

stateF :: forall a b. (Show a, Ord a, Show b, Ord b) =>
               MatchingInput a b -> MatchingState a b
stateF prefs = view _2
  $ (runRWS findRotations prefs (initialMatchingState prefs)
    :: ((), MatchingState a b, ()))

-- builds up stableMatching, while keeping proposalsRecieved,
--   singleUnmatchedMen, menProposingStatus, updated and other fields empty
mpda :: MatchingMonad m a b => m ()
mpda = do
  whileM_ (not . S.null <$> use singleProposingMen) $ do
    man <- S.findMin <$> use singleProposingMen
    singleProposingMen %= S.delete man

    (topWomen, remainingWomen) <- use $ menProposalStatus . ix man
    (acceptingWoman, _) <- manProposesDownList man topWomen

    case acceptingWoman of
      Just woman -> womanUpgradesSimple woman man
      Nothing -> singleUnmatchedMen %= S.insert man

-- In this function, every woman in topWomen rejectin man will be added
-- to man's rejection list and removed from his preference list.
manProposesDownList :: MatchingMonad m a b => a -> [b] -> m (Maybe b, [Int])
manProposesDownList man topWomen = do
    (rejectingWomen, coveredRho) <- takeAccumWhileM topWomen []
      $ \woman covRho -> do
        traceM $ "man " ++ show man ++ " prop to " ++ show woman
        (accepts, rhoI) <- acceptProposal woman man
        proposalsRecieved . ix woman += 1
        return $ (not accepts, maybeToList rhoI ++ covRho)

    menProposalStatus . ix man . _2
      %= S.union (S.fromList rejectingWomen)
      -- current woman rejects also.
    let topWomen' = dropWhile (`elem` rejectingWomen) topWomen
      -- ^ obvious inefficiency case here
    menProposalStatus . ix man . _1 .= topWomen'
      -- ^ this makes the current match ON his list.
    return (listToMaybe topWomen', coveredRho)

-- if either member doesn't rank the other, they will never match.
-- return a rotation label if that rotation moved w from BELOW to ABOVE m.
acceptProposal :: MatchingMonad m a b => b -> a -> m (Bool, Maybe Int)
acceptProposal woman man = do
  match <- use $ stableMatching . at woman
  womanLabeledPref :: [(b, Maybe Int)] <- use (rotationLabeledWomenPrefs . ix woman)
  let womanPref = fmap fst womanLabeledPref
      beforeIsh Nothing = man `elem` womanPref
      beforeIsh (Just oldMatch) = man `elem` takeWhile (/=oldMatch) womanPref
      movedLabel = join . fmap snd . find ((==man).fst) $ womanLabeledPref
  return $ (beforeIsh match, movedLabel)

  -- ^^ TODO for poset predecessors:
  --  1) here, change this to doing a lookup in _rotationLabeledWomenPrefs
  --      instead of the reader monad
  --  2) elsewhere, make sure you actually make rotation labels


womanUpgradesSimple :: MatchingMonad m a b => b -> a -> m ()
womanUpgradesSimple woman man = do
  oldMatch <- use $ stableMatching . at woman
  case oldMatch of
    Nothing -> return ()
    Just m -> do
      singleProposingMen %= S.insert m
      menProposalStatus . ix m . _2 %= S.insert woman
      menProposalStatus . ix m . _1 %= drop 1
      -- here was the problem
      -- WAIT maybe this isn't correct for the later parts...
  stableMatching . at woman .= Just man


findRotations :: MatchingMonad m a b => m ()
findRotations = do
  mpda
  manOpt <- use stableMatching
  -- traceShowM manOpt
  rotationsFound . psManOptMatching .= manOpt

  -- initMosmToWosm
  matchedWomen <- setOf (stableMatching . keysF) <$> get
  improvingWomen .= matchedWomen
  allWomen <- setOf (womenPrefs . keysF) <$> ask
  womenAtTopMatch .= allWomen `S.difference` matchedWomen

  whileM_ (not . null <$> use improvingWomen) $ do
    (experimentalMatching .=) =<< use stableMatching

    womanZero <- S.findMin <$> use improvingWomen
    startNewDivorceChain womanZero

    terminalPhaseCleanup

  womanOpt <- use stableMatching
  rotationsFound . psWomanOptMatching .= womanOpt

getVolatileWomen :: MatchingMonad m a b => m [b]
getVolatileWomen = fmap (view _2) <$> use rejectionStack

terminalPhaseCleanup :: MatchingMonad m a b => m ()
terminalPhaseCleanup = do
  (experimentalMatching .=) =<< use stableMatching
  vol <- getVolatileWomen
  -- change this to work with rejection stack
  womenAtTopMatch %= \s -> foldr S.insert s vol
  improvingWomen %= \s -> foldr S.delete s vol

startNewDivorceChain :: MatchingMonad m a b => b -> m ()
startNewDivorceChain womanZero = do
  manZero <- use $ experimentalMatching . at womanZero
  floatingMan .= manZero -- ^ already wrapped in Just
  experimentalMatching . at womanZero .= Nothing

  manZeroRhoCov <- use $ rotationsMovingMan . at (fromJust manZero)
  rejectionStack .= [(fromJust manZero, womanZero, manZeroRhoCov, [])]
  -- subtle thing: manZero will re-propose to womanZero. This is okay though
  -- (as he's not better than himself) and other men DO need to re-propose sometimes.

  whileM_ (not . null <$> use floatingMan) $ do
    man <- fromJust <$> use floatingMan -- won't break (loop cond)

    (topWomen, remainingWomen) <- use $ menProposalStatus . ix man
    (acceptingWoman, coveredRho) <- manProposesDownList man topWomen

    case acceptingWoman of
      Nothing -> do -- This case doesn't happen if |W| > |M|
        floatingMan .= Nothing
      Just woman -> do
        womanUpgradesConvert woman man coveredRho


womanUpgradesConvert :: MatchingMonad m a b => b -> a -> [Int] -> m ()
womanUpgradesConvert woman man coveredRho = do
  (stabWomen, mu) <- (,) <$> use womenAtTopMatch <*> use stableMatching
  if woman `elem` stabWomen || woman `M.notMember` mu
    then do
      -- maybe for consistency I should add (m,w) to rejection stack? idk
      floatingMan .= Nothing -- trigger terminalPhaseCleanup

  else do
    -- I know this is confusing, but this is the man to label
    rejectionStack . _head . _4 %= (coveredRho ++)

    oldMatch <- use $ experimentalMatching . at woman
    floatingMan .= oldMatch -- ^ Nothing iff woman == womanZero, as we want it!

    -- traceM $ "setting match of " ++ show woman ++ " to " ++ show man
    experimentalMatching . at woman .= Just man

    vol <- getVolatileWomen
    -- traceShowM vol

    if woman `elem` vol
      then do -- ^ new stable match found (simple improvement cycle)
        improvementCyclePhase woman man coveredRho

      else do -- continue trying to upgrade
        let rejectedMan = fromMaybe (error "should have old man if woman not volatile")
              oldMatch
        rejectedManCovered <- use $ rotationsMovingMan . at rejectedMan
        rejectionStack %= ((rejectedMan, woman, rejectedManCovered, []) :)

improvementCyclePhase :: MatchingMonad m a b => b -> a -> [Int] -> m ()
improvementCyclePhase woman man coveredRho = do
  rejStack <- use rejectionStack
  let adjust (as, b:bs) = (as++[b], bs)
      adjust _ = error "not possible as woman `elem` vol"
      (rejImproved, rejRemaining) = adjust $ span ((/= woman) . view _2) rejStack

  -- traceM $ "improved ,rem " ++ show (rejImproved, rejRemaining)

  let improvedWomen = fmap (view _2) rejImproved
  stab <- use stableMatching
  expImp <- M.filterWithKey (\k _ -> k `elem` improvedWomen)
    <$> use experimentalMatching
  stableMatching .= expImp `M.union` stab -- left-biased, i.e. overwrite stab.

  -- traceShowM =<< use stableMatching

  rejectionStack .= rejRemaining

  insertImprovedRotation rejImproved coveredRho

womanSwaps :: Rotation a b -> [(b, (a,a))]
womanSwaps (Rotation rot)
  = (w, (m1,m2))
  : [ (b, (m1, m2)) | (m2,_):(m1,b):_ <- tails rot ]
  where (m1,w) = head rot
        (m2,_) = last rot

insertImprovedRotation :: MatchingMonad m a b
  => [(a,b,Maybe Int, [Int])] -> [Int] -> m ()
insertImprovedRotation rejImproved lastWomanCovs = do
  -- make the corresponding rotation
  let pairsImproved = fmap (\(u,v,_,_) -> (u,v)) rejImproved
      rhoFound = makeRotation $ reverse pairsImproved
  rotationsFound %= insertNew rhoFound
  rhoFoundIndex <- (subtract 1) <$> use (rotationsFound . psMaxIndex)

  traceM $ "improved like " ++ show rejImproved ++ " also " ++ show lastWomanCovs
  traceShowM =<< use rotationsMovingMan
  traceShowM =<< use rotationLabeledWomenPrefs
  traceShowM =<< use stableMatching


  let accum = foldl
        (\(s1, s2) (m,w, mCov, wCov) ->
          (maybe id S.insert mCov $ s1, s2 `S.union` S.fromList wCov))
        (S.empty, S.empty) rejImproved
  rotationsFound . psPredecessors . at rhoFoundIndex .= Just accum

  forM_ rejImproved $ \(m,w,_,_) -> do
    rotationsMovingMan . at m .= Just rhoFoundIndex

  forM_ (womanSwaps rhoFound) $ \(w, (m1, m2)) -> do
    -- if m is after m2 but before m1 in this list, label.
    rotationLabeledWomenPrefs . ix w %=
      betweenPredicatesMap ((==m2).fst) ((==m1).fst) (\case
          (m,Nothing) -> (m,Just rhoFoundIndex)
          (m,Just _) -> error "I think this labeling should happen at most once.."
        )



-- important: this example doesn't really featur any rejections at all
-- except by women seeking to improve their stable match.
smallPosetEx :: MatchingInput Int Int
smallPosetEx = MatchingInput
  { _menPrefs = M.fromList $ zip [1..]
    [ [1,2,3]
    , [2,1,3]
    , [3,5,1]
    , [4,3,5]
    , [5,4]
    ]
  , _womenPrefs = M.fromList $ zip [1..]
    [ [3,2,1]
    , [1,2]
    , [2,4,1,3]
    , [5,4]
    , [4,3,5]
    ]
  }

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

-- parens: extra
reapplyCascadeEx :: MatchingInput Int Int
reapplyCascadeEx = MatchingInput
  { _menPrefs = M.fromList $ zip [1..5]
    [ [1,2,(4),5]
    , [(4),2,3]
    , [(2),(1),3,4]
    , [4,2,5]
    , [(4),5,1]
    ]
  , _womenPrefs = M.fromList $ zip [1..5]
    [ [5,1,(3)]
    , [1,4,2]
    , [(2),1,4,(3)]
    , [3,(1),4,(2),(5)]
    , [4,(2),(3),5]
    ]
  }

queryBumpedWomenEx :: MatchingInput Int Int
queryBumpedWomenEx = MatchingInput
  { _menPrefs = M.fromList $ zip [1..5]
    [ [1,2,(4),5]
    , [(4),2,3]
    , [(2),(1),3,4]
    , [4,2,5]
    , [(4),5,1]
    ]
  , _womenPrefs = M.fromList $ zip [1..5]
    [ [5,1,(3)]
    , [4,1,2]
    , [(2),1,4,(3)]
    , [3,(1),4,(2),(5)]
    , [1,4,(2),(3),5]
    ]
  }

