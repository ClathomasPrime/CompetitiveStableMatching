{-# LANGUAGE FlexibleContexts, ConstraintKinds, TemplateHaskell,
  TupleSections, TypeFamilies #-}
module Convert where

import qualified Data.Bimap as BM
import Data.Bimap (Bimap)
import Data.Set (Set)
import qualified Data.Set as S
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Control.Monad.Random
import Control.Lens
import Data.Set.Lens
import Data.Maybe
import Control.Monad.RWS
import Data.Function
import Data.Tuple
import Data.List

import Utils
import Main
import Rand

import Debug.Trace


--------------------------------------------------------------------------------
-- Rotation (out of order... refactor eventually
--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------
-- Monad
--------------------------------------------------------------------------------

data MatchingInput a b = MatchingInput
  { _menPrefs :: Map a [b]
  , _womenPrefs :: Map b [a]
  } deriving(Show, Read, Eq, Ord)
makeLenses 'MatchingInput

data MatchingState a b = MatchingState
  { _womenAtTopMatch :: Set b -- ^ unused during MPDA
  , _improvingWomen :: Set b -- ^ unused during MPDA
  -- after mpda, set of women is (disj) union of womenAtTop,
  --  improvingWomen, {notMember stableMatching}
  , _proposalsRecieved :: Map b Int

  , _floatingMan :: Maybe a -- ^ unused during MPDA
  , _volatileWomen :: [b] -- ^ unused during MPDA
  , _volatileMen :: [a] -- ^ unused during MPDA
  -- ^ invariant: one is empty iff the other are empty
  -- ^ note: stored in inverse (stack) order
  -- , _rotationsFound :: RotationPoset a b

  , _singleProposingMen :: Set a -- ^ unused during convert to WOSM
  , _singleUnmatchedMen :: Set a -- ^ unused during convert to WOSM
  , _menProposalStatus :: Map a ([b], Set b)
  -- First element: remaining proposals; second: women already proposed to
  --   subtlety: _1 is women he hasn't proposed to, _2 is women who have rejected him.
  --     thus, his current match (if it exists) is in neither collection.
  --  Another funny thing: after a terminal phase rejection chain, there is
  --    ``one too many'' element in rejected set (the worst stable partner)

  , _stableMatching :: Map b a
  -- invariant: after mpda, w being in matched set is encoded as beging a key in this
  , _experimentalMatching :: Map b a -- ^ unused during MPDA
  } deriving(Show, Read, Eq, Ord)
makeLenses 'MatchingState

initialMatchingState :: (Ord a, Ord b) => MatchingInput a b -> MatchingState a b
initialMatchingState (MatchingInput menPrefs womenPrefs) =
  MatchingState S.empty S.empty (fmap (const 0) womenPrefs)
    Nothing [] []
    men S.empty (fmap (,S.empty) menPrefs) M.empty M.empty
  where women = M.keysSet womenPrefs
        men = M.keysSet menPrefs

swapGenders :: MatchingInput a b -> MatchingInput b a
swapGenders (MatchingInput u v) = MatchingInput v u

type MatchingMonad m a b
  = (Show a, Show b, Ord a, Ord b,
    MonadState (MatchingState a b) m,
    MonadReader (MatchingInput a b) m,
    MonadWriter [(Map b a, [b], Rotation a b)] m)
    -- the writer instance holds the stable matches, and also
    -- the volatile women when the match was found. Admitedly, this is hacky
    -- and just because I want those volatile women for a very specific reason.
    -- TODO: use a different writer type to avoid quadratic time appends.

--------------------------------------------------------------------------------
-- Algorithm as in the paper
--------------------------------------------------------------------------------

mosmF :: (Show a, Show b, Ord a, Ord b) => MatchingInput a b -> Map b a
mosmF prefs = view (_2.stableMatching)
  $ runRWS mpda prefs (initialMatchingState prefs)

-- procede from one to the other by some (order undefined) sequence of simple
-- improvement cycles
mosmToWosmF :: (Show a, Show b, Ord a, Ord b)
  => MatchingInput a b -> [(Map b a, Rotation a b)]
mosmToWosmF prefs
  = fmap (\(u,_,v) -> (u,v)) . view _3 $ runRWS mosmToWosm
      prefs (initialMatchingState prefs)

rotationsF :: (Show a, Show b, Ord a, Ord b)
  => MatchingInput a b -> [Rotation a b]
rotationsF prefs
  = drop 1 $ fmap (\(_,_,v) -> v) . view _3 $ runRWS mosmToWosm
      prefs (initialMatchingState prefs)


-- builds up stableMatching, while keeping proposalsRecieved,
--   singleUnmatchedMen, menProposingStatus, updated and other fields empty
mpda :: MatchingMonad m a b => m ()
mpda = do
  whileM_ (not . S.null <$> use singleProposingMen) $ do
    man <- S.findMin <$> use singleProposingMen
    singleProposingMen %= S.delete man

    (topWomen, remainingWomen) <- use $ menProposalStatus . ix man

    rejectingWomen <- flip takeWhileM topWomen $ \woman -> do
      accepts <- acceptProposalSimple woman man
      proposalsRecieved . ix woman += 1
      return $ not accepts

    menProposalStatus . ix man . _2 %= \s -> foldr S.insert s rejectingWomen
    let topWomen' = dropWhile (`elem` rejectingWomen) topWomen
    menProposalStatus . ix man . _1 .= drop 1 topWomen'

    case topWomen' of
      woman:rest -> womanUpgradesSimple woman man
      [] -> do
        singleUnmatchedMen %= S.insert man


womanUpgradesSimple :: MatchingMonad m a b => b -> a -> m ()
womanUpgradesSimple woman man = do
  oldMatch <- use $ stableMatching . at woman
  case oldMatch of
    Nothing -> return ()
    Just m -> do
      singleProposingMen %= S.insert m
      menProposalStatus . ix m . _2 %= S.insert woman
  stableMatching . at woman .= Just man

-- if either member doesn't rank the other, they
-- will never match.
acceptProposalSimple :: MatchingMonad m a b => b -> a -> m Bool
acceptProposalSimple woman man = do
  match <- use $ stableMatching . at woman
  womanPref <- ask <&> view (womenPrefs . ix woman)
  let beforeIsh Nothing = man `elem` womanPref
      beforeIsh (Just oldMatch) = man `elem` takeWhile (/=oldMatch) womanPref
  return $ beforeIsh match

shoutMatch :: MatchingMonad m a b => Rotation a b -> m ()
shoutMatch rot = do
  mu <- use stableMatching
  vol <- use volatileWomen
  tell [(mu, vol, rot)]



initMosmToWosm :: MatchingMonad m a b => m ()
initMosmToWosm = do
  matchedWomen <- setOf (stableMatching . keysF) <$> get
  improvingWomen .= matchedWomen
  allWomen <- setOf (womenPrefs . keysF) <$> ask
  womenAtTopMatch .= allWomen `S.difference` matchedWomen

mosmToWosm :: MatchingMonad m a b => m ()
mosmToWosm = do
  mpda
  shoutMatch (makeRotation [])
  manOpt <- use stableMatching
  -- rotationsFound . psManOptMatching .= manOpt

  initMosmToWosm

  whileM_ (not . null <$> use improvingWomen) $ do
    (experimentalMatching .=) =<< use stableMatching

    womanZero <- S.findMin <$> use improvingWomen
    startNewDivorceChain womanZero

    terminalPhaseCleanup

  -- womanOpt <- use stableMatching
  -- rotationsFound . psWomanOptMatching .= womanOpt

terminalPhaseCleanup :: MatchingMonad m a b => m ()
terminalPhaseCleanup = do
  (experimentalMatching .=) =<< use stableMatching
  vol <- use volatileWomen
  womenAtTopMatch %= \s -> foldr S.insert s vol
  improvingWomen %= \s -> foldr S.delete s vol
  volatileWomen .= []
  volatileMen .= []

startNewDivorceChain :: MatchingMonad m a b => b -> m ()
startNewDivorceChain womanZero = do
  volatileWomen .= [womanZero]
  manZero <- use $ experimentalMatching . at womanZero
  -- volatileMen .= [fromJust manZero] -- should be nonempty as womanZero `elem` improvingWomen
  floatingMan .= manZero -- ^ already wrapped in Just
  experimentalMatching . at womanZero .= Nothing


  whileM_ (not . null <$> use floatingMan) $ do
    man <- fromJust <$> use floatingMan -- (theoretically) shouldn't by loop cond
    (topWomen, remainingWomen) <- use $ menProposalStatus . ix man

    rejectingWomen <- flip takeWhileM topWomen $ \woman -> do
      -- IMPORTANT: do comparison based on woman's match in stableMatch.
      accepts <- acceptProposalSimple woman man
      proposalsRecieved . ix woman += 1
      return $ not accepts
    menProposalStatus . ix man . _2 %= \s -> foldr S.insert s rejectingWomen
    let topWomen' = dropWhile (`elem` rejectingWomen) topWomen
    menProposalStatus . ix man . _1 .= topWomen'

    case topWomen' of
      [] -> do -- This case doesn't happen if |W| > |M|
        -- terminalPhaseCleanup
        floatingMan .= Nothing
        -- ^ this isn't analyzed in the paper but apparently this just works lol
      woman:rest -> do
        womanUpgradesConvert woman man


womanUpgradesConvert :: MatchingMonad m a b => b -> a -> m ()
womanUpgradesConvert woman man = do
  (stabWomen, mu) <- (,) <$> use womenAtTopMatch <*> use stableMatching
  if woman `elem` stabWomen || woman `M.notMember` mu
    then floatingMan .= Nothing -- trigger terminalPhaseCleanup

  else do
    oldMatch <- use $ experimentalMatching . at woman
    floatingMan .= oldMatch -- ^ Nothing iff woman == womanZero, as we want it!
    -- traverse (\m -> menProposalStatus . ix m . _2 %= S.insert woman) oldMatch

    experimentalMatching . at woman .= Just man

    vol <- use volatileWomen

    if woman `elem` vol
      then do -- ^ new stable match found (simple improvement cycle)
        improvementCyclePhase woman man

      else do -- continue trying to upgrade
        volatileMen %= (man:)
        volatileWomen %= (woman:)
        -- weird thing: men don't get added to volatile until they find a NEW match;
        --   where women get upgraded when they reject their old match.

improvementCyclePhase :: MatchingMonad m a b => b -> a -> m ()
improvementCyclePhase woman man = do
  volWomen <- use volatileWomen
  let adjust (as, b:bs) = (as++[b], bs)
      adjust _ = error "not possible as woman `elem` vol"
      (volImproved,volRemaining) = adjust $ span (/= woman) volWomen
  stab <- use stableMatching
  expImp <- M.filterWithKey (\k _ -> k `elem` volImproved)
    <$> use experimentalMatching
  stableMatching .= expImp `M.union` stab -- left-biased, i.e. overwrite stab.
  volatileWomen .= volRemaining -- ^ empty iff woman == womanZero, as we want!

  -- make the corresponding rotation
  volMen <- use volatileMen
  let (worsenedMen, volMenRemaining) = splitAt (length volImproved) $ man:volMen
      -- worsenedMen' = rotate 1 worsenedMen
  volatileMen .= drop 1 volMenRemaining
  -- traceShowM $ ()
  -- traceShowM $ (man, volMen, woman, volWomen)
  -- traceShowM $ (drop 1 volMenRemaining, volRemaining)
  -- traceShowM $ (worsenedMen', volImproved)

  shoutMatch (makeRotation . reverse $ zip worsenedMen volImproved)

--------------------------------------------------------------------------------
-- Examples
--------------------------------------------------------------------------------

checkStable' :: (Ord a, Ord b) => MatchingInput a b -> Map b a -> Bool
checkStable' (MatchingInput m w) mu = checkStable m w mu

unbalancedAlphaMarket ::
  MonadRandom m => Int -> Int -> m (MatchingInput Int Char)
unbalancedAlphaMarket nmen nwomen
  = uncurry MatchingInput <$> unbalancedRandomMarketFrom nmen 1 nwomen 'a'

unbalancedRandomMarketInput ::
  MonadRandom m => Int -> Int -> m (MatchingInput Int Int)
unbalancedRandomMarketInput nmen nwomen =
  uncurry MatchingInput <$> unbalancedRandomMarket nmen nwomen

stratEx :: MatchingInput Int Char
stratEx = MatchingInput
  ( M.fromList
    [ (1, "abc")
    , (2, "bac")
    ] )
  (M.fromList
    [ ('a', [2,1])
    , ('b', [1,2])
    -- , ('b', [1]) << not reporting `iso` reporting 3 above 2 in balanced case
    , ('c', [1,2])
    ] )


doesntReachWosm :: MatchingInput Int Int
doesntReachWosm = MatchingInput {_menPrefs = M.fromList [(1,[4,3,2,1]),(2,[3,1,2,4]),(3,[2,1,4,3]),(4,[2,3,1,4])], _womenPrefs = M.fromList [(1,[1,4,3,2]),(2,[4,1,2,3]),(3,[3,1,2,4]),(4,[2,4,1,3])]}

--------------------------------------------------------------------------------
-- Constructing the full latice helper funcs
--------------------------------------------------------------------------------

-- Nothing if woman is at best stable match.
-- outputs the volatile women and any improving map if it can be found
-- NOTE: if no improving map is found, the volatile women
-- have achieved their best possible husband.
-- NOTE: consideredWomen (womenAtTop ?) will (hopefull) ``short circuit'' things along
--   - if from those women we already know what happens (successors or otherwise)
--   we can stop once we get here.
iic :: (Show a, Show b, Ord a, Ord b)
  => MatchingInput a b -> Map b a -> b -> Set b
  -> (Maybe (Map b a), [b])
iic input mu woman womenAtTop
  = adjOut $ runRWS (startNewDivorceChain $ woman) input
    (adjInit $ initialMatchingState input)
  where adjOut ((), state, (m,v,_):_) = (Just m, v)
        adjOut ((), state, []) = (Nothing, state^.volatileWomen)
        adjInit i = i & stableMatching .~ mu & experimentalMatching .~ mu
          & womenAtTopMatch .~ womenAtTop -- allWomen S.\\ remainingIICableWomen
        allWomen = M.keysSet $ view womenPrefs input

