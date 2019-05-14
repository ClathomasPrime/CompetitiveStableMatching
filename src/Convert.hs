{-# LANGUAGE FlexibleContexts, ConstraintKinds, TemplateHaskell,
  TupleSections, TypeFamilies #-}
module Convert where

import Data.Set (Set)
import qualified Data.Set as S
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Control.Monad.Random
import Control.Lens
import Data.Set.Lens
import Data.Maybe
import Control.Monad.RWS

import Utils
import Main
import Rand

import Debug.Trace


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
  , _proposalsRecieved :: Map b Int

  , _floatingMan :: Maybe a -- ^ unused during MPDA
  , _volatileWomen :: [b] -- ^ unused during MPDA
  -- ^ invariant: one is empty iff the other is empty
  -- ^ note: stored in inverse (stack) order

  , _singleProposingMen :: Set a -- ^ unused during convert to WOSM
  , _singleUnmatchedMen :: Set a -- ^ unused during convert to WOSM
  , _menProposalStatus :: Map a ([b], Set b)
  -- First element: remaining proposals; second: women already proposed to

  , _stableMatching :: Map b a
  , _experimentalMatching :: Map b a -- ^ unused during MPDA
  } deriving(Show, Read, Eq, Ord)
makeLenses 'MatchingState

initialMatchingState :: (Ord a, Ord b) => MatchingInput a b -> MatchingState a b
initialMatchingState (MatchingInput menPrefs womenPrefs) =
  MatchingState S.empty S.empty (fmap (const 0) womenPrefs)
    Nothing []
    men S.empty (fmap (,S.empty) menPrefs) M.empty M.empty
  where women = M.keysSet womenPrefs
        men = M.keysSet menPrefs

swapGenders :: MatchingInput a b -> MatchingInput b a
swapGenders (MatchingInput u v) = MatchingInput v u

type MatchingMonad m a b
  = (Show a, Show b, Ord a, Ord b, MonadState (MatchingState a b) m,
    MonadReader (MatchingInput a b) m, MonadWriter [(Map b a, [b])] m)
    -- the writer instance holds the stable matches, and also
    -- the volatile women when the match was found. admitedly, this is hacky
    -- and just because I want those volatile women for a very specific reason.

--------------------------------------------------------------------------------
-- Algorithm as in the paper
--------------------------------------------------------------------------------

mosmF :: (Show a, Show b, Ord a, Ord b) => MatchingInput a b -> Map b a
mosmF prefs = view (_2.stableMatching)
  $ runRWS mpda prefs (initialMatchingState prefs)

-- procede from one to the other by some (order undefined) sequence of simple
-- improvement cycles
mosmToWosmF :: (Show a, Show b, Ord a, Ord b) => MatchingInput a b -> [Map b a]
mosmToWosmF prefs
  = fmap fst . view _3 $ runRWS (mpda >> shoutMatch >> mosmToWosm)
      prefs (initialMatchingState prefs)

mpda :: MatchingMonad m a b => m ()
mpda = do
  whileM_ (not . S.null <$> use singleProposingMen) $ do
    man <- S.findMin <$> use singleProposingMen
    -- traceShowM man
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
  -- if match == Just man
  --   then traceShowM $ "acceptoCheck: " ++ show match ++ show man
  --     ++ show (beforeIsh match)
  --   else return ()
  return $ beforeIsh match

shoutMatch :: MatchingMonad m a b => m ()
shoutMatch = do
  mu <- use stableMatching
  vol <- use volatileWomen
  tell [(mu, vol)]



initMosmToWosm :: MatchingMonad m a b => m ()
initMosmToWosm = do
  matchedWomen <- setOf (stableMatching . keysF) <$> get
  improvingWomen .= matchedWomen
  allWomen <- setOf (womenPrefs . keysF) <$> ask
  womenAtTopMatch .= S.empty

mosmToWosm :: MatchingMonad m a b => m ()
mosmToWosm = do
  initMosmToWosm
  whileM_ (not . null <$> use improvingWomen) $ do
    -- traceShowM =<< use improvingWomen
    (experimentalMatching .=) =<< use stableMatching

    womanZero <- S.findMin <$> use improvingWomen
    startNewDivorceChain womanZero

    terminalPhaseCleanup

terminalPhaseCleanup :: MatchingMonad m a b => m ()
terminalPhaseCleanup = do
  (experimentalMatching .=) =<< use stableMatching
  vol <- use volatileWomen
  -- traceM $ "vol terminal: " ++ show vol
  womenAtTopMatch %= \s -> foldr S.insert s vol
  improvingWomen %= \s -> foldr S.delete s vol
  volatileWomen .= []

startNewDivorceChain :: MatchingMonad m a b => b -> m ()
startNewDivorceChain womanZero = do
  volatileWomen .= [womanZero]
  manZero <- use $ experimentalMatching . at womanZero
  floatingMan .= manZero -- ^ already wrapped in Just
  -- traceShowM (womanZero, manZero)
  experimentalMatching . at womanZero .= Nothing

  -- traceM $ "zero: " ++ show (womanZero, manZero)

  whileM_ (not . null <$> use floatingMan) $ do
    man <- fromJust <$> use floatingMan -- (theoretically) shouldn't by loop cond
    -- traceM $ "proposing man: " ++ show man
    (topWomen, remainingWomen) <- use $ menProposalStatus . ix man

    -- traceShowM (man, topWomen)
    rejectingWomen <- flip takeWhileM topWomen $ \woman -> do
      accepts <- acceptProposalSimple woman man
      proposalsRecieved . ix woman += 1
      -- traceM $ show woman ++ " replies with " ++ show accepts
      return $ not accepts
    menProposalStatus . ix man . _2 %= \s -> foldr S.insert s rejectingWomen
    let topWomen' = dropWhile (`elem` rejectingWomen) topWomen
    menProposalStatus . ix man . _1 .= topWomen'
    -- menProposalStatus . ix man . _1 .= drop 1 topWomen'

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
  -- traceM $ "stabWomen: " ++ show stabWomen
  if woman `elem` stabWomen || woman `M.notMember` mu
    then floatingMan .= Nothing -- terminalPhaseCleanup

  else do
    oldMatch <- use $ experimentalMatching . at woman
    floatingMan .= oldMatch -- ^ Nothing iff woman == womanZero, as we want it!
    -- traverse (\m -> menProposalStatus . ix m . _2 %= S.insert woman) oldMatch

    experimentalMatching . at woman .= Just man

    vol <- use volatileWomen
    -- traceM $ "vol improver: " ++ show vol ++ " at " ++ show (woman, man)
    -- traceM $ "new floating man: " ++ show oldMatch
    -- case oldMatch of
    --   Just m -> traceShowM =<< use (menProposalStatus . at m)
    --   Nothing -> return ()

    if woman `elem` vol
      then do -- ^ new stable match found (simple improvement cycle)
        let adjust (as, b:bs) = (b:as, bs)
            adjust _ = error "not possible as woman `elem` vol"
            (volImproved,volRemaining) = adjust $ span (/= woman) vol
        stab <- use stableMatching
        expImp <- M.filterWithKey (\k _ -> k `elem` volImproved)
          <$> use experimentalMatching
        stableMatching .= expImp `M.union` stab
        shoutMatch
        volatileWomen .= volRemaining -- ^ empty iff woman == womanZero, as we want!
        -- traceShowM volRemaining

      else do -- continue trying to upggrade
        volatileWomen %= (woman:)


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
-- NOTE: consideredWomen will (hopefull) ``short circuit'' things along -
--   if from those women we already know what happens (successors or otherwise)
--   we can stop once we get here.
iic :: (Show a, Show b, Ord a, Ord b)
  => MatchingInput a b -> Map b a -> b -> Set b
  -> (Maybe (Map b a), [b])
iic input mu woman womenAtTop
  = adjOut $ runRWS (startNewDivorceChain $ woman) input
    (adjInit $ initialMatchingState input)
  where adjOut ((), state, (m,v):_) = (Just m, v)
        adjOut ((), state, []) = (Nothing, state^.volatileWomen)
        adjInit i = i & stableMatching .~ mu & experimentalMatching .~ mu
          & womenAtTopMatch .~ womenAtTop -- allWomen S.\\ remainingIICableWomen
        allWomen = M.keysSet $ view womenPrefs input

