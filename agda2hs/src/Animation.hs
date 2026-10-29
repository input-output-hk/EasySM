{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DuplicateRecordFields #-}

-- | JSON generation for the EasySM animation system.
--
-- This module converts execution traces into the "Animation Plan" JSON format
-- and writes the "Automaton Configuration" JSON file (hardcoded to MultiSig for now).
--
module Animation
  ( -- * Animation Plan
    AnimationPlan(..)
  , AnimationStep(..)
  , traceToAnimationPlan
  , writeAnimationPlan
    -- * Automaton Configuration
  , writeAutomatonConfig
  ) where

import Data.Aeson (ToJSON(..), object, (.=), encode)
import qualified Data.ByteString.Lazy as BL
import Data.Text (Text, pack)
import Numeric.Natural (Natural)

import EasySM.Functional.Augmented (Conf(..), Valued(..), KeyHash, Value)
import EasySM.Functional.EasySM (TimedConf(..), TraceEntry(..))
import EasySM.Examples.Functional.MultiSig
  ( State(..), LabelPlus(..), StatePlus(..), Payment(..)
  , paymentAmount, receiver, deadline )


------------------------------------------------------------------------------
-- Animation Plan types
--

-- | An animation plan: the sequence of steps to animate.
--
data AnimationPlan = AnimationPlan
  { initialState :: Text
  , initialValue :: Maybe Text
  , steps        :: [AnimationStep]
  }

-- | A single animation step: either a state transition or an action.
--
data AnimationStep
  = StateStep
      { node      :: Text
      , valueText :: Maybe Text
      }
  | ActionStep
      { edge      :: Text
      , label     :: Text
      , valueText :: Maybe Text
      }

instance ToJSON AnimationPlan where
  toJSON (AnimationPlan st val steps) = object
    [ "initialState" .= st
    , "initialValue" .= val
    , "steps"        .= steps
    ]

instance ToJSON AnimationStep where
  toJSON (StateStep node val) = object
    [ "type"      .= ("state" :: Text)
    , "node"      .= node
    , "valueText" .= val
    ]
  toJSON (ActionStep edge label val) = object
    [ "type"      .= ("action" :: Text)
    , "edge"      .= edge
    , "label"     .= label
    , "valueText" .= val
    ]


------------------------------------------------------------------------------
-- Convert trace to Animation Plan
--

-- | Convert an execution trace to an animation plan for the MultiSig contract.
--
traceToAnimationPlan
  :: Value                    -- ^ initial value
  -> [TraceEntry State StatePlus LabelPlus () KeyHash]
  -> AnimationPlan
traceToAnimationPlan initialVal trace = AnimationPlan
  { initialState = "holding"
  , initialValue = Just (pack (show initialVal))
  , steps        = concatMap traceEntryToSteps trace
  }

-- | Convert a single trace entry to animation steps.
--
traceEntryToSteps :: TraceEntry State StatePlus LabelPlus () KeyHash -> [AnimationStep]
traceEntryToSteps (StepEntry action _inputs outputs) =
  [ ActionStep
      { edge      = labelPlusToEdge action
      , label     = labelPlusToLabel action
      , valueText = labelPlusToValue action outputs
      }
  ]
traceEntryToSteps (IngressEntry _msg) =
  []  -- Ingress not used in MultiSig animation
traceEntryToSteps (StateEntry timedConf) =
  [ StateStep
      { node      = stateToNode (baseState (conf timedConf))
      , valueText = Just (stateValueText (conf timedConf))
      }
  ]

-- | Format the value text for a state.
--
-- For Holding: just the current value.
-- For Collecting: a four-tuple (value, receiver, deadline, keys).
--
stateValueText :: Conf State StatePlus -> Text
stateValueText c = case augState c of
  HoldingPlus -> pack (show (value c))
  CollectingPlus p keys ->
    pack ("(" ++ show (paymentAmount p) ++ ", " ++ receiver p
          ++ ", " ++ show (deadline p) ++ ", " ++ showKeys keys ++ ")")

-- | Format a list of keys as a string.
--
showKeys :: [KeyHash] -> String
showKeys [] = "[]"
showKeys (k : ks) = "[" ++ k ++ concatMap (", " ++) ks ++ "]"

-- | Map a LabelPlus action to an edge id.
--
labelPlusToEdge :: LabelPlus -> Text
labelPlusToEdge (ProposePlus _) = "propose"
labelPlusToEdge (AddPlus _)     = "add"
labelPlusToEdge PayPlus         = "pay"
labelPlusToEdge CancelPlus      = "cancel"

-- | Map a LabelPlus action to a display label.
--
labelPlusToLabel :: LabelPlus -> Text
labelPlusToLabel (ProposePlus _) = "Propose"
labelPlusToLabel (AddPlus _)     = "Add key"
labelPlusToLabel PayPlus         = "Pay"
labelPlusToLabel CancelPlus      = "Cancel"

-- | Extract a value text from a LabelPlus action and its outputs.
--
labelPlusToValue :: LabelPlus -> [Valued KeyHash] -> Maybe Text
labelPlusToValue (ProposePlus p) _ =
  Just (pack ("(" ++ show (paymentAmount p) ++ ", " ++ receiver p
              ++ ", " ++ show (deadline p) ++ ")"))
labelPlusToValue (AddPlus k) _ = Just (pack k)
labelPlusToValue PayPlus outputs =
  case outputs of
    (v : _) -> Just (pack (show (amount v) ++ " -> " ++ datum v))
    []      -> Nothing
labelPlusToValue CancelPlus _ = Nothing

-- | Map a State to a node id.
--
stateToNode :: State -> Text
stateToNode Holding = "holding"
stateToNode Collecting = "collecting"


------------------------------------------------------------------------------
-- Write JSON files
--

-- | Write an animation plan to a JSON file.
--
writeAnimationPlan :: FilePath -> AnimationPlan -> IO ()
writeAnimationPlan path plan = BL.writeFile path (encode plan)

-- | Write the automaton configuration to a JSON file.
--
-- For now, this is hardcoded to the MultiSig contract configuration.
-- The configuration is read from the bundled @multisig-config.json@ file.
--
writeAutomatonConfig :: FilePath -> IO ()
writeAutomatonConfig path = do
  config <- readFile "multisig-config.json"
  writeFile path config
