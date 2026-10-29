module Main (main) where

import Engine
  ( runMultiSig, runMultiSigTraced, runMultiSigToJson
  , MultiSigResult(..), LabelPlus(..), Payment(..), TraceEntry(..) )
import EasySM.Functional.Augmented (KeyHash, Value, Valued(..), Conf(..))
import EasySM.Functional.EasySM (TimedConf(..))
import EasySM.Examples.Functional.MultiSig
  ( State(..), StatePlus(..)
  , paymentAmount, receiver, deadline )
import Numeric.Natural (Natural)

-- | A test payment.
testPayment :: Payment
testPayment = MkPayment
  { paymentAmount = 100
  , receiver = "alice"
  , deadline = 10
  }

-- | Run a MultiSig scenario with two signers:
-- 1. Propose a payment to Alice
-- 2. Add Bob's key
-- 3. Add Charlie's key
-- 4. Pay
--
testScenario :: [LabelPlus]
testScenario =
  [ ProposePlus testPayment
  , AddPlus "bob"
  , AddPlus "charlie"
  , PayPlus
  ]

-- | Run the test and print the result.
main :: IO ()
main = do
  putStrLn "Running MultiSig contract..."
  let result = runMultiSig 1000 testScenario
  case result of
    MultiSigSuccess state val tick outs -> do
      putStrLn $ "Success!"
      putStrLn $ "  Final state: " ++ showState state
      putStrLn $ "  Final value: " ++ show val
      putStrLn $ "  Final tick:  " ++ show tick
      putStrLn $ "  Outputs:     " ++ show (map showOutput outs)
    MultiSigFailure err -> do
      putStrLn $ "Failure: " ++ err

  putStrLn ""
  putStrLn "Running MultiSig contract with trace..."
  case runMultiSigTraced 1000 testScenario of
    Nothing -> putStrLn "Failure: Contract execution failed"
    Just (trace, result') -> do
      putStrLn "Trace:"
      mapM_ (putStrLn . ("  " ++) . showTraceEntry) trace
      case result' of
        MultiSigSuccess state val tick outs -> do
          putStrLn $ "Success!"
          putStrLn $ "  Final state: " ++ showState state
          putStrLn $ "  Final value: " ++ show val
          putStrLn $ "  Final tick:  " ++ show tick
          putStrLn $ "  Outputs:     " ++ show (map showOutput outs)
        MultiSigFailure err -> putStrLn $ "Failure: " ++ err

  putStrLn ""
  putStrLn "Writing JSON files..."
  jsonResult <- runMultiSigToJson 1000 testScenario "multisig-plan.json" "multisig-config-out.json"
  case jsonResult of
    Nothing -> putStrLn "Failure: Contract execution failed"
    Just r -> do
      putStrLn "JSON files written:"
      putStrLn "  multisig-plan.json"
      putStrLn "  multisig-config-out.json"
      case r of
        MultiSigSuccess state val tick outs -> do
          putStrLn $ "Success!"
          putStrLn $ "  Final state: " ++ showState state
          putStrLn $ "  Final value: " ++ show val
          putStrLn $ "  Final tick:  " ++ show tick
          putStrLn $ "  Outputs:     " ++ show (map showOutput outs)
        MultiSigFailure err -> putStrLn $ "Failure: " ++ err

-- | Show a Valued KeyHash output.
showOutput :: Valued KeyHash -> String
showOutput v = show (amount v) ++ " -> " ++ datum v

-- | Show a State.
showState :: State -> String
showState Holding = "Holding"
showState Collecting = "Collecting"

-- | Show a trace entry.
showTraceEntry :: TraceEntry State StatePlus LabelPlus () KeyHash -> String
showTraceEntry (StepEntry action inputs outputs) =
  "Step " ++ showLabelPlus action
  ++ " (inputs: " ++ show (map showValued inputs) ++ ")"
  ++ " (outputs: " ++ show (map showOutput outputs) ++ ")"
showTraceEntry (IngressEntry msg) =
  "Ingress " ++ showValued msg
showTraceEntry (StateEntry timedConf) =
  "State: " ++ showState (baseState (conf timedConf))
  ++ " " ++ showStateValue (conf timedConf)
  ++ " (tick: " ++ show (tick timedConf) ++ ")"

-- | Show the value of a state.
-- For Holding: just the current value.
-- For Collecting: a four-tuple (value, receiver, deadline, keys).
showStateValue :: Conf State StatePlus -> String
showStateValue c = case augState c of
  HoldingPlus -> show (value c)
  CollectingPlus p keys ->
    "(" ++ show (paymentAmount p) ++ ", " ++ receiver p
    ++ ", " ++ show (deadline p) ++ ", " ++ showKeys keys ++ ")"

-- | Show a list of keys.
showKeys :: [KeyHash] -> String
showKeys [] = "[]"
showKeys (k : ks) = "[" ++ k ++ concatMap (", " ++) ks ++ "]"

-- | Show a LabelPlus action.
showLabelPlus :: LabelPlus -> String
showLabelPlus (ProposePlus p) = "Propose (" ++ show (paymentAmount p) ++ ", " ++ receiver p ++ ", " ++ show (deadline p) ++ ")"
showLabelPlus (AddPlus k) = "Add " ++ k
showLabelPlus PayPlus = "Pay"
showLabelPlus CancelPlus = "Cancel"

-- | Show a Valued input.
showValued :: Valued () -> String
showValued v = show (amount v)
