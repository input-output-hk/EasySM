-- NB: For this to work, you need to set AGDA_DIR in the Haskell Language Server configuration
--     to '$HOME/.config/agda' or wherever the Agda configuration is located.

import Distribution.Simple
    ( UserHooks (..)
    , defaultMainWithHooks
    , simpleUserHooks
    )
import Distribution.Simple.PreProcess
    ( knownSuffixHandlers, PPSuffixHandler, Suffix(..), 
      PreProcessor(..), mkSimplePreProcessor, unsorted
    )
import Distribution.Types.BuildInfo(BuildInfo, hsSourceDirs)
import Distribution.Types.LocalBuildInfo(LocalBuildInfo)
import Distribution.Types.ComponentLocalBuildInfo(ComponentLocalBuildInfo)
import Distribution.Utils.Path (getSymbolicPath)
import System.Process (system)

import Data.List (intersperse)

agdaSuffixHandler :: PPSuffixHandler
agdaSuffixHandler = (Suffix "agda", preprocessAgda)

preprocessAgda :: BuildInfo -> LocalBuildInfo -> ComponentLocalBuildInfo -> PreProcessor
preprocessAgda bi _ _ =
    PreProcessor
        { platformIndependent = True
        , runPreProcessor = mkSimplePreProcessor $ \inFile outFile _verbosity ->
              let extraSrcDirs = map getSymbolicPath (hsSourceDirs bi) 
                  includes = concatMap (" -i " ++) extraSrcDirs
                  agda2hs = "agda2hs" ++ includes ++ " " ++ inFile 
              in do    
                putStrLn agda2hs          
                system agda2hs
                return ()
        , ppOrdering = unsorted
        }

main :: IO ()
main =
    defaultMainWithHooks
        $ simpleUserHooks
            { hookedPreProcessors =
                knownSuffixHandlers <> [agdaSuffixHandler]
            }
            