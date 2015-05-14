module Main (main) where

import Data.Maybe
import System.FilePath
import System.Process
import System.IO
import System.Exit
import System.Console.GetOpt

import Futhark.Pipeline
import Futhark.Passes
import Futhark.Compiler
import qualified Futhark.CodeGen.Backends.SequentialC as SequentialC
import Futhark.Util.Options

main :: IO ()
main = mainWithOptions newCompilerConfig commandLineOptions inspectNonOptions
  where inspectNonOptions [file] config = Just $ compile config file
        inspectNonOptions _      _      = Nothing


compile :: CompilerConfig -> FilePath -> IO ()
compile config filepath = do
  (msgs, res) <- runPipelineOnProgram (futharkConfig config) filepath
  hPutStr stderr msgs
  case res of
    Left err -> do
      hPutStrLn stderr $ errorDesc err
      exitWith $ ExitFailure 2
    Right (Basic _) ->
      error "Pipeline produced program without memory annotations."
    Right (ExplicitMemory prog) ->
      case SequentialC.compileProg prog of
        Left err -> do
          hPutStrLn stderr err
          exitWith $ ExitFailure 2
        Right cprog -> do
          let binpath = outputFilePath filepath config
              cpath = binpath `replaceExtension` "c"
          writeFile cpath cprog
          (gccCode, _, gccerr) <-
            readProcessWithExitCode "gcc"
            [cpath, "-o", binpath, "-lm", "-O3", "-std=c99"] ""
          case gccCode of
            ExitFailure code -> error $ "gcc failed with code " ++ show code ++ ":\n" ++ gccerr
            ExitSuccess      -> return ()

type CompilerOption = OptDescr (Either (IO ()) (CompilerConfig -> CompilerConfig))

commandLineOptions :: [CompilerOption]
commandLineOptions =
  [ Option "o" []
    (ReqArg (\filename -> Right $ \config -> config { compilerOutput = Just filename })
     "FILE")
    "Name of the compiled binary."
  , Option [] ["real-as-single"]
    (NoArg $ Right $ \config -> config { compilerRealConfiguration = RealAsFloat32 } )
    "Map 'real' to 32-bit floating point."
  , Option [] ["real-as-double"]
    (NoArg $ Right $ \config -> config { compilerRealConfiguration = RealAsFloat64 } )
    "Map 'real' to 64-bit floating point (the default)."
  , Option "V" ["verbose"]
    (OptArg (\file -> Right $ \config -> config { compilerVerbose = Just file }) "FILE")
    "Print verbose output on standard error; wrong program to FILE."
  , Option [] ["unsafe"]
    (NoArg $ Right $ \config -> config { compilerUnsafe = True })
    "Do not perform bound- and size-checks in generated code."
  ]

data CompilerConfig =
  CompilerConfig { compilerOutput :: Maybe FilePath
                 , compilerVerbose :: Maybe (Maybe FilePath)
                 , compilerRealConfiguration :: RealConfiguration
                 , compilerUnsafe :: Bool
                 }

newCompilerConfig :: CompilerConfig
newCompilerConfig = CompilerConfig { compilerOutput = Nothing
                                   , compilerVerbose = Nothing
                                   , compilerRealConfiguration = RealAsFloat64
                                   , compilerUnsafe = False
                                   }

outputFilePath :: FilePath -> CompilerConfig -> FilePath
outputFilePath srcfile =
  fromMaybe (srcfile `replaceExtension` "") . compilerOutput

futharkConfig :: CompilerConfig -> FutharkConfig
futharkConfig config =
  newFutharkConfig { futharkPipeline = compilerPipeline
                   , futharkVerbose = compilerVerbose config
                   , futharkRealConfiguration = compilerRealConfiguration config
                   , futharkBoundsCheck = not $ compilerUnsafe config
                   }

compilerPipeline :: [Pass]
compilerPipeline =
  standardPipeline ++
  [ fotransform
  , eotransform
  , inPlaceLowering
  , explicitMemory
  , eotransform
  , commonSubexpressionElimination
  , eotransform
  , doubleBuffer
  , eotransform
  ]
