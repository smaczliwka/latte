module Main where

import System.Environment   (getArgs)
import System.Exit          (exitFailure, exitSuccess, ExitCode(..))
import System.FilePath      (takeBaseName, replaceExtension, takeDirectory)
import System.Process       (readProcessWithExitCode, readCreateProcessWithExitCode)
import System.IO            (stderr, hPutStrLn)

import AbsLatte             (Program)
import LexLatte             (Token)
import ParLatte             (pProgram, myLexer)
import Typechecker          (typecheck)
import Emiter               (emitP)
import Printer              (printLLVM)

type Err        = Either String
type ParseFun a = [Token] -> Err a

runFile parseFun filePath = do
  instantSourceCode <- readFile filePath
  let llvmSourceCodeFilePath = replaceExtension filePath "ll"
  let llvmByteCodeFilePath = replaceExtension filePath "bc"
  case run parseFun instantSourceCode of
    Left error -> do
      hPutStrLn stderr error
      exitFailure
    Right code -> do
        writeFile llvmSourceCodeFilePath code
        (exitcode, out, err) <- readProcessWithExitCode "llvm-as" ["-o", llvmByteCodeFilePath, llvmSourceCodeFilePath] ""
        case exitcode of
          ExitSuccess -> do
            (exitcode', out', err') <- readProcessWithExitCode "llvm-link" ["-o", llvmByteCodeFilePath, llvmByteCodeFilePath, "lib/runtime.bc"] ""
            case exitcode' of
              ExitSuccess -> exitSuccess
              ExitFailure i' -> do
                hPutStrLn stderr $ "An error occurred (exit code: " ++ show i' ++ ")"
                hPutStrLn stderr out
                hPutStrLn stderr err
                exitFailure
          ExitFailure i -> do
            hPutStrLn stderr $ "An error occurred (exit code: " ++ show i ++ ")"
            hPutStrLn stderr out
            hPutStrLn stderr err
            exitFailure

run :: ParseFun Program -> String -> Either String String
run parseFun s = case parseFun ts of
    Left error -> Left error
    Right prog ->
      case typecheck prog of
        Just error -> Left error
        Nothing -> Right (compile prog)
  where
  ts = myLexer s

compile :: Program -> String
compile prog = printLLVM (emitP prog)

usage :: IO ()
usage = do
  putStrLn $ unlines
    [ "usage: Call with one of the following argument combinations:"
    , "  --help          Display this help message."
    , "  (files)         Compile files."
    ]

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["--help"] -> usage
    fs         -> mapM_ (runFile pProgram) fs
