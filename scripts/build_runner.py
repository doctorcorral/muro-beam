#!/usr/bin/env python3
# Link the muro-beam binary.
#
# agda --ghc --ghc-dont-call-ghc has written
# MAlonzo/Code/MuroBeam/RunImage.hs. The id on d_cliRun is not stable,
# so this script reads it. The main is handwritten Haskell under
# MAlonzo/, same rule as conform.py: IO stays out of agda/.
# cliRun loads the text and runs drive. This file only reads the
# path, parses the fuel, and turns the tag into an exit code.

import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
HS = os.path.join(ROOT, "MAlonzo", "Code", "MuroBeam", "RunImage.hs")
MAIN = os.path.join(ROOT, "MAlonzo", "RunnerMain.hs")
BIN = os.path.join(ROOT, "muro-beam")
DEFAULT_FUEL = 1000


def fail(msg):
    print(msg, file=sys.stderr)
    sys.exit(1)


def symbol():
    if not os.path.isfile(HS):
        fail("missing " + HS + " (run agda --ghc first)")
    names = []
    with open(HS, encoding="utf-8") as fh:
        for line in fh:
            m = re.match(r"^(d_cliRun_\d+)\s+::", line)
            if m:
                names.append(m.group(1))
    if len(names) != 1:
        fail("expected one d_cliRun binding, found " + repr(names))
    return names[0]


def rte_dir():
    agda = os.environ.get("AGDA", "agda")
    data = subprocess.check_output([agda, "--print-agda-data-dir"], text=True).strip()
    rte = os.path.join(data, "MAlonzo", "src")
    if not os.path.isfile(os.path.join(rte, "MAlonzo", "RTE.hs")):
        fail("MAlonzo RTE not at " + rte)
    return rte


def write_main(sym):
    fuel = str(DEFAULT_FUEL)
    text = "\n".join(
        [
            "module Main where",
            "",
            "import Control.Exception (IOException, try)",
            "import System.Environment (getArgs)",
            "import System.Exit (exitSuccess, exitWith, ExitCode(ExitFailure))",
            "import System.IO (hPutStrLn, stderr)",
            "import System.IO.Error (ioeGetErrorString)",
            "import qualified Data.Text as T",
            "import qualified Data.Text.IO as TIO",
            "import MAlonzo.Code.MuroBeam.RunImage (" + sym + ")",
            "",
            "usage :: String",
            "usage = unlines",
            "  [ \"usage: muro-beam IMAGE [--fuel N]\"",
            "  , \"       muro-beam --help\"",
            "  , \"\"",
            "  , \"Load a .mbi image and run it on the round-robin driver.\"",
            "  , \"N is a natural. The default is " + fuel + ".\"",
            "  , \"\"",
            "  , \"A finished run prints one line: outcome, events, fingerprint, kept nat.\"",
            "  , \"exit 0  halted, deadlock, or stuck\"",
            "  , \"exit 1  usage, a missing file, or a bad fuel\"",
            "  , \"exit 2  parse or load refusal\"",
            "  , \"exit 3  out of fuel\"",
            "  ]",
            "",
            "die :: String -> IO a",
            "die msg = hPutStrLn stderr msg >> exitWith (ExitFailure 1)",
            "",
            "readNat :: String -> Maybe Integer",
            "readNat s = case reads s of",
            "  [(n, \"\")] | n >= 0 -> Just n",
            "  _ -> Nothing",
            "",
            "parseArgs :: [String] -> IO (FilePath, Integer)",
            "parseArgs = go Nothing Nothing",
            "  where",
            "    go (Just path) (Just fuel) [] = return (path, fuel)",
            "    go (Just path) Nothing [] = return (path, " + fuel + ")",
            "    go _ _ (\"--help\" : _) = putStr usage >> exitSuccess",
            "    go _ _ (\"-h\" : _) = putStr usage >> exitSuccess",
            "    go path fuel (\"--fuel\" : n : rest) =",
            "      case readNat n of",
            "        Nothing -> die (\"muro-beam: bad fuel: \" ++ n)",
            "        Just k ->",
            "          case fuel of",
            "            Just _ -> die \"muro-beam: fuel given twice\"",
            "            Nothing -> go path (Just k) rest",
            "    go path fuel (\"--fuel\" : []) = die \"muro-beam: bad fuel:\"",
            "    go Nothing fuel (flag : rest)",
            "      | take 1 flag /= \"-\" = go (Just flag) fuel rest",
            "    go _ _ _ = die usage",
            "",
            "readImage :: FilePath -> IO T.Text",
            "readImage path = do",
            "  r <- try (TIO.readFile path)",
            "  case r of",
            "    Left e ->",
            "      die (\"muro-beam: cannot read \" ++ path ++ \": \" ++ ioeGetErrorString (e :: IOException))",
            "    Right src -> return src",
            "",
            "dispatch :: T.Text -> IO ()",
            "dispatch t =",
            "  let (tag, rest0) = T.breakOn (T.pack \"\\n\") t",
            "      rest = T.drop 1 rest0",
            "  in case T.unpack tag of",
            "    \"ok\" -> TIO.putStrLn rest",
            "    \"fuel\" -> do",
            "      TIO.putStrLn rest",
            "      hPutStrLn stderr \"muro-beam: out of fuel\"",
            "      exitWith (ExitFailure 3)",
            "    \"load\" -> do",
            "      hPutStrLn stderr (\"muro-beam: \" ++ T.unpack rest)",
            "      exitWith (ExitFailure 2)",
            "    other -> die (\"muro-beam: bad runner result: \" ++ other)",
            "",
            "main :: IO ()",
            "main = do",
            "  (path, fuel) <- getArgs >>= parseArgs",
            "  src <- readImage path",
            "  dispatch (" + sym + " src fuel)",
            "",
        ]
    )
    os.makedirs(os.path.dirname(MAIN), exist_ok=True)
    with open(MAIN, "w", encoding="utf-8") as fh:
        fh.write(text)


def main():
    if subprocess.call(["ghc", "--version"], stdout=subprocess.DEVNULL) != 0:
        fail("ghc is not on PATH")
    sym = symbol()
    print("cliRun symbol " + sym, file=sys.stderr)
    write_main(sym)
    rte = rte_dir()
    subprocess.run(
        [
            "ghc",
            "-O0",
            "-j1",
            "-i" + ROOT,
            "-i" + rte,
            "-package",
            "text",
            "-o",
            BIN,
            MAIN,
        ],
        check=True,
        cwd=ROOT,
    )
    print("linked " + BIN, file=sys.stderr)


if __name__ == "__main__":
    main()
