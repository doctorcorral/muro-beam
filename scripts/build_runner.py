#!/usr/bin/env python3
# Link the muro-beam binary.
#
# agda --ghc --ghc-dont-call-ghc has written
# MAlonzo/Code/MuroBeam/RunImage.hs. The id on d_cliRun is not stable,
# so this script reads it. This file writes MAlonzo/RunnerMain.hs and
# links it, same rule as conform.py: IO stays out of agda/.
# cliRun loads the text (loadIO) and runs drive. A format-3 image runs
# with the console at pid 1, and its lines come before the summary
# line inside the same string. The generated main reads the
# path, parses the fuel, caps the read, decodes UTF-8, and turns the
# tag into an exit code.

import os
import re
import shutil
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
HS = os.path.join(ROOT, "MAlonzo", "Code", "MuroBeam", "RunImage.hs")
MAIN = os.path.join(ROOT, "MAlonzo", "RunnerMain.hs")
BIN = os.path.join(ROOT, "muro-beam")
DEFAULT_FUEL = 1000
# 1 MiB. Checked-in images are a few hundred bytes. A larger file
# is refused with exit 1 before load sees the text.
MAX_IMAGE_BYTES = 1048576


def fail(msg):
    print(msg, file=sys.stderr)
    sys.exit(1)


def symbol(prefix):
    if not os.path.isfile(HS):
        fail("missing " + HS + " (run agda --ghc first)")
    names = []
    with open(HS, encoding="utf-8") as fh:
        for line in fh:
            m = re.match(r"^(" + prefix + r"_\d+)\s+::", line)
            if m:
                names.append(m.group(1))
    if len(names) != 1:
        fail("expected one " + prefix + " binding, found " + repr(names))
    return names[0]


def rte_dir():
    agda = os.environ.get("AGDA", "agda")
    data = subprocess.check_output([agda, "--print-agda-data-dir"], text=True).strip()
    rte = os.path.join(data, "MAlonzo", "src")
    if not os.path.isfile(os.path.join(rte, "MAlonzo", "RTE.hs")):
        fail("MAlonzo RTE not at " + rte)
    return rte


def write_main(sym, alias):
    fuel = str(DEFAULT_FUEL)
    text = "\n".join(
        [
            "module Main where",
            "",
            "import Control.Exception (IOException, try)",
            "import qualified Data.ByteString as BS",
            "import qualified Data.Text as T",
            "import qualified Data.Text.Encoding as TE",
            "import qualified Data.Text.IO as TIO",
            "import System.Environment (getArgs)",
            "import System.Exit (exitSuccess, exitWith, ExitCode(ExitFailure))",
            "import System.IO (IOMode(ReadMode), hFileSize, hPutStrLn, stderr, withBinaryFile)",
            "import System.IO.Error (ioeGetErrorString)",
            "import MAlonzo.Code.MuroBeam.RunImage (" + sym + ", " + alias + ")",
            "",
            "usage :: String",
            "usage = unlines",
            "  [ \"usage: muro-beam IMAGE [--fuel N]\"",
            "  , \"       muro-beam --alias-bind IMAGE\"",
            "  , \"       muro-beam --help\"",
            "  , \"\"",
            "  , \"Load a .mbi image and run it on the round-robin driver.\"",
            "  , \"--alias-bind loads IMAGE, plants a second reference on the\"",
            "  , \"returned reply cell, and prints the bind refusal.\"",
            "  , \"A load refusal under --alias-bind is exit 2, same as a normal load.\"",
            "  , \"N is a natural. The default is " + fuel + ".\"",
            "  , \"\"",
            "  , \"The last line is the summary: outcome, events, fingerprint\"",
            "  , \"(h<heap>l<live>p<procs>), kept nat. Formats 1 and 2 print only\"",
            "  , \"that line. Format 3 boots a console at pid 1 and first prints\"",
            "  , \"one line per message delivered to it, in order: a nat,\"",
            "  , \"con <tag>, closure, or stuck. The console counts in p<procs>:\"",
            "  , \"--fuel 0 prints fuel [] h0l0p1 v- for formats 1 and 2, and\"",
            "  , \"fuel [] h0l0p2 v- for format 3.\"",
            "  , \"exit 0  halted, deadlock, or stuck\"",
            "  , \"         --alias-bind on a loaded image also exits 0\"",
            "  , \"         and prints refuse: aliased reply result\"",
            "  , \"exit 1  usage, a file that cannot be read, or a bad fuel\"",
            "  , \"exit 2  parse or load refusal\"",
            "  , \"exit 3  out of fuel (stdout still has the partial line)\"",
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
            "    go path fuel (\"--fuel\" : []) = die \"muro-beam: --fuel needs a natural\"",
            "    go Nothing fuel (flag : rest)",
            "      | take 1 flag /= \"-\" = go (Just flag) fuel rest",
            "    go _ _ _ = die usage",
            "",
            "maxImageBytes :: Integer",
            "maxImageBytes = " + str(MAX_IMAGE_BYTES),
            "",
            "readLimited :: FilePath -> IO (Either String T.Text)",
            "readLimited path =",
            "  withBinaryFile path ReadMode $ \\h -> do",
            "    size <- hFileSize h",
            "    if size > maxImageBytes",
            "      then return (Left \"file too large\")",
            "      else do",
            "        bs <- BS.hGet h (fromInteger size)",
            "        case TE.decodeUtf8' bs of",
            "          Left _ -> return (Left \"invalid UTF-8\")",
            "          Right src -> return (Right src)",
            "",
            "readImage :: FilePath -> IO T.Text",
            "readImage path = do",
            "  r <- try (readLimited path)",
            "  case r of",
            "    Left e ->",
            "      die (\"muro-beam: cannot read \" ++ path ++ \": \" ++ ioeGetErrorString (e :: IOException))",
            "    Right (Left reason) ->",
            "      die (\"muro-beam: cannot read \" ++ path ++ \": \" ++ reason)",
            "    Right (Right src) -> return src",
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
            "  args <- getArgs",
            "  case args of",
            "    [\"--alias-bind\", path] -> do",
            "      src <- readImage path",
            "      dispatch (" + alias + " src)",
            "    _ -> do",
            "      (path, fuel) <- parseArgs args",
            "      src <- readImage path",
            "      dispatch (" + sym + " src fuel)",
            "",
        ]
    )
    os.makedirs(os.path.dirname(MAIN), exist_ok=True)
    with open(MAIN, "w", encoding="utf-8") as fh:
        fh.write(text)


def main():
    if shutil.which("ghc") is None:
        fail("ghc is not on PATH")
    sym = symbol("d_cliRun")
    alias = symbol("d_aliasCli")
    print("cliRun symbol " + sym, file=sys.stderr)
    print("aliasCli symbol " + alias, file=sys.stderr)
    write_main(sym, alias)
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
            "-package",
            "bytestring",
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
