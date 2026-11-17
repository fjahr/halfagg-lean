import Halfagg.Vectors

/-!
# Differential test driver

Reads one case per line from standard input, runs the byte-level model of
`Halfagg.Vectors` on it and prints one result per line. `scripts/fuzz.py`
generates the cases and compares the results with BIP458's Python reference.

Line formats (hex fields, `_` for empty bytes, `-` for an empty list):

* `A pk:m:sig,…`: `Aggregate`
* `I aggsig pk:m,… pk:m:sig,…`: `IncAggregate`
* `V aggsig pk:m,…`: `VerifyAggregate`
-/

open Halfagg.Vectors Taproot.BIP340Vectors

def field (s : String) : Bytes := if s == "_" then [] else hex s

def toHex (b : Bytes) : String :=
  let d (x : Nat) : Char := "0123456789abcdef".toList.getD x '0'
  String.ofList (b.flatMap fun x => [d (x.toNat / 16), d (x.toNat % 16)])

def parts (s : String) : List (List Bytes) :=
  if s == "-" then [] else (s.splitOn ",").map fun it => (it.splitOn ":").map field

def pm2 (s : String) : List (Bytes × Bytes) :=
  (parts s).map fun l => (l.getD 0 [], l.getD 1 [])

def pm3 (s : String) : List (Bytes × Bytes × Bytes) :=
  (parts s).map fun l => (l.getD 0 [], l.getD 1 [], l.getD 2 [])

def showAgg : Option Bytes → String
  | none => "FAIL"
  | some b => toHex b

def run (line : String) : String :=
  match line.splitOn " " with
  | ["A", pms] => showAgg (aggregateBytes (pm3 pms))
  | ["I", agg, pm, pms] => showAgg (incAggregateBytes (field agg) (pm2 pm) (pm3 pms))
  | ["V", agg, pm] => toString (verifyAggregateBytesFast (field agg) (pm2 pm))
  | _ => "BADLINE"

partial def loop (stdin stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  stdout.putStrLn (run (String.ofList (line.toList.filter (· != '\n'))))
  stdout.flush
  loop stdin stdout

def main : IO Unit := do
  loop (← IO.getStdin) (← IO.getStdout)
