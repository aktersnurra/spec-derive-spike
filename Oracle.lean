import SpecDerive

/-!
# Lean oracle

`oracle <example>` reads one input per line on stdin and prints, per line,
`<reference result> <checkInvariant result> <Bounded>`, computed by the Lean definitions
(compiled by Lean, with unbounded `Int`). The OCaml differential test compares against it.

Input line formats (space-separated tokens):
* `running_sum`: entries newest first, each `x:cum`. An empty line is the empty list.
* `sorted_lookup`: the query key, then entries `key:value`. Results print as `none` or
  `some <v>`.
-/

def words (line : String) : List String := (line.splitOn " ").filter (· ≠ "")

def ints (tok : String) : Option (List Int) := (tok.splitOn ":").mapM String.toInt?

def runningSum (line : String) : Option String := do
  let s ← (words line).mapM fun tok => do
    let [x, cum] ← ints tok | none
    pure ({ x, cum } : RunningSum.Entry)
  pure s!"{RunningSum.reference s} {RunningSum.checkInvariant s} {decide (RunningSum.Bounded s)}"

def sortedLookup (line : String) : Option String := do
  let k :: toks := words line | none
  let k ← k.toInt?
  let s ← toks.mapM fun tok => do
    let [key, value] ← ints tok | none
    pure ({ key, value } : SortedLookup.Entry)
  let r := match SortedLookup.reference s k with
    | none => "none"
    | some v => s!"some {v}"
  pure s!"{r} {SortedLookup.checkInvariant s} {decide (SortedLookup.Bounded s k)}"

def examples : List (String × (String → Option String)) :=
  [("running_sum", runningSum), ("sorted_lookup", sortedLookup)]

partial def loop (f : String → Option String) (stdin : IO.FS.Stream) (stdout : IO.FS.Stream)
    (lineNo : Nat) : IO UInt32 := do
  let line ← stdin.getLine
  if line.isEmpty then return 0
  match f (line.trimAsciiEnd.toString) with
  | some out => stdout.putStrLn out; loop f stdin stdout (lineNo + 1)
  | none => IO.eprintln s!"oracle: malformed input on line {lineNo}"; return 1

def main : List String → IO UInt32
  | [name] =>
    match examples.lookup name with
    | some f => do
      let code ← loop f (← IO.getStdin) (← IO.getStdout) 1
      (← IO.getStdout).flush
      return code
    | none => do IO.eprintln s!"oracle: unknown example {name}"; return 2
  | _ => do IO.eprintln "usage: oracle <example> < inputs"; return 2
