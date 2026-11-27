import RischTragerBronstein.CLI.Parse

/-!
# `rtb`: integrate formulas from the command line

`rtb 'x*exp(x^2)' '1/(x^2+1)'` answers each argument; without arguments it reads one formula per
line from standard input. `--time` prints the time taken by each formula.
-/

open RTB.CLI

def answer (timing : Bool) (s : String) : IO Unit := do
  IO.println ("∫ " ++ s ++ " dx")
  let t0 ← IO.monoMsNow
  for l in integrateText s do
    IO.println ("  " ++ l)
  if timing then IO.println s!"  [{(← IO.monoMsNow) - t0} ms]"
  (← IO.getStdout).flush

partial def repl (timing : Bool) (h : IO.FS.Stream) : IO Unit := do
  let l ← h.getLine
  if l.isEmpty then return
  let t := l.trimAscii.toString
  if t = "quit" || t = "exit" then return
  if !t.isEmpty && !t.startsWith "#" then answer timing t
  repl timing h

def main (args : List String) : IO UInt32 := do
  let timing := args.contains "--time"
  let args := args.filter (· != "--time")
  if args.isEmpty then
    repl timing (← IO.getStdin)
  else
    for a in args do answer timing a
  return 0
