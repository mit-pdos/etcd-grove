/-
`compare-exports CONFIG CHALLENGE_EXPORT SOLUTION_EXPORT`: the comparator's check
(leanprover/comparator v4.34.0, `Main.lean`'s `verifyMatch`) on two `lean4export` exports made in
separate Lake workspaces. The challenge and the solution have modules of the same names (the
challenge's are trimmed copies of the solution's: a private name like
`_private.<Module>.0.<decl>._proof_1` holds its module's name), so one workspace, one `LEAN_PATH`,
cannot hold both, and `comparator` itself takes one.

Built as an executable of the comparator's package (challenge/check.sh adds it), so the comparison
is the comparator's own code: `Comparator.compareAt` (every constant reached from the theorems'
and the permitted axioms' statements is the challenge's, name for name, value for value),
`Comparator.checkAxioms` (the solution's theorems use no other axiom), and the kernel replay below
(`Main.lean`'s `runBuiltinKernel`, copied unchanged but for its monad). The export targets are
`Main.lean`'s too: `builtinTargets ++ theorem_names ++ permitted_axioms ++ primitiveTargets`
(challenge/check.sh passes them to `lean4export`, in that order).

CONFIG is the comparator's JSON (`theorem_names`, `permitted_axioms`); its module and kernel
fields are not used here. Prints "Your solution is okay!" and exits 0 when every check passes.
-/
import Lean
import Comparator
import Export.Parse

open Lean

def primitiveTargets : Array Name := #[
    ``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.pow, ``Nat.gcd, ``Nat.div, ``Nat.mod, ``Nat.beq,
    ``Nat.ble, ``Nat.land, ``Nat.lor, ``Nat.xor, ``Nat.shiftLeft, ``Nat.shiftRight,
    ``String.ofList, ``Char.ofNat, ``List, ``eagerReduce, ``Nat, ``String, ``String.mk, ``Char,
    ``optParam, ``autoParam, ``semiOutParam, ``outParam]

def runBuiltinKernel (solution : Export.ExportedEnv) : IO (Option String) := do
  IO.println "Running Lean default kernel on solution."
  let env ← Lean.mkEmptyEnvironment
  let mut kernelEnv := env.toKernelEnv
  let origConstMap := solution.constMap
  let quotTargets := [`Quot.mk, `Quot.lift, `Quot.ind]
  let kernelConstMap := quotTargets.foldl (init := origConstMap) (·.erase ·)
  try
    kernelEnv ← kernelEnv.replay kernelConstMap
    IO.println "Lean default kernel accepts the solution"
  catch e =>
    IO.println "Lean default kernel rejects the solution"
    return some e.toString
  try
    let verifyTargets := `Quot :: quotTargets
    for quotTarget in verifyTargets do
      if let some info := origConstMap[quotTarget]? then
        let some info' := kernelEnv.find? quotTarget |
          throw <| .userError s!"Could not find quotient constant in final kernel env: {quotTarget}"
        if info != info' then
          throw <| .userError s!"Quotient constant mismatch on: {quotTarget}"
    return none
  catch e =>
    IO.println "Quotient post-check rejects the solution"
    return some e.toString

def parseFile (p : System.FilePath) : IO Export.ExportedEnv := do
  let h ← IO.FS.Handle.mk p .read
  Export.parseStream (IO.FS.Stream.ofHandle h)

def names (j : Json) (field : String) : Except String (Array Name) := do
  let a ← j.getObjValAs? (Array String) field
  return a.map fun s => (Syntax.decodeNameLit ("`" ++ s)).getD s.toName

def main (args : List String) : IO UInt32 := do
  let [cfg, chal, sol] := args
    | IO.eprintln "usage: compare-exports CONFIG CHALLENGE_EXPORT SOLUTION_EXPORT"; return 2
  let j ← IO.ofExcept <| Json.parse (← IO.FS.readFile cfg)
  let theorems ← IO.ofExcept <| names j "theorem_names"
  let axioms ← IO.ofExcept <| names j "permitted_axioms"
  IO.println s!"Parsing the challenge's export"
  let challenge ← parseFile chal
  IO.println s!"Parsing the solution's export"
  let solution ← parseFile sol
  IO.println s!"Comparing ({theorems.size} theorems, {axioms.size} permitted axioms)"
  try
    IO.ofExcept <| Comparator.compareAt challenge solution (theorems ++ axioms) #[] primitiveTargets
    IO.ofExcept <| Comparator.checkAxioms solution theorems #[] axioms
    IO.println "The statements match and the solution uses only the permitted axioms"
  catch e =>
    IO.println s!"Error: {e}"
    return 1
  if let some err ← runBuiltinKernel solution then
    IO.println s!"Error: {err}"
    return 1
  IO.println "Your solution is okay!"
  return 0
