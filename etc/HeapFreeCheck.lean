/-
**The heap-free gate** of phase 7 S2's service table (`notes/phase7-plan.md`, O2; #24, 2026-11-23):
the specs a service table holds (`etcd*SpecW`, ...) and the vocabulary they are written in depend on
no machine's heap. Run by `etc/heapfree-check.py`:

    lake env lean --run etc/HeapFreeCheck.lean MODULE,MODULE,... NAME... [-- NEG...]

Imports the modules, walks every constant reachable from each `NAME` (types and definition
bodies, through every constant, theorems' statements included), and prints each reachable
constant whose type mentions `Perennial.HeapGS` or `Perennial.GooseLocalGS`, with the path from
its root; each `NEG` (a negative test: a definition known to need the heap) must be reported.
Exits 1 on a reachable heap constant or a missed negative test.
-/
import Lean
open Lean

def mentionsHeap (e : Expr) : Bool :=
  (e.find? fun x => match x with
    | .const n _ => n == `Perennial.HeapGS || n == `Perennial.GooseLocalGS
    | _ => false).isSome

/-- The heap constants reachable from `root`, each with its parent on the path. -/
def heapReach (env : Environment) (root : Name) : Array (Name × Name) := Id.run do
  let mut seen : NameSet := {}
  let mut todo : Array (Name × Name) := #[(root, root)]
  let mut out := #[]
  while h : todo.size > 0 do
    let (n, p) := todo.back
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    if mentionsHeap ci.type then
      out := out.push (n, p)
      continue
    let val? := match ci with
      | .defnInfo d => some d.value
      | .opaqueInfo d => some d.value
      | _ => none
    for c in ci.type.getUsedConstants ++ ((val?.map (·.getUsedConstants)).getD #[]) do
      unless seen.contains c do todo := todo.push (c, n)
  return out

def main (args : List String) : IO UInt32 := do
  let mods := (args.head!.splitOn ",").map (·.toName)
  let rest := args.tail!
  let roots := (rest.takeWhile (· != "--")).map (·.toName)
  let negs := ((rest.dropWhile (· != "--")).drop 1).map (·.toName)
  initSearchPath (← findSysroot)
  let env ← importModules (mods.map fun m => { module := m }).toArray {}
  let mut bad := false
  for r in roots do
    if (env.find? r).isNone then
      IO.println s!"MISSING {r}"; bad := true; continue
    for (n, p) in heapReach env r do
      IO.println s!"HEAP {r}: {n} (used by {p})"; bad := true
  for r in negs do
    if (heapReach env r).isEmpty then
      IO.println s!"NEGATIVE TEST MISSED {r}"; bad := true
  return if bad then 1 else 0
