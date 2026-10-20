/-
The trusted part of this repository's proofs, as hashes, for `fingerprint.py` (run it
through that; not part of the lakefile):

    lake env lean --run .claude/skills/proof-perf/fingerprint.lean [--part=ROOT]... MODULE...

The roots are the theorems declared in the given modules (every `Link` and `Results`
module, as `etc/tcb-report.lean`'s).  One tab-separated line per constant, sorted:

  root  NAME  HASH   a root theorem: its statement (type)
  def   NAME  HASH   a definition, inductive, constructor, opaque or recursor of this
                     repository (`Code.*`, `GeneratedProof.*`, `Spec.*`, `Proof.*`, and
                     the parts' `ROOT.*`) that some root's statement reaches, through
                     types and definition bodies (not proofs): its kind, type and body
  axiom NAME  HASH   every axiom declared in this repository's modules: its type

A hash is Lean's structural `Expr.hash` (binder names and binder info are not part of
it, which a statement's meaning does not depend on either).  A change to a proof changes
no line; a change to what a result says, to a definition it is written in terms of, or to
an axiom, changes one.
-/
import Lean
open Lean

def modOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i.toNat]!
  | none => .anonymous

/-- Whether `n` is declared in this repository: the Goose translations, the specs and
proofs, and the same under each part root. -/
def isRepo (parts : List Name) (env : Environment) (n : Name) : Bool :=
  let r := (modOf env n).getRoot
  r == `Code || r == `GeneratedProof || r == `Spec || r == `Proof || parts.contains r

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor" | .recInfo _ => "rec"

/-- A constant's meaning: its kind, universe parameters, type, and body if it is a
definition; an inductive's constructors. -/
def meaningHash (ci : ConstantInfo) : UInt64 :=
  let h := mixHash (hash (kindOf ci)) (mixHash (hash ci.levelParams) ci.type.hash)
  match ci with
  | .defnInfo d => mixHash h d.value.hash
  | .opaqueInfo d => mixHash h d.value.hash
  | .inductInfo d => mixHash h (hash d.ctors)
  | _ => h

/-- The constants a constant's meaning is made of (as `etc/tcb-report.lean`'s
`meaningDeps`). -/
def meaningDeps (ci : ConstantInfo) : Array Name :=
  let s := ci.type.getUsedConstants
  match ci with
  | .defnInfo d => s ++ d.value.getUsedConstants
  | .opaqueInfo d => s ++ d.value.getUsedConstants
  | .inductInfo d => s ++ d.ctors.toArray
  | .ctorInfo d => s.push d.induct
  | _ => s

def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let parts : List Name := args.filterMap fun a =>
    (a.dropPrefix? "--part=").map (·.toString.toName)
  let mods : Array Name := (args.filter (!·.startsWith "--")).toArray.map String.toName
  if mods.isEmpty then
    IO.eprintln "usage: fingerprint.lean [--part=ROOT]... MODULE..."
    return 2
  let env ← importModules (mods.map fun m => { module := m }) {}
  let mut lines : Array String := #[]
  let mut todo : Array Name := #[]
  for (n, ci) in env.constants.map₁.toList do
    if mods.contains (modOf env n) && ci matches .thmInfo _ && !n.isInternalDetail then
      lines := lines.push s!"root\t{n}\t{ci.type.hash}"
      todo := todo ++ ci.type.getUsedConstants
    if ci matches .axiomInfo _ && isRepo parts env n then
      lines := lines.push s!"axiom\t{n}\t{meaningHash ci}"
  let mut seen : NameSet := {}
  while todo.size > 0 do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    if !isRepo parts env n then continue
    let some ci := env.find? n | continue
    if ci matches .thmInfo _ || ci matches .axiomInfo _ then continue
    lines := lines.push s!"def\t{n}\t{meaningHash ci}"
    todo := todo ++ meaningDeps ci
  let out ← IO.getStdout
  for l in lines.qsort (· < ·) do
    out.putStrLn l
  return 0
