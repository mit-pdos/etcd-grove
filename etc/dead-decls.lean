/-
Which of this repository's declarations the results use.  Not part of the lakefile; run
with

    lake env lean --run etc/dead-decls.lean [--part=ROOT]... MODULE...

(normally via `etc/dead-decls.py`, which chooses the modules as `etc/tcb-report.py` does:
every `Link` and `Results` module, in groups that can be imported together).  The roots
are the theorems declared in the given modules: a `Link` module's (the linked results)
and a `Results` module's.  A constant is used if a root's statement or proof reaches it,
through statements, definition bodies and proofs.

One JSON object per line, for every user-facing declaration of this repository (an
auxiliary constant -- `_proof_n`, `match_n`, an equation lemma -- counts as the
declaration it belongs to) in the imported modules:

  {"name", "module", "line", "endLine", "kind", "link", "results"}

`link`/`results`: whether a `Link`/`Results` root reaches it.  `kind` is `meta` for a
declaration of the tactic framework (a macro, a syntax, an elaborator: used while
elaborating, never in a term).
-/
import Lean
open Lean

def jstr (s : String) : String := (Json.str s).compress

def modOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i.toNat]!
  | none => .anonymous

/-- The declaration an auxiliary constant belongs to: the nearest enclosing constant with a
source range (as `etc/tcb-report.lean`'s `rootOf`, private names kept). -/
partial def ownerOf (env : Environment) (n : Name) (m : Name := modOf env n) : Option Name :=
  match n with
  | .anonymous => none
  | _ =>
    if (env.find? n).isSome && modOf env n == m &&
        (declRangeExt.find? env n (level := .private)).isSome then
      some n
    else ownerOf env n.getPrefix m

def isProject (parts : List Name) (env : Environment) (n : Name) : Bool :=
  let m := modOf env n
  let r := m.getRoot
  r == `Spec || r == `Proof ||
    parts.any fun p => (p ++ `Spec).isPrefixOf m || (p ++ `Proof).isPrefixOf m

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor" | .recInfo _ => "rec"

def metaHeads : List Name :=
  [`Lean.Syntax, `Lean.Macro, `Lean.ParserDescr, `Lean.TrailingParserDescr,
   `Lean.Elab.Tactic.Tactic, `Lean.Elab.Term.TermElab, `Lean.Elab.Command.CommandElab,
   `Lean.MacroM, `Lean.Elab.TermElabM, `Lean.Elab.Tactic.TacticM, `Lean.Meta.MetaM,
   `Lean.Elab.Command.CommandElabM, `Lean.CoreM, `Lean.Meta.Simp.Simproc,
   `Lean.Meta.Simp.DSimproc, `Lean.Name]

def isMeta (ci : ConstantInfo) : Bool :=
  ci.type.getUsedConstants.any (metaHeads.contains ·)

/-- The constants reached from `roots`: their types, values (proofs included) and, for an
inductive, its constructors. -/
def reach (env : Environment) (roots : Array Name) : NameHashSet := Id.run do
  let mut seen : NameHashSet := {}
  let mut todo := roots
  while todo.size > 0 do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    let mut deps := ci.getUsedConstantsAsSet
    if let .inductInfo d := ci then deps := d.ctors.foldl (·.insert ·) deps
    if let .ctorInfo d := ci then deps := deps.insert d.induct
    for d in deps do
      if !seen.contains d then todo := todo.push d
  return seen

def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let parts : List Name := args.filterMap fun a =>
    (a.dropPrefix? "--part=").map (·.toString.toName)
  let mods : Array Name :=
    (args.filter (!·.startsWith "--")).toArray.map String.toName
  if mods.isEmpty then
    IO.eprintln "usage: etc/dead-decls.lean [--part=ROOT]... MODULE..."
    return 2
  let env ← importModules (mods.map fun m => { module := m }) {}
  let mut linkRoots : Array Name := #[]
  let mut resRoots : Array Name := #[]
  for (n, ci) in env.constants.map₁.toList do
    let m := modOf env n
    if mods.contains m && ci matches .thmInfo _ then
      if m.getString! == "Link" then linkRoots := linkRoots.push n
      else resRoots := resRoots.push n
  IO.eprintln s!"dead-decls: {linkRoots.size} Link roots, {resRoots.size} Results roots"
  let rl := reach env linkRoots
  let rr := reach env resRoots
  -- the user-facing declarations, with whether each root kind reaches one of its constants
  let mut decls : Std.HashMap Name (Bool × Bool) := {}
  for (n, _) in env.constants.map₁.toList do
    if !isProject parts env n then continue
    let some o := ownerOf env n | continue
    let (a, b) := decls.getD o (false, false)
    decls := decls.insert o (a || rl.contains n, b || rr.contains n)
  let out ← IO.getStdout
  for (d, (a, b)) in decls.toList do
    let some ci := env.find? d | continue
    let (l0, l1) := match declRangeExt.find? env d (level := .private) with
      | some r => (r.range.pos.line, r.range.endPos.line) | none => (0, 0)
    let kind := if isMeta ci then "meta" else kindOf ci
    out.putStrLn s!"\{\"name\":{jstr d.toString},\"module\":{jstr (modOf env d).toString},\"line\":{l0},\"endLine\":{l1},\"kind\":{jstr kind},\"link\":{a},\"results\":{b}}"
  return 0
