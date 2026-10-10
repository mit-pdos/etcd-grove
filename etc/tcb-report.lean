/-
Trust base of this repository's proofs.  Not part of the lakefile; run with

    lake env lean --run etc/tcb-report.lean [--part=ROOT]... MODULE...  > tcb.json

(normally via `etc/tcb-report.py` and `etc/verified-code.py`, through
`etc/proof_roots.py`, which choose the modules: every `Link` and `Results` module, in
groups that can be imported together).  The roots are the theorems declared in the
given modules.  This repository's own declarations are those of the modules `Spec.*`,
`Proof.*` and, for each `--part=ROOT` (a module root of a project's part, as
`etc/goose.py` configures), `ROOT.Spec.*` and `ROOT.Proof.*`.

For each root it computes what `#print axioms` computes -- the axioms its proof transitively depends on -- and, in addition, which
declarations along the way contain a `sorry` themselves (`#print axioms` only says
`sorryAx`).  One JSON object per line:

  {"t":"root", ...}   a root theorem: name, module, line, axioms (every axiom it
                      depends on, `sorryAx` included), sorries (the declarations
                      containing a `sorry` that it depends on), uses (the other
                      roots its proof uses: a linked result uses its callees'),
                      defs (this repository's definitions its *statement* is
                      written in terms of, transitively through their bodies)
  {"t":"axiom", ...}  every axiom some root depends on: name, module, line, doc
  {"t":"sorry", ...}  every declaration containing a `sorry` some root depends on:
                      name, module, line, synthetic (an elaboration error)
  {"t":"def", ...}    every definition in some root's `defs`: name, module, line,
                      endLine, kind
-/
import Lean
open Lean

def jstr (s : String) : String := (Json.str s).compress

def modOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i.toNat]!
  | none => .anonymous

/-- The user-facing declaration an auxiliary constant (`_proof_n`, `match_n`, a
private name, ...) belongs to: the nearest enclosing constant with a source range. -/
partial def rootOf (env : Environment) (n : Name) (user := true) : Name × Nat :=
  let rec go (m : Name) : Option (Name × Nat) :=
    match m with
    | .anonymous => none
    | _ =>
      let here := if (env.find? m).isSome then
          (declRangeExt.find? env m (level := .private)) else none
      match here with
      | some r => some (m, r.range.pos.line)
      | none => go m.getPrefix
  let un (m : Name) := if user then privateToUserName m else m
  match go n with
  | some (m, l) => (un m, l)
  | none => (un n, 0)

def ciExprs (ci : ConstantInfo) : List Expr :=
  ci.type :: (match ci.value? (allowOpaque := true) with | some v => [v] | none => [])

def hasSyntheticSorry (e : Expr) : Bool :=
  (e.find? fun e => e.isAppOfArity ``sorryAx 2 && e.appArg! == mkConst ``Bool.true).isSome

/-- What a constant's trust base is made of: the axioms it depends on and the
constants containing a `sorry` it depends on (as `.inl` / `.inr`). -/
abbrev Item := Name ⊕ Name

/-- Memoized transitive closure of `Item`s (iterative DFS; a constant on a cycle sees
the partial result, as in `collectAxioms`). -/
partial def closure (env : Environment) (roots : Array Name) :
    IO (Std.HashMap Name (Array Item)) := do
  let mut memo : Std.HashMap Name (Array Item) := {}
  let mut onStack : NameSet := {}
  for r in roots do
    if memo.contains r then continue
    let mut stack : Array (Name × Bool) := #[(r, false)]
    while stack.size > 0 do
      let (n, expanded) := stack.back!
      if memo.contains n then
        stack := stack.pop; continue
      match env.find? n with
      | none => memo := memo.insert n #[]; stack := stack.pop
      | some ci =>
        let deps := ci.getUsedConstantsAsSet
        if !expanded then
          stack := stack.set! (stack.size - 1) (n, true)
          onStack := onStack.insert n
          for d in deps do
            if !memo.contains d && !onStack.contains d then
              stack := stack.push (d, false)
        else
          let mut acc : Array Item := #[]
          if ci matches .axiomInfo _ then acc := acc.push (.inl n)
          if deps.contains ``sorryAx then acc := acc.push (.inr n)
          for d in deps do
            for a in memo.getD d #[] do
              if !acc.contains a then acc := acc.push a
          memo := memo.insert n acc
          onStack := onStack.erase n
          stack := stack.pop
  return memo

/-- Whether `n` is declared in this repository's specs and proofs: `Spec.*`, `Proof.*`,
and `ROOT.Spec.*`, `ROOT.Proof.*` for the part roots `parts`. -/
def isProject (parts : List Name) (env : Environment) (n : Name) : Bool :=
  let m := modOf env n
  let r := m.getRoot
  r == `Spec || r == `Proof ||
    parts.any fun p => (p ++ `Spec).isPrefixOf m || (p ++ `Proof).isPrefixOf m

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor" | .recInfo _ => "rec"

/-- The constants a constant's meaning is made of: its type, and its body if it is a
definition (not a proof); an inductive's constructors. -/
def meaningDeps (ci : ConstantInfo) : NameSet :=
  let s := ci.type.getUsedConstantsAsSet
  match ci with
  | .defnInfo d => d.value.getUsedConstants.foldl (·.insert ·) s
  | .opaqueInfo d => d.value.getUsedConstants.foldl (·.insert ·) s
  | .inductInfo d => d.ctors.foldl (·.insert ·) s
  | .ctorInfo d => s.insert d.induct
  | _ => s

/-- This repository's definitions a statement is written in terms of: the closure of
`meaningDeps` from the statement, not descending outside this repository (the
framework is trusted as a whole) or into proofs. -/
partial def statementDefs (parts : List Name) (env : Environment) (stmt : Expr) :
    NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo : Array Name := stmt.getUsedConstants
  while todo.size > 0 do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n || !isProject parts env n then continue
    let some ci := env.find? n | continue
    if ci matches .thmInfo _ then continue
    seen := seen.insert n
    for d in meaningDeps ci do
      if !seen.contains d then todo := todo.push d
  -- auxiliary constants (`match_n`, `_proof_n`, equation lemmas, …) count as part of
  -- the declaration they belong to; private names are kept (printed by `etc/tcb-report.py`)
  return seen.toList.foldl (init := {}) fun acc n => acc.insert (rootOf env n (user := false)).1

def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let parts : List Name := args.filterMap fun a =>
    (a.dropPrefix? "--part=").map (·.toString.toName)
  let mods : Array Name :=
    (args.filter (!·.startsWith "--")).toArray.map String.toName
  if mods.isEmpty then
    IO.eprintln "usage: etc/tcb-report.lean [--part=ROOT]... MODULE..."
    return 2
  let env ← importModules (mods.map fun m => { module := m }) {}
  let mut roots : Array Name := #[]
  for (n, ci) in env.constants.map₁.toList do
    if mods.contains (modOf env n) && ci matches .thmInfo _ && !n.isInternalDetail then
      roots := roots.push n
  roots := roots.qsort (·.toString < ·.toString)
  IO.eprintln s!"tcb: {roots.size} root theorems in {mods.toList}"
  let memo ← closure env roots
  let out ← IO.getStdout
  let mut axioms : NameSet := {}
  let mut sorries : Std.HashMap Name (Name × Nat × Bool) := {}
  let mut defs : NameSet := {}
  let rootSet : NameSet := roots.foldl (·.insert ·) {}
  for r in roots do
    let items := memo.getD r #[]
    let mut axs : Array String := #[]
    let mut srs : Array String := #[]
    for it in items do
      match it with
      | .inl a => axioms := axioms.insert a; axs := axs.push a.toString
      | .inr s =>
        let (u, line) := rootOf env s
        let synth := match env.find? s with
          | some ci => (ciExprs ci).any hasSyntheticSorry | none => false
        let prev := (sorries.get? u).map (·.2.2) |>.getD false
        sorries := sorries.insert u (modOf env s, line, prev || synth)
        if !srs.contains u.toString then srs := srs.push u.toString
    let line := match declRangeExt.find? env r with | some d => d.range.pos.line | none => 0
    let some rci := env.find? r | continue
    let uses := ((rci.value? (allowOpaque := true)).map (·.getUsedConstants) |>.getD #[]).filter
      (fun d => rootSet.contains d && d != r)
    let sd := statementDefs parts env rci.type
    defs := sd.toList.foldl (init := defs) (·.insert ·)
    let jl (a : Array Name) := ",".intercalate (a.toList.map (jstr ·.toString))
    out.putStrLn s!"\{\"t\":\"root\",\"name\":{jstr r.toString},\"module\":{jstr (modOf env r).toString},\"line\":{line},\"axioms\":[{",".intercalate (axs.toList.map jstr)}],\"sorries\":[{",".intercalate (srs.toList.map jstr)}],\"uses\":[{jl uses}],\"defs\":[{jl sd.toList.toArray}]}"
  for a in axioms.toList do
    let line := match declRangeExt.find? env a (level := .private) with
      | some d => d.range.pos.line | none => 0
    let doc := (← findDocString? env a).getD ""
    out.putStrLn s!"\{\"t\":\"axiom\",\"name\":{jstr a.toString},\"module\":{jstr (modOf env a).toString},\"line\":{line},\"doc\":{jstr doc}}"
  for (s, (m, line, synth)) in sorries.toList do
    out.putStrLn s!"\{\"t\":\"sorry\",\"name\":{jstr s.toString},\"module\":{jstr m.toString},\"line\":{line},\"synthetic\":{synth}}"
  for d in defs.toList do
    let some ci := env.find? d | continue
    let (l0, l1) := match declRangeExt.find? env d (level := .private) with
      | some r => (r.range.pos.line, r.range.endPos.line) | none => (0, 0)
    out.putStrLn s!"\{\"t\":\"def\",\"name\":{jstr d.toString},\"module\":{jstr (modOf env d).toString},\"line\":{l0},\"endLine\":{l1},\"kind\":{jstr (kindOf ci)}}"
  return 0
