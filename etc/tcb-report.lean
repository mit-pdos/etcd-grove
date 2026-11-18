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
  {"t":"errorf", ...} every constant some root depends on that steps into Perennial's
                      model of `fmt.Errorf` itself (see `isErrorfStep`): name, user (the
                      declaration it belongs to), module, line; a root's `errorf` lists
                      those it depends on (read by `etc/errorf-wrap-check.py`)
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

/-- What a constant's trust base is made of: the axioms it depends on, the constants
containing a `sorry` it depends on, and the constants stepping into Perennial's `fmt.Errorf`
model it depends on (`isErrorfStep`; not trust base, but a model step to review). -/
inductive Item where
  | ax (n : Name)
  | sorry (n : Name)
  | errorf (n : Name)
  deriving Inhabited, BEq, Hashable

def Item.tag : Item → Nat
  | .ax _ => 0 | .sorry _ => 1 | .errorf _ => 2

def Item.name : Item → Name
  | .ax n | .sorry n | .errorf n => n

/-- An `Item`'s order, for the sorted arrays that represent sets of them. -/
def Item.lt (a b : Item) : Bool :=
  a.tag < b.tag || (a.tag == b.tag && Name.quickLt a.name b.name)

/-- The union of two sorted, duplicate-free arrays of `Item`s. -/
def mergeItems (a b : Array Item) : Array Item := Id.run do
  let mut out : Array Item := Array.mkEmpty (a.size + b.size)
  let mut i := 0
  let mut j := 0
  while i < a.size || j < b.size do
    if j ≥ b.size then out := out.push a[i]!; i := i + 1
    else if i ≥ a.size then out := out.push b[j]!; j := j + 1
    else if Item.lt a[i]! b[j]! then out := out.push a[i]!; i := i + 1
    else if Item.lt b[j]! a[i]! then out := out.push b[j]!; j := j + 1
    else out := out.push a[i]!; i := i + 1; j := j + 1
  return out

/-- The sets of `Item`s met so far, interned: almost every constant reaches the same few
thousand axioms (Goose's untranslated types among them), so the distinct sets are few
and a union of two of them is computed once. -/
structure Interned where
  sets : Array (Array Item) := #[#[]]
  ids : Std.HashMap (Array Item) Nat := ({} : Std.HashMap (Array Item) Nat).insert #[] 0
  unions : Std.HashMap (Nat × Nat) Nat := {}

def Interned.intern (t : Interned) (s : Array Item) : Interned × Nat :=
  match t.ids.get? s with
  | some i => (t, i)
  | none => ({ t with sets := t.sets.push s, ids := t.ids.insert s t.sets.size }, t.sets.size)

def Interned.union (t : Interned) (a b : Nat) : Interned × Nat :=
  if a == b || b == 0 then (t, a) else if a == 0 then (t, b) else
  let k := if a < b then (a, b) else (b, a)
  match t.unions.get? k with
  | some u => (t, u)
  | none =>
    let (t, u) := t.intern (mergeItems t.sets[a]! t.sets[b]!)
    ({ t with unions := t.unions.insert k u }, u)

/-! **Steps into Perennial's model of `fmt.Errorf`** (the term-level errorf gate, 2026-11-18,
replacing a text search). Perennial's model of `fmt.Errorf` is `errors.New(format)` (`%w` and the
arguments' formatting methods not modelled). A proof that steps into it (`wp_start`/`wp_apply` on a
call of `@! fmt.Errorf`, or a hand-written `func_unfold`) needs `#(functions "fmt.Errorf" []) =
fmt.Errorf.impl`, which only the `FuncUnfold` instance `fmt.Assumptions.Errorf_unfold` (a field of
the class `fmt.Assumptions`) gives: `functions` is uninterpreted otherwise. So its proof term
mentions one of `errorfAtoms` (the field's projection; the model's body `fmt.Errorf.impl`, which
the instance's type names; the class's recursors), or a raw `Expr.proj` of the class at the
field's index. Such a constant is an errorf step unless it is the class's own (declared in
Perennial's generated `fmt` module) or sanctioned
(Perennial's `fmt.Errorf.wp_proof`: its post is some `Error()` string, its premise `ArgsWf`, no
argument an error or with methods, so its statement is true of Go); a sanctioned constant's steps
are not propagated. `etc/errorf-wrap-check.py` fails on a step outside its reviewed modules. -/

def errorfCls : Name := `Perennial.fmt.Assumptions
def errorfField : Name := `Perennial.fmt.Assumptions.Errorf_unfold

def errorfAtoms : NameSet := ({} : NameSet)
  |>.insert errorfField
  |>.insert `Perennial.fmt.Errorf.impl
  |>.insert (errorfCls ++ `rec) |>.insert (errorfCls ++ `casesOn) |>.insert (errorfCls ++ `recOn)

def errorfSanctioned : NameSet := ({} : NameSet)
  |>.insert `Perennial.fmt.Errorf.wp_proof

/-- The field's index among the class's fields (for a raw `Expr.proj`). -/
def errorfFieldIdx (env : Environment) : Option Nat :=
  (getStructureFields env errorfCls).idxOf? `Errorf_unfold

def errorfRawProj (idx : Option Nat) (ci : ConstantInfo) : Bool :=
  match idx with
  | none => false
  | some i => (ciExprs ci).any fun e =>
      (e.find? fun e => match e with
        | .proj s j _ => s == errorfCls && j == i
        | _ => false).isSome

/-- The class's own constants (its projections, constructor, recursors), declared with it in
Perennial's generated `fmt` module: only those are exempt, not anything named under it elsewhere. -/
def isErrorfClsOwn (env : Environment) (n : Name) : Bool :=
  errorfCls.isPrefixOf n && modOf env n == modOf env errorfCls

def isErrorfStep (env : Environment) (idx : Option Nat) (n : Name) (ci : ConstantInfo)
    (deps : NameSet) : Bool :=
  !errorfAtoms.contains n && !errorfSanctioned.contains n && !isErrorfClsOwn env n &&
    (deps.any (errorfAtoms.contains ·) || errorfRawProj idx ci)

/-- Memoized transitive closure of `Item`s (iterative DFS; a constant on a cycle sees
the partial result, as in `collectAxioms`). Each constant's set is an interned id. -/
partial def closure (env : Environment) (roots : Array Name) :
    IO (Std.HashMap Name (Array Item)) := do
  let mut memo : Std.HashMap Name Nat := {}
  let mut onStack : NameSet := {}
  let mut t : Interned := {}
  let idx := errorfFieldIdx env
  for r in roots do
    if memo.contains r then continue
    -- a constant's dependencies are computed once, when it is first expanded (walking a
    -- proof term is the closure's main cost), and kept on the stack until it is finished
    let mut stack : Array (Name × Option NameSet) := #[(r, none)]
    while stack.size > 0 do
      let (n, expanded) := stack.back!
      if memo.contains n then
        stack := stack.pop; continue
      match expanded with
      | none =>
        match env.find? n with
        | none => memo := memo.insert n 0; stack := stack.pop
        | some ci =>
          let deps := ci.getUsedConstantsAsSet
          stack := stack.set! (stack.size - 1) (n, some deps)
          onStack := onStack.insert n
          for d in deps do
            if !memo.contains d && !onStack.contains d then
              stack := stack.push (d, none)
      | some deps =>
        let ci := (env.find? n).get!
        let isAx := match ci with | .axiomInfo _ => true | _ => false
        let mut own : Array Item := #[]
        if isAx then own := own.push (.ax n)
        if deps.contains ``sorryAx then own := own.push (.sorry n)
        if isErrorfStep env idx n ci deps then own := own.push (.errorf n)
        let (t', i0) := t.intern own
        t := t'
        let mut acc := i0
        for d in deps do
          let (t', u) := t.union acc (memo.getD d 0)
          t := t'
          acc := u
        if errorfSanctioned.contains n then
          let (t', u) := t.intern (t.sets[acc]!.filter (·.tag != 2))
          t := t'
          acc := u
        memo := memo.insert n acc
        onStack := onStack.erase n
        stack := stack.pop
  IO.eprintln s!"tcb: {t.sets.size} distinct trust bases, {t.unions.size} unions"
  return roots.foldl (init := {}) fun m r => m.insert r t.sets[memo.getD r 0]!

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

/-- `statementDefs`' view of a constant, shared by all roots: `none` if the walk does not
enter it (outside this repository, a theorem, unknown), else the constants of its
meaning (`meaningDeps`) and the declaration it belongs to (`rootOf`). -/
abbrev DefCache := Std.HashMap Name (Option (Array Name × Name))

/-- This repository's definitions a statement is written in terms of: the closure of
`meaningDeps` from the statement, not descending outside this repository (the
framework is trusted as a whole) or into proofs. -/
partial def statementDefs (parts : List Name) (env : Environment) (stmt : Expr)
    (cache : DefCache) : NameSet × DefCache := Id.run do
  let mut cache := cache
  let mut seen : NameSet := {}
  let mut out : NameSet := {}
  let mut todo : Array Name := stmt.getUsedConstants
  while todo.size > 0 do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let entry ← match cache.get? n with
      | some e => pure e
      | none =>
        let e := if !isProject parts env n then none else
          match env.find? n with
          | none | some (.thmInfo _) => none
          | some ci => some ((meaningDeps ci).toList.toArray, (rootOf env n (user := false)).1)
        cache := cache.insert n e
        pure e
    let some (deps, r) := entry | continue
    -- auxiliary constants (`match_n`, `_proof_n`, equation lemmas, …) count as part of
    -- the declaration they belong to; private names are kept (printed by `etc/tcb-report.py`)
    out := out.insert r
    for d in deps do
      if !seen.contains d then todo := todo.push d
  return (out, cache)

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
  -- the given modules' own theorems, from their module data (walking every constant of the
  -- environment took most of a run's time outside the closure); a constant listed in a
  -- module's data but attributed to another (a `congr_simp` lemma realized in both) is the
  -- other's
  let mut roots : Array Name := #[]
  for i in [0:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    if mods.contains m then
      for n in env.header.moduleData[i]!.constNames do
        if let some ci := env.find? n then
          if ci matches .thmInfo _ && !n.isInternalDetail && modOf env n == m then
            roots := roots.push n
  roots := roots.qsort (·.toString < ·.toString)
  IO.eprintln s!"tcb: {roots.size} root theorems in {mods.toList}"
  let memo ← closure env roots
  let out ← IO.getStdout
  let mut axioms : NameSet := {}
  let mut sorries : Std.HashMap Name (Name × Nat × Bool) := {}
  let mut defs : NameSet := {}
  let mut errorfs : NameSet := {}
  let mut defCache : DefCache := {}
  let rootSet : NameSet := roots.foldl (·.insert ·) {}
  for r in roots do
    let items := memo.getD r #[]
    let mut axs : Array String := #[]
    let mut srs : Array String := #[]
    let mut efs : Array String := #[]
    for it in items do
      match it with
      | .ax a => axioms := axioms.insert a; axs := axs.push a.toString
      | .errorf c => errorfs := errorfs.insert c; efs := efs.push c.toString
      | .sorry s =>
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
    let (sd, dc) := statementDefs parts env rci.type defCache
    defCache := dc
    defs := sd.toList.foldl (init := defs) (·.insert ·)
    let jl (a : Array Name) := ",".intercalate (a.toList.map (jstr ·.toString))
    out.putStrLn s!"\{\"t\":\"root\",\"name\":{jstr r.toString},\"module\":{jstr (modOf env r).toString},\"line\":{line},\"axioms\":[{",".intercalate (axs.toList.map jstr)}],\"sorries\":[{",".intercalate (srs.toList.map jstr)}],\"uses\":[{jl uses}],\"defs\":[{jl sd.toList.toArray}],\"errorf\":[{",".intercalate (efs.toList.map jstr)}]}"
  for a in axioms.toList do
    let line := match declRangeExt.find? env a (level := .private) with
      | some d => d.range.pos.line | none => 0
    let doc := (← findDocString? env a).getD ""
    out.putStrLn s!"\{\"t\":\"axiom\",\"name\":{jstr a.toString},\"module\":{jstr (modOf env a).toString},\"line\":{line},\"doc\":{jstr doc}}"
  for (s, (m, line, synth)) in sorries.toList do
    out.putStrLn s!"\{\"t\":\"sorry\",\"name\":{jstr s.toString},\"module\":{jstr m.toString},\"line\":{line},\"synthetic\":{synth}}"
  for c in errorfs.toList do
    let (u, line) := rootOf env c
    out.putStrLn s!"\{\"t\":\"errorf\",\"name\":{jstr c.toString},\"user\":{jstr u.toString},\"module\":{jstr (modOf env c).toString},\"line\":{line}}"
  for d in defs.toList do
    let some ci := env.find? d | continue
    let (l0, l1) := match declRangeExt.find? env d (level := .private) with
      | some r => (r.range.pos.line, r.range.endPos.line) | none => (0, 0)
    out.putStrLn s!"\{\"t\":\"def\",\"name\":{jstr d.toString},\"module\":{jstr (modOf env d).toString},\"line\":{l0},\"endLine\":{l1},\"kind\":{jstr (kindOf ci)}}"
  -- exit without freeing the environment (tearing it down took a minute of the largest run)
  out.flush
  IO.Process.exit 0
