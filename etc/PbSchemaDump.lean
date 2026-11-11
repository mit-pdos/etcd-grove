/-
**The registered protobuf schemas, dumped for the descriptor check** (per-type message models,
stage A, `[v6a]` 1 and 6; `etc/pbschema-check.py`). Not part of the lakefile; run with

    lake env lean --run etc/PbSchemaDump.lean MODULE...

on the modules declaring the registrations (`pbModelOf … = some …`). It prints, one per line:

- `root <Go type>`: the key of each `pbModelOf` registration (the message types whose wire content
  the trust boundary models: their schemas are trusted, `PbSchema.lean`'s header);
- `schema <Go type> <num>:<wt>,<wt> ...`: `pbSchemaOf`'s table, read from its definition (its
  `if ty = X.ty then S else ...` chain), each schema constant's list literal evaluated;
- `uses <registration> <schema constant>`: every `FieldSchema` constant the registered instance's
  definition reaches (through this repository's definitions), which must be one of `pbSchemaOf`'s.

A Go type is printed as its last two name components (`raftpb.Entry`), the protobuf full name of
the generated message. The Go side (`examples/pbschema`) walks each root's `protoreflect`
descriptor and compares.
-/
import Lean
open Lean

def lastTwo (n : Name) : String :=
  -- `go_etcd_io.raft.v3.raftpb.Entry.ty` → `raftpb.Entry`
  let n := if n.getString! == "ty" then n.getPrefix else n
  s!"{n.getPrefix.getString!}.{n.getString!}"

partial def natLit? (e : Expr) : Option Nat :=
  match e.consumeMData with
  | .lit (.natVal n) => some n
  | e' =>
    if e'.isAppOfArity ``OfNat.ofNat 3 then natLit? (e'.getArg! 1)
    else none

partial def listLit? (e : Expr) : Option (List Expr) :=
  let e := e.consumeMData
  if e.isAppOfArity ``List.nil 1 then some []
  else if e.isAppOfArity ``List.cons 3 then
    (listLit? (e.getArg! 2)).map (e.getArg! 1 :: ·)
  else none

def schemaLit? (e : Expr) : Option (List (Nat × List Nat)) := do
  let xs ← listLit? e
  xs.mapM fun x => do
    let x := x.consumeMData
    guard (x.isAppOfArity ``Prod.mk 4)
    let n ← natLit? (x.getArg! 2)
    let ws ← listLit? (x.getArg! 3)
    let ws ← ws.mapM natLit?
    pure (n, ws)

/-- The `ite` chain of `pbSchemaOf`'s body: (key constant, schema constant). -/
partial def chain (e : Expr) : List (Name × Name) :=
  let e := e.consumeMData
  match e with
  | .lam _ _ b _ => chain b
  | _ =>
    if e.isAppOfArity ``ite 5 then
      let c := (e.getArg! 1).consumeMData
      let k := if c.isAppOfArity ``Eq 3 then (c.getArg! 2).getAppFn.constName? else none
      let s := (e.getArg! 3).getAppFn.constName?
      match k, s with
      | some k, some s => (k, s) :: chain (e.getArg! 4)
      | _, _ => chain (e.getArg! 4)
    else []

def isProject (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some i => let r := env.header.moduleNames[i.toNat]!.getRoot; r == `Proof || r == `Spec
  | none => false

/-- The `FieldSchema`-typed constants reached from `c` through this repository's definitions. -/
partial def schemaConsts (env : Environment) (c : Name) (seen : NameSet) (acc : NameSet) :
    NameSet × NameSet := Id.run do
  if seen.contains c then return (seen, acc)
  let mut seen := seen.insert c
  let mut acc := acc
  let some ci := env.find? c | return (seen, acc)
  if ci.type.consumeMData.isConstOf `Perennial.EtcdGrove.FieldSchema then
    acc := acc.insert c
  let some v := ci.value? | return (seen, acc)
  if !isProject env c then return (seen, acc)
  for d in v.getUsedConstants do
    (seen, acc) := schemaConsts env d seen acc
  return (seen, acc)

def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let mods := args.toArray.map String.toName
  let env ← importModules (mods.map fun m => { module := m }) {}
  let some sci := env.find? `Perennial.EtcdGrove.pbSchemaOf
    | IO.eprintln "pbschema: pbSchemaOf not found"; return 1
  let some body := sci.value? | return 1
  let mut ok := true
  let tbl := chain body
  if tbl.isEmpty then IO.eprintln "pbschema: pbSchemaOf's chain not read"; return 1
  for (k, s) in tbl do
    let some sv := (env.find? s).bind (·.value?)
      | IO.eprintln s!"pbschema: {s} has no value"; ok := false; continue
    match schemaLit? sv with
    | some fs =>
      let fields := fs.map fun (n, ws) => s!"{n}:{",".intercalate (ws.map toString)}"
      IO.println s!"schema {lastTwo k} {s} {" ".intercalate fields}"
    | none => IO.eprintln s!"pbschema: {s} is not a list literal"; ok := false
  -- the registrations: `pbModelOf … K = some I`
  for (n, ci) in env.constants.map₁.toList do
    let .axiomInfo _ := ci | continue
    let mut t0 := ci.type
    while t0.isForall do t0 := t0.bindingBody!
    let t := t0.consumeMData
    unless t.isAppOfArity ``Eq 3 do continue
    let lhs := (t.getArg! 1).consumeMData
    unless lhs.getAppFn.isConstOf `Perennial.EtcdGrove.pbModelOf do continue
    let some k := lhs.appArg!.getAppFn.constName? | continue
    IO.println s!"root {lastTwo k} {n}"
    let rhs := (t.getArg! 2).consumeMData
    if let some i := rhs.appArg!.getAppFn.constName? then
      let (_, acc) := schemaConsts env i {} {}
      for s in acc.toList do IO.println s!"uses {n} {s}"
  return (if ok then 0 else 1)
