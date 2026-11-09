/-
**The model-as-parameter gate** (per-type message models, stage A: the Scope's G, `[v4]` rules 1-7
as restated by `[v5]`/`[v6]`/`[v6a]`; `notes/per-type-blockers.md`). Not part of the lakefile; run
with

    lake env lean --run etc/ModelParamCheck.lean [--part=ROOT]... [--selftest] MODULE...  > out.jsonl

normally through `etc/model-param-check.py`, which picks the modules as `etc/tcb-report.py` does
(the root modules, grouped by the part roots they reach) and judges the output.

**What it guards.** A trusted statement (an axiom, or a theorem resting on `sorryAx`) must not let
its user choose a message model: a record whose fields are the model (a carrier `M : Type`, a
wire relation, a receive predicate) bound by the statement with nothing tying it to its Go type.
The tie is the registry (`pbModelOf`, `grpcReqModelOf`, `grpcRepModelOf`, `streamReqModelOf`,
`streamRepModelOf`): one model per Go type, by one registration axiom each.

The walk (the dry run's, `2ed37d8e22`): every axiom declared in this repository's `Spec.*`/`Proof.*`
modules (and a part's) whose type is a `Prop` is walked through the δ-closure of this
repository's definitions (each definition summarized once, its leading `fun`s as parameters; no
`whnf`, nothing outside the repository unfolded), every binder read with its polarity (the axiom's
user supplies what is negative and receives what is positive; `→`, `-∗`, `⊢` flip their left;
`↔`, `⊣⊢`, `=` and arguments the walk does not know count as both).

- **R1** (a model binder): a binder whose type holds (through `List`/`Option`/`Prod`/... and
  function codomains, and the fields of structures, recursively) a structure with a `Type`-sorted
  field (a carrier) is a hit at the path of that field. Enums are exempt; the fixed semantic
  classes (`GooseExts`, `HeapGS`, the packages' `Assumptions`, ...) are not walked (R0).
- **Rule 1** (premise matching): an R1 hit passes only if (a) the statement has, at the
  polarity its user supplies, a registry atom `R … k = some v` whose `v` is the hit's binder (or a
  projection chain from it that the hit's path extends) and whose key `k` is a projection chain
  from the same binder (its `.ty`); or (b) the hit lies under a field `F` of a structure that has a
  `Prop` field which is a registry atom on `F` (`GrpcMethod.reqReg : grpcReqModelOf GF Req.ty =
  some Req`): such a record cannot be built without the registration.
- **Rule 2** (registry atoms by polarity): no registry atom, and no binder of a structure carrying a
  registry `Prop` field (`GrpcMethod`), is *received* by the user of an axiom (a positive atom, an
  `∃` at positive polarity, a `∀` at negative polarity), except the exact-shape registrations
  themselves. The same for theorems whose proof reaches `sorryAx`.
- **Registrations** (rules 3, 4): an axiom whose statement, under its binders, is a registry atom
  is a registration. It must have the exact shape `R <binders> <key> = some <value>`: the
  registry applied to distinct bound variables, the key and the value constants applied to bound
  variables only; its non-`Prop` binders are exactly the registry's arguments (rule 4). One per
  (registry, key's constant) (rule 3).
- **Rule 7** (`Sat` per registration): in the registration's module, a theorem whose type is
  exactly the role's `Sat` at the registered value (`ProtoMsgT.ReqSat`/`RepSat`,
  `StreamMsgT.ReqSat`/`RepSat`; for `pbModelOf`, `PbModelC.Sat` at the instance's `data`, a
  constant), and for a request role also a theorem `∃ m, X.wireLen m < grpcMsgMax` (`[v6a]` 5);
  their axioms are printed (`{"t":"satax",...}`), for the driver's allowlist: Lean's three and
  the generated type-declaration axioms of `Code/` (checked there by module, file line and shape:
  `[v6a]` 4).

**What `Sat` is.** Rule 7's `Sat` theorems prove that each registered model is *satisfiable* (some
loop-free store from the zero struct reaches it), not that it is *faithful* to Go's decoder: the
models' fields (`dec`, `wire`, `send`, `recv`, `wireLen`, ...) are trusted text, listed and argued
in the Freeze package and attacked there.

`--selftest` (rule 6's negative tests) elaborates scratch declarations over the imported
environment (`SELFTESTS` below), each of which must be refused, and one which must pass.

One JSON object per line: `axiom`, `hit` (`R1` hits, `covered` by rule 1 or not), `atom`
(rule 2 failures), `reg` (registrations, with `bad` reasons), `sat` (rule 7: the theorems found),
`satax` (their axioms, with modules and types), `selftest`.
-/
import Lean
open Lean Elab

def jstr (s : String) : String := (Json.str s).compress

def modOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i.toNat]!
  | none => env.mainModule

def isProject (parts : List Name) (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | none => true  -- the selftests' scratch declarations
  | some _ =>
    let m := modOf env n
    let r := m.getRoot
    r == `Spec || r == `Proof ||
      parts.any fun p => (p ++ `Spec).isPrefixOf m || (p ++ `Proof).isPrefixOf m

def REGISTRIES : List Name :=
  [`Perennial.EtcdGrove.pbModelOf, `Perennial.EtcdGrove.grpcReqModelOf,
   `Perennial.EtcdGrove.grpcRepModelOf, `Perennial.EtcdGrove.streamReqModelOf,
   `Perennial.EtcdGrove.streamRepModelOf]

def isR0Class (n : Name) : Bool :=
  match n with
  | .str p l =>
    ["GooseExts", "GooseSemantics", "GooseInterp", "GoGlobalContext", "HeapGS",
     "BundledGFunctors", "Assumptions"].contains l ||
    (l == "Semantics" && (match p with | .str _ s => s == "go" | _ => false))
  | _ => false

/-- A package `Assumptions` class, by name: R0 for the walk, but rule 7 checks where it is declared. -/
def isAssumptionsName (n : Name) : Bool :=
  match n with | .str _ l => l == "Assumptions" | _ => false

def CONTAINERS : List Name :=
  [`List, `Option, `Array, `Prod, `Sum, `PProd, `MProd, `Subtype, `Sigma, `PSigma]

inductive Pol | pos | neg | both
  deriving BEq, Hashable, Inhabited

def Pol.flip : Pol → Pol | .pos => .neg | .neg => .pos | .both => .both
def Pol.comp (outer q : Pol) : Pol :=
  match outer with | .pos => q | .neg => q.flip | .both => .both
/-- (received, supplied) -/
def rs (p : Pol) : Bool × Bool := (p == .pos || p == .both, p == .neg || p == .both)
def orPair (a b : Bool × Bool) : Bool × Bool := (a.1 || b.1, a.2 || b.2)
def compPair (outer : Pol) (rsu : Bool × Bool) : Bool × Bool :=
  match outer with
  | .pos => rsu
  | .neg => (rsu.2, rsu.1)
  | .both => (rsu.1 || rsu.2, rsu.1 || rsu.2)

partial def codomain : Expr → Expr
  | .forallE _ _ b _ => codomain b
  | .mdata _ e => codomain e
  | e => e

def isTypeSort (e : Expr) : Bool :=
  match codomain e with
  | .sort l => !l.isZero
  | _ => false

def indIsProp (iv : InductiveVal) : Bool :=
  match codomain iv.type with
  | .sort l => l.isZero
  | _ => false

def isEnum (env : Environment) (iv : InductiveVal) : Bool :=
  iv.ctors.all fun c => match env.find? c with
    | some (.ctorInfo cv) => cv.numFields == 0
    | _ => false

def ctorFields (cv : ConstructorVal) (params : Array Expr) : Array (Name × Expr) := Id.run do
  let mut t := cv.type
  let mut ps : Array Expr := #[]
  for i in [0:cv.numParams] do
    match t with
    | .forallE _ _ b _ =>
      ps := ps.push (params[i]?.getD (mkConst `_param)); t := b
    | _ => pure ()
  t := t.instantiateRev ps
  let mut out := #[]
  for _ in [0:cv.numFields] do
    match t with
    | .forallE n d b _ =>
      out := out.push (n, d)
      t := b.instantiate1 (mkConst (`_field ++ n))
    | _ => pure ()
  return out

/-- A registry atom: `@Eq (Option _) (R … k) (Option.some v)` (or with `some` elided). -/
def regAtom? (e : Expr) : Option (Name × Expr × Expr) :=
  let e := e.consumeMData
  if e.isAppOfArity ``Eq 3 then
    let lhs := (e.getArg! 1).consumeMData
    match lhs.getAppFn with
    | .const r _ =>
      if REGISTRIES.contains r && lhs.getAppNumArgs > 0 then
        let rhs := (e.getArg! 2).consumeMData
        let v := if rhs.isAppOfArity ``Option.some 2 then rhs.getArg! 1 else rhs
        some (r, lhs.appArg!, v)
      else none
    | _ => none
  else none

/-- The bound variable an expression is a projection chain from (structure projections only). -/
partial def rootBVar? (e : Expr) : Option Nat :=
  match e.consumeMData with
  | .bvar i => some i
  | .proj _ _ x => rootBVar? x
  | _ => none

/-- Whether a field type mentions the constant `c` (a placeholder `_field.F`). -/
def mentions (e : Expr) (c : Name) : Bool := (e.find? fun x => x.isConstOf c).isSome

structure St where
  binders : Array (String × Option Nat) := #[]
  -- per unit
  occ : Std.HashMap (Nat × String × String) (Bool × Bool) := {}
  locals : Std.HashMap (String × String) (Bool × Bool) := {}
  r1 : Std.HashSet (String × String × Bool) := {}
  atoms : Bool × Bool := (false, false)
  atomWhere : Array String := #[]
  paramPol : Std.HashMap Nat (Bool × Bool) := {}
  -- global
  sums : Std.HashMap Name (Array (String × String × Bool) × Array (Nat × String × String × Pol) ×
    Array (String × String × Bool × Bool) × (Bool × Bool) × Array (Bool × Bool)) := {}
  inProg : NameSet := {}
  r1Cache : Std.HashMap Expr (Array (String × String × Bool)) := {}
  indCache : Std.HashMap Name (Array (String × String × Bool)) := {}
  indProg : NameSet := {}
  regCarry : Std.HashMap Name Bool := {}
  whereMap : Std.HashMap Name (Array String) := {}

abbrev M := ReaderT (Environment × List Name) (StateM St)

/-- Whether an inductive (a structure) carries a registry `Prop` field, directly or in a field. -/
partial def carriesReg (c : Name) : M Bool := do
  let (env, _) ← read
  if let some b := (← get).regCarry.get? c then return b
  modify fun s => { s with regCarry := s.regCarry.insert c false }
  let mut b := false
  if let some (.inductInfo iv) := env.find? c then
    for k in iv.ctors do
      let some (.ctorInfo cv) := env.find? k | continue
      for (_, fty) in ctorFields cv #[] do
        if (fty.find? fun x => match x with
            | .const n _ => REGISTRIES.contains n | _ => false).isSome then b := true
  modify fun s => { s with regCarry := s.regCarry.insert c b }
  return b

partial def typeCarriesReg (t : Expr) : M Bool := do
  let t := codomain t.consumeMData
  let .const c _ := t.getAppFn | return false
  if CONTAINERS.contains c then
    for a in t.getAppArgs do
      if ← typeCarriesReg a then return true
    return false
  carriesReg c

mutual
partial def r1Hits (t : Expr) : M (Array (String × String × Bool)) := do
  let (env, parts) ← read
  let t := codomain t.consumeMData
  let args := t.getAppArgs
  let .const c lvls := t.getAppFn | return #[]
  if CONTAINERS.contains c then
    let sfx := if c == `List || c == `Array then "[]" else if c == `Option then "?" else ""
    let mut out := #[]
    for i in [0:args.size] do
      let p := if c == `Prod && args.size == 2 then s!".{i + 1}" else sfx
      out := out ++ (← r1Hits args[i]!).map fun (q, ty, cv) => (p ++ q, ty, cv)
    return out
  if isR0Class c then return #[]
  match env.find? c with
  | some (.inductInfo iv) =>
    if indIsProp iv || isEnum env iv then return #[]
    let own ← indHits c iv
    let mut out := own
    for a in args.extract 0 iv.numParams do
      out := out ++ (← r1Hits a).map fun (q, ty, cv) => (s!"⟨{c.getString!} arg⟩" ++ q, ty, cv)
    return out
  | some (.defnInfo dv) =>
    if !isProject parts env c then return #[]
    r1Hits ((dv.value.instantiateLevelParams dv.levelParams lvls).beta args)
  | _ => return #[]

partial def indHits (c : Name) (iv : InductiveVal) : M (Array (String × String × Bool)) := do
  let (env, _) ← read
  if let some h := (← get).indCache.get? c then return h
  if (← get).indProg.contains c then return #[]
  modify fun s => { s with indProg := s.indProg.insert c }
  let single := iv.ctors.length == 1
  let mut out := #[]
  for k in iv.ctors do
    let some (.ctorInfo cv) := env.find? k | continue
    let fs := ctorFields cv #[]
    for (fn, fty) in fs do
      let p := if single then s!".{fn}" else s!".{k.getString!}.{fn}"
      -- rule 1 (b): a sibling Prop field that is a registry atom on this field
      let covered := fs.any fun (_, g) =>
        match regAtom? (codomain g) with
        | some (_, key, v) => mentions v (`_field ++ fn) && mentions key (`_field ++ fn)
        | none => false
      if isTypeSort fty then out := out.push (p, s!"{c}", covered)
      else out := out ++ (← r1Hits fty).map fun (q, ty, cv) => (p ++ q, ty, cv || covered)
  modify fun s => { s with indCache := s.indCache.insert c out, indProg := s.indProg.erase c }
  return out
end

def newBinder (path : String) (ty : Expr) (param : Option Nat := none) : M Nat := do
  let id := (← get).binders.size
  let hs ← if param.isSome then pure #[] else match (← get).r1Cache.get? ty with
    | some h => pure h
    | none =>
      let h ← r1Hits ty
      modify fun s => { s with r1Cache := s.r1Cache.insert ty h }
      pure h
  modify fun s => { s with binders := s.binders.push (path, param),
                           r1 := hs.foldl (fun m (p, t, cv) => m.insert (path ++ p, t, cv)) s.r1 }
  return id

partial def objPath (env : Environment) (stack : Array Nat) (e : Expr) : Option (Nat × String) :=
  match e.consumeMData with
  | .bvar i => if i < stack.size then some (stack[stack.size - 1 - i]!, "") else none
  | .proj s i x =>
    (objPath env stack x).map fun (r, p) =>
      (r, s!"{p}.{(getStructureFields env s)[i]?.getD (Name.mkNum .anonymous i)}")
  | e' =>
    match e'.getAppFn with
    | .const f _ =>
      match env.getProjectionFnInfo? f with
      | some info =>
        let args := e'.getAppArgs
        if args.size < info.numParams + 1 then none else
        let call := if args.size > info.numParams + 1 then "(·)" else ""
        (objPath env stack args[info.numParams]!).map fun (r, p) =>
          (r, s!"{p}.{f.getString!}{call}")
      | none => none
    | _ => none

def contra (n : Name) : Option (Pol → Array Pol → Array Pol) :=
  let lastTwo (f : Pol → Pol × Pol) := fun (p : Pol) (ps : Array Pol) =>
    if ps.size < 2 then ps else
      let (a, b) := f p
      (ps.set! (ps.size - 2) a).set! (ps.size - 1) b
  if n == `Iris.BI.BIBase.wand || n == `Iris.BI.BIBase.imp || n == `Iris.BI.BIBase.Entails ||
     n == `Iris.BI.Entails then
    some (lastTwo fun p => (p.flip, p))
  else if n == `Iris.BI.BiEntails || n == `Iris.BI.BIBase.BiEntails || n == `Iff ||
     n == `Eq || n == `Ne || n == `HEq || n == `Iris.BI.BIBase.iff || n == `Iris.BI.iff then
    some (lastTwo fun _ => (.both, .both))
  else if n == `Not then
    some fun p ps => if ps.size < 1 then ps else ps.set! (ps.size - 1) p.flip
  else none

/-- The binders `fun x => …` of these heads are existential: received at positive polarity. -/
def FORALLS : List Name := [`Iris.BI.BIBase.forall, `Iris.BI.forall]

def EXISTS : List Name := [``Exists, `Iris.BI.BIBase.exists, `Iris.BI.exist, `Iris.BI.BIBase.exist]

def notePar (stack : Array Nat) (i : Nat) (pol : Pol) : M Unit := do
  if i < stack.size then
    let b := stack[stack.size - 1 - i]!
    if let some k := (← get).binders[b]!.2 then
      modify fun s => { s with paramPol := s.paramPol.insert k (orPair (s.paramPol.getD k (false, false)) (rs pol)) }

def unfoldable (env : Environment) (parts : List Name) (c : Name) : Option DefinitionVal :=
  match env.find? c with
  | some (.defnInfo dv) =>
    if isProject parts env c && (env.getProjectionFnInfo? c).isNone then some dv else none
  | _ => none

def noteAtom (pol : Pol) (what : String) : M Unit := modify fun s =>
  let sign := match pol with | .pos => "+" | .neg => "-" | .both => "±"
  { s with atoms := orPair s.atoms (rs pol), atomWhere := s.atomWhere.push (sign ++ what) }

def recordOcc (stack : Array Nat) (obj : Expr) (tag : String) (pol : Pol) : M Unit := do
  let (env, _) ← read
  let some (r, p) := objPath env stack obj | return
  modify fun s => { s with occ := s.occ.insert (r, p, tag) (orPair (s.occ.getD (r, p, tag) (false, false)) (rs pol)) }

mutual
partial def walkBinder (n : Name) (d b : Expr) (bpol : Pol) (pol : Pol) (pfx : String)
    (stack : Array Nat) : M Unit := do
  -- `bpol`: the polarity at which the bound value is received by the user. A bounded binder
  -- (`∀ m ∈ ms, …`, `∃ m ∈ ms, …`) ranges over a variable already bound: not judged ([v5]).
  -- the membership's collection must be a variable bound outside (or a projection chain from one)
  let memBound (d' : Expr) : Bool :=
    let d' := d'.consumeMData
    d'.isAppOf ``Membership.mem && d'.getAppNumArgs == 5 && d'.hasLooseBVar 0 &&
      (match rootBVar? (d'.getArg! 3) with | some i => i ≥ 1 | none => false)
  let bounded := match b.consumeMData with
    | .forallE _ d' _ _ => memBound d'
    | .app (.app (.const ``And _) d') _ => memBound d'
    | _ => false
  if !bounded then
    if ← typeCarriesReg d then noteAtom bpol s!"binder {n}"
  let x ← newBinder s!"{pfx}{n}" d
  walk b pol pfx (stack.push x)

partial def walk (e : Expr) (pol : Pol) (pfx : String) (stack : Array Nat) : M Unit := do
  let (env, parts) ← read
  match e with
  | .mdata _ b => walk b pol pfx stack
  | .bvar i => notePar stack i pol
  | .forallE n d b _ =>
    walk d pol.flip pfx stack
    walkBinder n d b pol.flip pol pfx stack
  | .lam n d b _ =>
    walk d .both pfx stack
    let x ← newBinder s!"{pfx}{n}" d
    walk b pol pfx (stack.push x)
  | .letE n t v b _ =>
    walk t .both pfx stack; walk v .both pfx stack
    let x ← newBinder s!"{pfx}{n}" t
    walk b pol pfx (stack.push x)
  | .proj _ _ x => walk x pol pfx stack
  | .const c _ =>
    if (unfoldable env parts c).isSome then useDef c #[] pol pfx stack
  | .app .. =>
    if let some (r, key, v) := regAtom? e then
      noteAtom pol s!"atom {r}"
      recordOcc stack v s!"__reg:{r}" pol
      recordOcc stack key s!"__regkey:{r}" pol
      walk key .both pfx stack
      walk v .both pfx stack
      return
    -- any other occurrence of a registry constant (`pbModelOf k = pbModelOf k'`, `.isSome`, ...)
    if let .const r _ := e.getAppFn then
      if REGISTRIES.contains r then noteAtom .both s!"bare registry {r}"
    let f := e.getAppFn
    let args := e.getAppArgs
    match f with
    | .const c _ =>
      -- a BI universal binder: chosen by the user at `pol` (its domain a premise)
      if FORALLS.contains c && args.size > 0 then
        if let .lam n d b _ := args.back!.consumeMData then
          -- the arguments before the lambda are the binder's type (`d` again) and instances
          walk d pol.flip pfx stack
          walkBinder n d b pol.flip pol pfx stack
          return
      -- an existential binder: received at `pol`
      if EXISTS.contains c && args.size > 0 then
        if let .lam n d b _ := args.back!.consumeMData then
          walk d pol pfx stack
          walkBinder n d b pol pol pfx stack
          return
      let pols := (contra c).map (· pol (args.map fun _ => pol)) |>.getD (args.map fun _ => pol)
      if (env.getProjectionFnInfo? c).isSome then
        for i in [0:args.size] do walk args[i]! pols[i]! pfx stack
        return
      if (unfoldable env parts c).isSome then
        useDef c args pol pfx stack
        return
      for i in [0:args.size] do walk args[i]! pols[i]! pfx stack
    | .bvar i =>
      notePar stack i pol
      for a in args do walk a pol pfx stack
    | _ =>
      walk f pol pfx stack
      for a in args do walk a pol pfx stack
  | _ => pure ()

partial def useDef (c : Name) (args : Array Expr) (pol : Pol) (pfx : String)
    (stack : Array Nat) : M Unit := do
  let (env, _) ← read
  let (r1, params, locals, atoms, paramPol) ← summary c
  modify fun s => { s with r1 := r1.foldl (·.insert ·) s.r1 }
  if (compPair pol atoms).1 || (compPair pol atoms).2 then
    let inner := ((← get).whereMap.getD c #[]).toList.take 3
    let sign := match pol with | .pos => "+" | .neg => "-" | .both => "±"
    modify fun s => { s with atomWhere := s.atomWhere.push s!"{sign}via {c} [{"; ".intercalate inner}]" }
  modify fun s => { s with atoms := orPair s.atoms (compPair pol atoms) }
  for (i, suf, tag, q) in params do
    if h : i < args.size then
      if let some (r, p) := objPath env stack args[i] then
        let k := (r, p ++ suf, tag)
        modify fun s => { s with occ := s.occ.insert k (orPair (s.occ.getD k (false, false)) (rs (pol.comp q))) }
  for (p, tag, r, u) in locals do
    let v := compPair pol (r, u)
    modify fun s => { s with locals := s.locals.insert (p, tag) (orPair (s.locals.getD (p, tag) (false, false)) v) }
  for i in [0:args.size] do
    let (pp, pn) := paramPol[i]?.getD (true, false)
    let q : Pol := if pp && pn then .both else if pn then .neg else .pos
    if pp || pn then walk args[i]! (pol.comp q) pfx stack
    else walk args[i]! .both pfx stack

partial def summary (c : Name) : M (Array (String × String × Bool) × Array (Nat × String × String × Pol) ×
    Array (String × String × Bool × Bool) × (Bool × Bool) × Array (Bool × Bool)) := do
  let (env, parts) ← read
  if let some sm := (← get).sums.get? c then return sm
  if (← get).inProg.contains c then return (#[], #[], #[], (false, false), #[])
  let some dv := unfoldable env parts c | return (#[], #[], #[], (false, false), #[])
  let s0 ← get
  set { s0 with occ := {}, locals := {}, r1 := {}, paramPol := {}, atoms := (false, false),
                atomWhere := #[], inProg := s0.inProg.insert c }
  let pfx := s!"{c.getString!}/"
  let mut body := dv.value
  let mut stack : Array Nat := #[]
  let mut np := 0
  repeat
    match body with
    | .lam n d b _ =>
      walk d .both pfx stack
      let x ← newBinder s!"{pfx}{n}" d (some np)
      stack := stack.push x; np := np + 1; body := b
    | _ => break
  walk body .pos pfx stack
  let st ← get
  let mut params := #[]
  let mut locals := #[]
  for ((r, p, tag), (rr, uu)) in st.occ.toList do
    match st.binders[r]!.2 with
    | some k =>
      if rr then params := params.push (k, p, tag, Pol.pos)
      if uu then params := params.push (k, p, tag, Pol.neg)
    | none => locals := locals.push (st.binders[r]!.1 ++ p, tag, rr, uu)
  for ((p, tag), (rr, uu)) in st.locals.toList do locals := locals.push (p, tag, rr, uu)
  let pp := (List.range np).toArray.map fun k => st.paramPol.getD k (false, false)
  let sm := (st.r1.toArray, params, locals, st.atoms, pp)
  let st := { st with whereMap := st.whereMap.insert c st.atomWhere }
  set { st with occ := s0.occ, locals := s0.locals, r1 := s0.r1, paramPol := s0.paramPol,
                atoms := s0.atoms, atomWhere := s0.atomWhere, inProg := st.inProg.erase c,
                sums := st.sums.insert c sm }
  return sm
end

/-- `p` extends `q` at a component boundary. -/
def extendsPath (p q : String) : Bool :=
  q.isPrefixOf p && (p.length == q.length ||
    let c := (p.drop q.length).front; c == '.' || c == '[' || c == '?')

/-- Judge one statement: the R1 hits (with whether rule 1 covers each), and the received
atoms (rule 2). -/
def judge (env : Environment) (parts : List Name) (t : Expr) (st0 : St) :
    Array (String × String × Bool) × Array String × St := Id.run do
  let st0 := { st0 with occ := {}, locals := {}, r1 := {}, paramPol := {}, atoms := (false, false),
                        atomWhere := #[], binders := #[] }
  let ((), st) := ((walk t .pos "" #[]).run (env, parts)).run st0
  -- the supplied registry occurrences: (path, registry) for values and keys
  let mut vals : Array String := #[]
  let mut keys : Array String := #[]
  for ((r, p, tag), (_, uu)) in st.occ.toList do
    if uu then
      let path := st.binders[r]!.1 ++ p
      if tag.startsWith "__reg:" then vals := vals.push path
      if tag.startsWith "__regkey:" then keys := keys.push path
  for ((path, tag), (_, uu)) in st.locals.toList do
    if uu then
      if tag.startsWith "__reg:" then vals := vals.push path
      if tag.startsWith "__regkey:" then keys := keys.push path
  let hits := st.r1.toArray.map fun (p, ty, cv) =>
    let ok := cv || vals.any fun v => extendsPath p v && keys.any fun k => extendsPath k v
    (p, ty, ok)
  return (hits, (if st.atoms.1 then st.atomWhere.filter (fun w => w.startsWith "+" || w.startsWith "±") else #[]), st)

def stripBinders (t : Expr) : Array (Name × Expr × BinderInfo) × Expr := Id.run do
  let mut t := t
  let mut bs := #[]
  while t.isForall do
    bs := bs.push (t.bindingName!, t.bindingDomain!, t.bindingInfo!)
    t := t.bindingBody!
  return (bs, t)

def isPropType (env : Environment) (ty : Expr) : IO Bool := do
  let ctx : Core.Context := { fileName := "<model-param>", fileMap := default, maxHeartbeats := 0 }
  try pure (← (Meta.MetaM.run' (Meta.isProp ty)).toIO ctx { env }).1
  catch _ => pure true

/-- A statement's leading binders, elaborated in context (`forallTelescope`): name, binder info,
type, and whether the type is a proposition. A type check that fails counts as NOT a proposition
(no exemption is granted on a failure). -/
def binderKinds (env : Environment) (t : Expr) : IO (Array (Name × BinderInfo × Expr × Bool)) := do
  let ctx : Core.Context := { fileName := "<model-param>", fileMap := default, maxHeartbeats := 0 }
  let m : MetaM (Array (Name × BinderInfo × Expr × Bool)) :=
    Meta.forallTelescope t fun xs _ => xs.mapM fun x => do
      let d ← x.fvarId!.getDecl
      let p ← try Meta.isProp d.type catch _ => pure false
      pure (d.userName, d.binderInfo, d.type, p)
  try pure (← (Meta.MetaM.run' m).toIO ctx { env }).1
  catch _ => pure #[]

/-- A module generated by Goose: this repository's `Code`/`GeneratedProof` (or a part's), or
Perennial's. -/
def gooseModule (parts : List Name) (m : Name) : Bool :=
  m.getRoot == `Code || m.getRoot == `GeneratedProof || (`Perennial.Code).isPrefixOf m ||
    (`Perennial.GeneratedProof).isPrefixOf m ||
    parts.any fun p => (p ++ `Code).isPrefixOf m || (p ++ `GeneratedProof).isPrefixOf m

/-- A registration's shape (rules 3, 4): `none` if exact, else the reason. -/
def regShape (env : Environment) (t : Expr) : IO (Option String × Option (Name × Name × Name)) := do
  let (bs, body) := stripBinders t
  let some (r, key, v) := regAtom? body | return (some "not a registry atom", none)
  let lhs := ((body.consumeMData).getArg! 1).consumeMData
  let regArgs := lhs.getAppArgs.pop
  -- the registry's arguments: distinct bound variables
  let mut idx : Array Nat := #[]
  for a in regArgs do
    match a.consumeMData with
    | .bvar i => if idx.contains i then return (some "a registry argument repeated", none) else idx := idx.push i
    | .const `Iris.HasLC.hasLC _ => pure ()  -- the heap's later-credit flag, fixed
    | _ => return (some "a registry argument is not a bound variable", none)
  let closedApp (e : Expr) : Option Name :=
    match e.consumeMData.getAppFn with
    | .const c _ => if e.consumeMData.getAppArgs.all (·.consumeMData.isBVar) then some c else none
    | _ => none
  let some kc := closedApp key | return (some "the key is not a constant at bound variables", none)
  let some vc := closedApp v | return (some "the value is not a constant at bound variables", none)
  -- rule 4: every non-Prop binder is a registry argument (binders elaborated in context; a
  -- binder whose type fails to check is not a proposition)
  let n := bs.size
  let kinds ← binderKinds env t
  if kinds.size != n then return (some "the binders do not elaborate", none)
  for i in [0:n] do
    let (bn, _, _, isP) := kinds[i]!
    let deBruijn := n - 1 - i
    if !isP && !idx.contains deBruijn then
      return (some s!"binder {bn} is not a registry argument", none)
  return (none, some (r, kc, vc))

def satName (r : Name) : Name :=
  if r == `Perennial.EtcdGrove.grpcReqModelOf then `Perennial.EtcdGrove.ProtoMsgT.ReqSat
  else if r == `Perennial.EtcdGrove.grpcRepModelOf then `Perennial.EtcdGrove.ProtoMsgT.RepSat
  else if r == `Perennial.EtcdGrove.streamReqModelOf then `Perennial.EtcdGrove.StreamMsgT.ReqSat
  else if r == `Perennial.EtcdGrove.streamRepModelOf then `Perennial.EtcdGrove.StreamMsgT.RepSat
  else `Perennial.EtcdGrove.PbModelC.Sat

def isReqRole (r : Name) : Bool :=
  r == `Perennial.EtcdGrove.grpcReqModelOf || r == `Perennial.EtcdGrove.streamReqModelOf

/-- For `pbModelOf`, the `data` constant of the registered value (`PbTypeC.mk D _`). -/
partial def dataConst (env : Environment) (vc : Name) : Option Name := do
  let ci ← env.find? vc
  let v ← ci.value?
  let rec go (e : Expr) : Option Name :=
    match e.consumeMData with
    | .lam _ _ b _ => go b
    | e' =>
      if e'.isAppOf `Perennial.EtcdGrove.PbTypeC.mk then
        let a := e'.getAppArgs
        (a[a.size - 2]?).bind fun d => d.consumeMData.getAppFn.constName?
      else none
  go v

def collectAx (env : Environment) (c : Name) : IO (Array Name) := do
  let ctx : Core.Context := { fileName := "<model-param>", fileMap := default, maxHeartbeats := 0 }
  pure (← (Lean.collectAxioms c : CoreM (Array Name)).toIO ctx { env }).1

/-- Rule 7's allowlist (`[v6a]` 4): Lean's three, and the generated type-declaration axioms of
`Code/` (declared in a `Code.*` module, or a part's, of the generated shapes `X.underlying :
go.GoType`, `X.zero_val : ZeroVal X`, `X : Type`). The driver also checks each one's file line. -/
def allowedAx (parts : List Name) (env : Environment) (a : Name) : Bool :=
  if a == ``propext || a == ``Classical.choice || a == ``Quot.sound then true else
  match env.getModuleIdxFor?  a, env.find? a with
  | some _, some (.axiomInfo av) =>
    let m := modOf env a
    -- this repository's translations (`Code.*`, a part's) and Perennial's of the standard library
    -- (`Perennial.Code.*`), both generated by the pinned translator
    let inCode := m.getRoot == `Code || (`Perennial.Code).isPrefixOf m ||
      parts.any fun p => (p ++ `Code).isPrefixOf m
    let (_, t) := stripBinders av.type
    let t := t.consumeMData
    let last := match a with | .str _ l => l | _ => ""
    inCode && ((last == "underlying" && t.isConstOf `Perennial.go.GoType) ||
      (last == "zero_val" && t.isAppOf `Perennial.ZeroVal &&
        (t.appArg!.consumeMData.getAppFn.constName? == some a.getPrefix)) ||
      (av.type.consumeMData matches .sort (.succ .zero)))
  | _, _ => false

structure Report where
  lines : Array String := #[]
  bad : Nat := 0

/-- Check one environment: every project axiom (and `sorry` theorem mentioning a registry), the
registrations, the `Sat` theorems. -/
def check (env : Environment) (parts : List Name) (emit : String → IO Unit) (onlyNew : Bool := false) :
    IO Nat := do
  let mut bad := 0
  let mut st : St := {}
  let mut regs : Array (Name × Name × Name × Name × Name) := #[]  -- axiom, registry, key, value, module
  let consts := env.constants.map₁.toList ++ env.constants.map₂.toList
  for (n, ci) in consts do
    if !isProject parts env n then continue
    let isAx := ci matches .axiomInfo _
    -- with `onlyNew` (the selftests) only the scratch declarations are walked; every
    -- registration is still collected, for rule 3
    if onlyNew && (env.getModuleIdxFor? n).isSome && !isAx then continue
    let isThm := ci matches .thmInfo _
    if !isAx && !isThm then continue
    -- theorems: every one whose own proof contains `sorryAx` (a theorem resting on another
    -- through it is checked at that one)
    if isThm then
      let direct := match ci.value? with
        | some v => (v.find? (·.isConstOf ``sorryAx)).isSome
        | none => false
      -- a scratch theorem (the selftests) may be elaborated asynchronously: ask the kernel
      let sorried ← if direct then pure true
        else if (env.getModuleIdxFor? n).isNone then pure ((← collectAx env n).contains ``sorryAx)
        else pure false
      if !sorried then continue
    if !(← isPropType env ci.type) then continue
    let (bs, body) := stripBinders ci.type
    let _ := bs
    if isAx && (regAtom? body).isSome then
      let (why, info) ← regShape env ci.type
      match why, info with
      | none, some (r, kc, vc) =>
        regs := regs.push (n, r, kc, vc, modOf env n)
        emit s!"\{\"t\":\"reg\",\"name\":{jstr n.toString},\"registry\":{jstr r.toString},\"key\":{jstr kc.toString},\"value\":{jstr vc.toString},\"module\":{jstr (modOf env n).toString}}"
      | some w, _ =>
        bad := bad + 1
        emit s!"\{\"t\":\"reg\",\"name\":{jstr n.toString},\"bad\":{jstr w}}"
      | _, _ => pure ()
      continue
    if onlyNew && (env.getModuleIdxFor? n).isSome then continue
    if let some o := (← IO.getEnv "MPC_ONLY") then
      if !(o.splitOn ",").contains n.toString then continue
    let (hits, recv, st') := judge env parts ci.type st
    if (← IO.getEnv "MPC_ONLY").isSome then
      emit s!"\{\"t\":\"debug\",\"axiom\":{jstr n.toString},\"where\":{jstr (" | ".intercalate st'.atomWhere.toList)}}"
    st := st'
    emit s!"\{\"t\":\"axiom\",\"name\":{jstr n.toString},\"kind\":{jstr (if isAx then "axiom" else "sorry-theorem")}}"
    for (p, ty, ok) in hits do
      emit s!"\{\"t\":\"hit\",\"rule\":\"R1\",\"axiom\":{jstr n.toString},\"path\":{jstr p},\"type\":{jstr ty},\"covered\":{ok}}"
      if !ok then bad := bad + 1
    for w in recv do
      bad := bad + 1
      emit s!"\{\"t\":\"atom\",\"axiom\":{jstr n.toString},\"where\":{jstr w}}"
  -- rule 3: one registration per (registry, key)
  let mut seen : Std.HashMap (Name × String) Name := {}
  for (n, r, kc, _, _) in regs do
    -- the key's value (a `.ty` constant's body: the Go type), not its name
    let kv := match env.find? kc with
      | some (.defnInfo dv) => toString dv.value
      | _ => kc.toString
    if let some m := seen.get? (r, kv) then
      bad := bad + 1
      emit s!"\{\"t\":\"reg\",\"name\":{jstr n.toString},\"bad\":{jstr s!"a second registration of {kc} in {r} (first: {m})"}}"
    else seen := seen.insert (r, kv) n
  -- rule 7: the `Sat` theorem (and a request's `wireLen` witness) in the registration's module
  for (n, r, _, vc, mod) in regs do
    if onlyNew && (env.getModuleIdxFor? n).isSome then continue
    let target := if r == `Perennial.EtcdGrove.pbModelOf then (dataConst env vc).getD vc else vc
    let sat := satName r
    let mut satThm : Option Name := none
    let mut wlThm : Option Name := none
    for (m, ci) in consts do
      unless ci matches .thmInfo _ do continue
      unless modOf env m == mod do continue
      let (bs, body) := stripBinders ci.type
      let body := body.consumeMData
      -- binders by type: only the R0 instance binders, `{GF}`/`{hlc}`, and an instance of a
      -- Prop-valued class declared in a Goose-generated module (a package's `Assumptions`)
      let kinds ← binderKinds env ci.type
      -- binders that do not elaborate in context are refused (no exemption on a failure)
      let mut hyp := kinds.size != (stripBinders ci.type).1.size
      for (_, bi, bt, isP) in kinds do
        let ok := match bt.getAppFn with
          | .const c _ =>
            (bi.isInstImplicit && ((isR0Class c && !isAssumptionsName c) || (isP && (env.getModuleIdxFor? c).isSome &&
              gooseModule parts (modOf env c)))) ||
            (bi.isImplicit && (c == `Perennial.BundledGFunctors || c == `Iris.HasLC ||
              c == `Iris.BundledGFunctors || c.getString! == "BundledGFunctors"))
          | _ => false
        if !ok then hyp := true
      if hyp then continue
      if body.isAppOf sat && body.getAppNumArgs > 0 &&
          body.appArg!.consumeMData.getAppFn.isConstOf target then
        satThm := some m
      -- the witness, exactly: `∃ m, ProtoMsg.wireLen X.toProtoMsg m < grpcMsgMax` (or the stream
      -- form), with `X` the registered value
      if isReqRole r && body.isAppOfArity ``Exists 2 then
        if let .lam _ _ lb _ := (body.getArg! 1).consumeMData then
          let lb := lb.consumeMData
          let lhs := if lb.isAppOfArity ``LT.lt 4 then (lb.getArg! 2).consumeMData else mkConst `_
          let exact := (lhs.isAppOfArity `Perennial.EtcdGrove.ProtoMsg.wireLen 3 ||
              lhs.isAppOfArity `Perennial.EtcdGrove.StreamMsg.wireLen 3) &&
            (lhs.getArg! 2).consumeMData == .bvar 0 &&
            (let x := (lhs.getArg! 1).consumeMData
             (x.isAppOf `Perennial.EtcdGrove.ProtoMsgT.toProtoMsg ||
                x.isAppOf `Perennial.EtcdGrove.StreamMsgT.toStreamMsg) &&
               x.appArg!.consumeMData.getAppFn.isConstOf vc)
          if exact && (lb.getArg! 3).isConstOf `Perennial.EtcdGrove.grpcMsgMax then
            wlThm := some m
    match satThm with
    | none =>
      bad := bad + 1
      emit s!"\{\"t\":\"sat\",\"reg\":{jstr n.toString},\"bad\":{jstr s!"no theorem of type {sat} {target} in {mod}"}}"
    | some t =>
      emit s!"\{\"t\":\"sat\",\"reg\":{jstr n.toString},\"theorem\":{jstr t.toString}}"
      for a in (← collectAx env t) do
        if !allowedAx parts env a then
          bad := bad + 1
          emit s!"\{\"t\":\"sat\",\"reg\":{jstr n.toString},\"bad\":{jstr s!"{t} rests on {a} ({modOf env a}), not allowed"}}"
        else
          emit s!"\{\"t\":\"satax\",\"theorem\":{jstr t.toString},\"axiom\":{jstr a.toString},\"module\":{jstr (modOf env a).toString}}"
    if isReqRole r then
      match wlThm with
      | none =>
        bad := bad + 1
        emit s!"\{\"t\":\"sat\",\"reg\":{jstr n.toString},\"bad\":{jstr s!"no theorem ∃ m, {vc}.wireLen m < grpcMsgMax in {mod}"}}"
      | some t =>
        emit s!"\{\"t\":\"sat\",\"reg\":{jstr n.toString},\"wireLen\":{jstr t.toString}}"
        for a in (← collectAx env t) do
          if !allowedAx parts env a then
            bad := bad + 1
            emit s!"\{\"t\":\"sat\",\"reg\":{jstr n.toString},\"bad\":{jstr s!"{t} rests on {a} ({modOf env a}), not allowed"}}"
          else
            emit s!"\{\"t\":\"satax\",\"theorem\":{jstr t.toString},\"axiom\":{jstr a.toString},\"module\":{jstr (modOf env a).toString}}"
  return bad

/-! ## Rule 6: the negative tests -/

def PRELUDE : String := "
open Iris Iris.BI Perennial Perennial.EtcdGrove
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [go_etcd_io.etcd.client.v3.Assumptions]
"

/-- (name, declarations, whether the check must refuse them). The scratch declarations are
elaborated over the imported environment (which holds the registered instances). -/
def SELFTESTS : List (String × String × Bool) := [
  ("bare model: an axiom over an unregistered ProtoMsgT",
   "axiom st_bare : ∀ (T : ProtoMsgT GF) (l : Loc) (m : T.M), T.recv l m ⊢ False", true),
  ("registered model: the same with the registry premise (must pass)",
   "axiom st_ok : ∀ (T : ProtoMsgT GF), grpcRepModelOf GF T.ty = some T → ∀ (l : Loc) (m : T.M), T.send l m ⊢ T.send l m", false),
  ("a stray positive registry atom",
   "axiom st_stray : ∀ (T : ProtoMsgT GF), grpcReqModelOf GF T.ty = some T", true),
  ("a post yielding a registry atom",
   "axiom st_post : ∀ (T : ProtoMsgT GF) (P : IProp GF), P ⊢ ⌜grpcReqModelOf GF T.ty = some T⌝", true),
  ("a post yielding a GrpcMethod",
   "axiom st_method : ∀ (P : IProp GF), P ⊢ ∃ m : GrpcMethod GF, ⌜m.name = m.name⌝", true),
  ("an axiom equating two registry entries",
   "axiom st_eq : grpcReqModelOf GF go.bool = grpcReqModelOf GF go.int64", true),
  ("a theorem proved with sorry stating a registration",
   "theorem st_sorry : ∀ (T : ProtoMsgT GF), grpcReqModelOf GF T.ty = some T := sorry", true),
  ("a second registration of a type",
   "axiom st_dup : grpcRepModelOf GF go_etcd_io.etcd.api.v3.etcdserverpb.RangeResponse.ty = some (pbRangeResponseT (GF := GF))", true),
  ("a registration with an extra binder",
   "noncomputable def stT (n : Nat) : ProtoMsgT GF := { pbRangeResponseT (GF := GF) with wireLen := fun _ => n }
axiom st_binder (n : Nat) : grpcRepModelOf GF go_etcd_io.etcd.api.v3.etcdserverpb.HashResponse.ty = some (stT (GF := GF) n)", true),
  ("a registration with no Sat theorem",
   "noncomputable def stU : ProtoMsgT GF := { pbRangeResponseT (GF := GF) with recv := fun _ _ => iprop(False), recv_persistent := fun _ _ => inferInstance }
axiom st_nosat : grpcRepModelOf GF go_etcd_io.etcd.api.v3.etcdserverpb.StatusRequest.ty = some (stU (GF := GF))", true),
  ("a Sat theorem resting on a hand-written zero_val axiom",
   "noncomputable def stV : ProtoMsgT GF := { pbRangeResponseT (GF := GF) with recv := fun _ _ => iprop(False), recv_persistent := fun _ _ => inferInstance }
axiom Foo.zero_val : False
theorem stV_repSat : (stV (GF := GF)).RepSat := Foo.zero_val.elim
axiom st_zv : grpcRepModelOf GF go_etcd_io.etcd.api.v3.etcdserverpb.MemberListResponse.ty = some (stV (GF := GF))", true),
  ("a vacuous Sat theorem (a False hypothesis)",
   "noncomputable def stX : ProtoMsgT GF := { pbRangeResponseT (GF := GF) with recv := fun _ _ => iprop(False), recv_persistent := fun _ _ => inferInstance }
theorem stX_repSat (h : False) : (stX (GF := GF)).RepSat := h.elim
axiom st_vac : grpcRepModelOf GF go_etcd_io.etcd.api.v3.etcdserverpb.HashKVResponse.ty = some (stX (GF := GF))", true),
  ("a reversed wireLen witness",
   "noncomputable def stY : ProtoMsgT GF := { pbPutRequestT (GF := GF) with wireLen := fun _ => grpcMsgMax }
theorem stY_reqSat : (stY (GF := GF)).ReqSat := by
  refine ⟨(pbPutRequestT_reqSat (GF := GF)).1, (pbPutRequestT_reqSat (GF := GF)).2.1, (pbPutRequestT_reqSat (GF := GF)).2.2.1, ?_⟩
  intro ls l m; iintro ⟨_, %h, _⟩; exact absurd h (by simp [stY])
theorem stY_wl : ∃ m, grpcMsgMax ≤ (stY (GF := GF)).wireLen m := ⟨putReqOp (zero_val _) [] [], by simp [stY]⟩
axiom st_rev : grpcReqModelOf GF go_etcd_io.etcd.api.v3.etcdserverpb.HashKVRequest.ty = some (stY (GF := GF))", true),
  ("an unbounded membership binder (∃ m ∈ a closed collection)",
   "noncomputable opaque stMs : List (GrpcMethod GF)
axiom st_univ : ∀ (P : IProp GF), P ⊢ ⌜∃ m ∈ (stMs (GF := GF)), m.name = m.name⌝", true),
  ("a Sat theorem over an Empty binder",
   "noncomputable def stE : ProtoMsgT GF := { pbRangeResponseT (GF := GF) with recv := fun _ _ => iprop(False), recv_persistent := fun _ _ => inferInstance }
theorem stE_repSat (e : Empty) : (stE (GF := GF)).RepSat := e.elim
axiom st_empty : grpcRepModelOf GF go_etcd_io.etcd.api.v3.etcdserverpb.StatusResponse.ty = some (stE (GF := GF))", true),
  ("a Sat theorem over a hand-written False Assumptions class",
   "class Evil.Assumptions : Prop where bad : False
noncomputable def stF : ProtoMsgT GF := { pbRangeResponseT (GF := GF) with recv := fun _ _ => iprop(False), recv_persistent := fun _ _ => inferInstance }
theorem stF_repSat [h : Evil.Assumptions] : (stF (GF := GF)).RepSat := h.bad.elim
axiom st_evil : grpcRepModelOf GF go_etcd_io.etcd.api.v3.etcdserverpb.DefragmentResponse.ty = some (stF (GF := GF))", true),
  ("a wireLen witness of wireLen m - wireLen m",
   "noncomputable def stZ : ProtoMsgT GF := { pbPutRequestT (GF := GF) with wireLen := fun _ => grpcMsgMax }
theorem stZ_reqSat : (stZ (GF := GF)).ReqSat := by
  refine ⟨(pbPutRequestT_reqSat (GF := GF)).1, (pbPutRequestT_reqSat (GF := GF)).2.1, (pbPutRequestT_reqSat (GF := GF)).2.2.1, ?_⟩
  intro ls l m; iintro ⟨_, %h, _⟩; exact absurd h (by simp [stZ])
theorem stZ_wl : ∃ m, (stZ (GF := GF)).wireLen m - (stZ (GF := GF)).wireLen m < grpcMsgMax :=
  ⟨putReqOp (zero_val _) [] [], by simp [stZ, grpcMsgMax]⟩
axiom st_sub : grpcReqModelOf GF go_etcd_io.etcd.api.v3.etcdserverpb.MemberListRequest.ty = some (stZ (GF := GF))", true),
  ("a request registration keeping the default wireLen (no wireLen witness)",
   "noncomputable def stW : ProtoMsgT GF := { pbPutRequestT (GF := GF) with wireLen := fun _ => grpcMsgMax }
theorem stW_reqSat : (stW (GF := GF)).ReqSat := by
  refine ⟨(pbPutRequestT_reqSat (GF := GF)).1, (pbPutRequestT_reqSat (GF := GF)).2.1, (pbPutRequestT_reqSat (GF := GF)).2.2.1, ?_⟩
  intro ls l m; iintro ⟨_, %h, _⟩; exact absurd h (by simp [stW])
axiom st_wl : grpcReqModelOf GF go_etcd_io.etcd.api.v3.etcdserverpb.DefragmentRequest.ty = some (stW (GF := GF))", true)
]

/-- A line of the check's output that is a failure. -/
def isBadLine (l : String) : Bool :=
  (l.splitOn "\"bad\":").length > 1 && !(l.startsWith "{\"t\":\"done\"") ||
  (l.splitOn "\"covered\":false").length > 1 || l.startsWith "{\"t\":\"atom\""

def runSelftest (env : Environment) (parts : List Name) (emit : String → IO Unit)
    (base : Array String) : IO Nat := do
  let mut failures := 0
  for (name, decls, mustRefuse) in SELFTESTS do
    let input := PRELUDE ++ decls ++ "\n"
    let inputCtx := Parser.mkInputContext input "<selftest>"
    let cmdState := Command.mkState env {} {}
    let s ← IO.processCommands inputCtx {} cmdState
    let msgs := s.commandState.messages.toList
    let errs ← msgs.filterMapM fun m => do
      if m.severity == .error then return some (← m.toString) else return none
    if !errs.isEmpty then
      failures := failures + 1
      emit s!"\{\"t\":\"selftest\",\"name\":{jstr name},\"ok\":false,\"why\":{jstr ("did not elaborate: " ++ errs.headD "")}}"
      continue
    let env' := s.commandState.env
    -- the scratch declarations judged with the imported ones (duplicates, Sat theorems): refused
    -- if the check finds more than on the imported environment alone
    let r ← IO.mkRef (#[] : Array String)
    let _ ← check env' parts (fun l => r.modify (·.push l)) (onlyNew := true)
    let news := (← r.get).filter fun l => !base.contains l && isBadLine l
    let refused : Bool := !news.isEmpty
    let ok := refused == mustRefuse
    if !ok then failures := failures + 1
    emit s!"\{\"t\":\"selftest\",\"name\":{jstr name},\"ok\":{ok},\"refused\":{refused},\"by\":{jstr (" | ".intercalate news.toList)}}"
  return failures

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let parts : List Name := args.filterMap fun a =>
    (a.dropPrefix? "--part=").map (·.toString.toName)
  let selftest := args.contains "--selftest"
  let mods : Array Name := (args.filter (!·.startsWith "--")).toArray.map String.toName
  if mods.isEmpty then
    IO.eprintln "usage: etc/ModelParamCheck.lean [--part=ROOT]... [--selftest] MODULE..."
    return 2
  let env ← importModules (mods.map fun m => { module := m }) {} (loadExts := true)
  let out ← IO.getStdout
  let baseRef ← IO.mkRef (#[] : Array String)
  let emit := fun (s : String) => do out.putStrLn s; out.flush; baseRef.modify (·.push s)
  let bad ← check env parts emit
  emit s!"\{\"t\":\"done\",\"bad\":{bad}}"
  if selftest then
    let f ← runSelftest env parts (fun s => do out.putStrLn s; out.flush) (← baseRef.get)
    emit s!"\{\"t\":\"selftests\",\"failures\":{f}}"
  return 0
