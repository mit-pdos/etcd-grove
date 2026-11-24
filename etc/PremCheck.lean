/-
**premcheck: the library premises of a dsverify challenge** (notes/dsv-premcheck.md). Not part of the
lakefile; run with

    lake env lean --run etc/PremCheck.lean --conf=FILE MODULE...
    lake env lean --run etc/PremCheck.lean --conf=FILE --selftest=FILE MODULE...

normally through `etc/premcheck.py`, which writes nothing, builds the modules and judges the exit code.

**What it guards.** A challenge's statement (`kitgen --export-challenge`) is the kit's statement with
one premise in place of the landed kit's premises: `(∀ G L, letI := heapAt G L; KitLibs remoteGF) →`,
where `KitLibs` is a class the agent declares in one file of its own (`KitLibs.lean`). The agent may
put there what the system's libraries do (their functions' specs, their initializers), and nothing
else: not what the system's own code does, not the kit's protocol, not the conclusion. premcheck
reads the elaborated class and refuses any field that is not one of:

1. **a library spec**: a `Prop` made of `∀`, `→`, `∧`, `∨`, `∃` (over data), `True`, definitions
   and `Prop`-valued structures (unfolded: the agent's, and the tree's), down to Iris entailments
   `P ⊢ Q` whose conclusion is a weakest precondition (a Hoare triple `{{ P }} e {{ Q }}`) whose
   **subject** `e` calls a function (`@! F`, `functions F _`) or a method (`r @!! T @!! m`,
   `methods T m _`) of a **library package**: `F` or `T` declared in a Goose `Code` module of a
   package that is not one of the challenge's system packages (`system=`), its driver's
   (`driver=`) or a model package (`model=`, e.g. `net`: communication goes through the net
   model, whose specs are proved, never assumed);
2. **an `InitHyp` class of a library package** (`<pkg>.InitHyp GF`: the package's initializer runs
   without panicking; `etc/dsv/README.md`);
3. **library data**: a field whose type is not a `Prop` (types and predicates, e.g. an event token
   `Loc → IProp GF`), or a structure of such data, whose `Prop` fields are themselves library
   specs.

Everywhere in a field (hypotheses, pre- and postconditions, data types), every constant that is not
the agent's own (declared in `KitLibs.lean`, which premcheck unfolds) must not be **denied**: a
constant of a system, driver package (by its name, `Perennial.<pkg>...` or
`Perennial.pkg_id.<pkg>...`, or by its module, `<root>.<tier>.<pkg>...`), or of the conclusion's
modules (`Robustness.*`, `Net.Statement.*`). One exception, read as the caller giving memory up: a
system package's global variable's address `globalAddr X` may occur at **negative polarity** (a
precondition, a hypothesis), never in a postcondition (gogo `proto.RegisterEnum` consuming
`message.MsgType_value`'s points-to, rabia's landed premise).

The file `KitLibs.lean` (`kitlibs_file=`) is elaborated again over its own imports, and every
command it holds is checked (an elaboration error refuses it): only `namespace`/`section`/`end`
(no `meta section`), `open`, `variable`, `universe`, `set_option` (`linter.*`, `maxHeartbeats`,
`maxRecDepth`, `autoImplicit`, `relaxedAutoImplicit`), `attribute [local instance] ...`, doc
comments, and `def`/`abbrev`/`structure`/`class`
declarations (modifiers: doc comment, visibility, `noncomputable`; attributes `reducible`,
`irreducible`, `expose`; no `deriving`). No `instance`, `axiom`, `opaque`, `theorem`, `inductive`,
`attribute`, `macro`, `syntax`, `notation`, `elab`, `initialize`, `#` command: the challenge's
statement imports this file, so nothing in it may change how the statement elaborates. Its
imports must be modules of the challenge as exported (`fixed=`, when given). In the environment, the
module declares no axiom, no opaque constant and no instance, and no instance of `KitLibs` exists in
any loaded module.

**The non-vacuity instance** (`instance=`, in `instance_module=`): a theorem whose type is the
statement's `KitLibs` premise (`premise=`, a definition of the statement's file, which `spec=`'s
hypothesis must equal). Its axioms are listed: Lean's three; those of the instance module, each of
which must itself pass rule 1 or 2 (an axiom about a library function: the lab judges whether it is
true of Go); those of the challenge's fixed tree (the trust base: Goose's untranslated
declarations, Perennial's); any other is refused, and so are `sorryAx`, `Lean.ofReduceBool`,
`Lean.ofReduceNat` and `Lean.trustCompiler`.

**Approximations** (what the walk does not see): a fixed constant is judged by its name and module
only, never unfolded in a scan (a library definition of the tree that mentioned the system would
pass; none does: library modules do not import the system's); in a spec position, fixed
definitions and structures are unfolded to find the triples. Polarity is tracked through Lean's
`→`/`¬`/`↔` and Iris's `-∗`/`→`/`⊢`; an atomic predicate's arguments inherit its polarity (the
`globalAddr` exception relies on it).

Exit 0: accepted; 1: refused (the reasons printed); 2: usage or a missing constant.
-/
import Lean
open Lean Meta Elab

/-! ## Configuration -/

structure Conf where
  kitlibs : Name := .anonymous
  /-- `none`: the selftest's own file (constants without a module). -/
  kitlibsMod : Option Name := none
  kitlibsFile : Option String := none
  spec : Option Name := none
  premise : Option Name := none
  inst : Option Name := none
  instMod : Option Name := none
  deny : Array Name := #[]
  model : Array Name := #[]
  denyMods : Array Name := #[`Robustness, `Net.Statement]
  fixed : Option (Std.HashSet Name) := none
  maxDepth : Nat := 400
  deriving Inhabited

inductive Pol | pos | neg | both
  deriving BEq, Inhabited

def Pol.flip : Pol → Pol | .pos => .neg | .neg => .pos | .both => .both

structure St where
  errs : Array String := #[]
  /-- The library functions and `InitHyp` classes the current field is about. -/
  about : Array Name := #[]
  notes : Array String := #[]
  path : List String := []

abbrev M := ReaderT Conf (StateRefT St MetaM)

def lastStr (n : Name) : String := match n with | .str _ s => s | _ => ""

def here : M String := do
  let p := (← get).path
  return if p.isEmpty then "" else ".".intercalate p.reverse ++ ": "

def err (msg : String) : M Unit := do
  let h ← here
  modify fun s => { s with errs := s.errs.push (h ++ msg) }

def inPath (p : String) (k : M α) : M α := do
  modify fun s => { s with path := p :: s.path }
  try k finally modify fun s => { s with path := s.path.tail }

def ppS (e : Expr) : MetaM String := do
  try return toString (← ppExpr e) catch _ => return toString e

/-! ## Packages: by name and by module -/

def nameOfComps (cs : List Name) : Name := cs.foldl (fun acc c => acc ++ c) .anonymous

def modOf (c : Name) : MetaM (Option Name) := do
  let env ← getEnv
  match env.getModuleIdxFor? c with
  | some i => return some env.header.moduleNames[i.toNat]!
  | none => return none

def tiers : List String := ["Code", "GeneratedProof", "Proof", "Spec", "TrustedCode", "ManualProof"]

/-- The package part of a module name: what follows its tier (`Dsverify.Code.rabia.internal.message`
↦ `rabia.internal.message`, `Proof.math.rand.Base` ↦ `math.rand.Base`); the name itself if no tier is
among its first two components. -/
def modTail (m : Name) : Name :=
  let cs := m.components
  match (cs.take 2).findIdx? (fun c => tiers.contains c.toString) with
  | some i => nameOfComps (cs.drop (i + 1))
  | none => m

def isCodeMod (m : Name) : Bool := (m.components.take 2).any (·.toString == "Code")

/-- A constant's name without `Perennial.` and `pkg_id.`. -/
def nameTail (c : Name) : Name :=
  let cs := c.components
  let cs := if cs.head?.map (·.toString) == some "Perennial" then cs.tail else cs
  let cs := if cs.head?.map (·.toString) == some "pkg_id" then cs.tail else cs
  nameOfComps cs

def isAgent (c : Name) : M Bool := do
  return (← modOf c) == (← read).kitlibsMod

/-- Why `c` is denied, if it is. -/
def denied (c : Name) : M (Option String) := do
  let conf ← read
  let nt := nameTail c
  if let some d := conf.deny.find? (·.isPrefixOf nt) then
    return some s!"`{c}` is in the system or driver package `{d}`"
  if let some m ← modOf c then
    if let some d := conf.denyMods.find? (·.isPrefixOf m) then
      return some s!"`{c}` is declared in `{m}` (the statement's conclusion, `{d}`)"
    if let some d := conf.deny.find? (·.isPrefixOf (modTail m)) then
      return some s!"`{c}` is declared in `{m}`, a module of the system or driver package `{d}`"
  return none

/-- The package of a constant declared in a Goose `Code` module, if it is. -/
def codePkg? (c : Name) : MetaM (Option Name) := do
  match ← modOf c with
  | some m => return if isCodeMod m then some (modTail m) else none
  | none => return none

/-! ## Unfolding -/

def findConst (c : Name) : MetaM (Option ConstantInfo) := do
  return ((← getEnv).setExporting false).find? c

/-- `e` with its head definition unfolded, if its head is a definition. -/
def unfoldHead? (e : Expr) : MetaM (Option Expr) := do
  let .const c us := e.getAppFn | return none
  let some ci ← findConst c | return none
  match ci with
  | .defnInfo v =>
    let body := v.value.instantiateLevelParams v.levelParams us
    return some (mkAppN body e.getAppArgs).headBeta
  | _ => return none

def isStructApp? (e : Expr) : MetaM (Option (Name × Array Expr)) := do
  let .const c _ := e.getAppFn | return none
  if isStructure (← getEnv) c then return some (c, e.getAppArgs) else return none

def norm (e : Expr) : MetaM Expr := do
  return (← instantiateMVars e).consumeMData.headBeta

def isPropTy (t : Expr) : MetaM Bool := do
  try isProp t catch _ => return false

/-! ## The walk -/

/-- `globalAddr X` with `X` a system package's constant (a global variable's name). -/
def sysGlobalAddr? (e : Expr) : M Bool := do
  let .const c _ := e.getAppFn | return false
  unless lastStr c == "globalAddr" do return false
  let some x := e.getAppArgs.back? | return false
  let .const x _ := x.consumeMData.getAppFn | return false
  return (← denied x).isSome

/-- The function or method a Goose expression calls: the constants naming it (`F` of
`functions F _`, `T` of `methods T m _`) and whether its head is a value at all. -/
partial def subjectOf (e : Expr) : MetaM (Option (Array Name)) := do
  let e := (← norm e)
  let fn := e.getAppFn
  let args := e.getAppArgs
  if let .const c _ := fn then
    if lastStr c == "App" && args.size ≥ 2 then return ← subjectOf args[args.size - 2]!
    if lastStr c == "Val" && args.size ≥ 1 then
      let v := args.back!
      let found := v.find? fun x => match x.getAppFn with
        | .const c _ => lastStr c == "functions" || lastStr c == "methods"
        | _ => false
      let some call := found | return none
      let cargs := call.getAppArgs
      let .const k _ := call.getAppFn | return none
      let named := if lastStr k == "functions" then cargs[cargs.size - 2]! else cargs[cargs.size - 3]!
      return some (named.getUsedConstants)
  return none

mutual

/-- Scan a term at a polarity: no denied constant (but a system `globalAddr` at negative polarity);
the agent's definitions unfolded, its structures expanded; every positive weakest precondition's
subject a library function or a variable. -/
partial def scan (e : Expr) (pol : Pol) (d : Nat) : M Unit := do
  if d > (← read).maxDepth then err "too deep (a recursive definition?)"; return
  let e ← norm e
  match e with
  | .forallE n t b bi =>
    if ← isPropTy t then scan t pol.flip (d + 1) else scan t .both (d + 1)
    withLocalDecl n bi t fun x => scan (b.instantiate1 x) pol (d + 1)
  | .lam n t b bi =>
    scan t .both (d + 1)
    withLocalDecl n bi t fun x => scan (b.instantiate1 x) pol (d + 1)
  | .letE _ t v b _ =>
    scan t .both (d + 1); scan v .both (d + 1); scan (b.instantiate1 v) pol (d + 1)
  | .proj _ _ x => scan x pol (d + 1)
  | .app .. | .const .. => scanApp e pol d
  | _ => pure ()

partial def scanArgs (args : Array Expr) (pol : Pol) (d : Nat) : M Unit := do
  for a in args do scan a pol (d + 1)

partial def scanApp (e : Expr) (pol : Pol) (d : Nat) : M Unit := do
  let fn := e.getAppFn
  let args := e.getAppArgs
  let .const c _ := fn | do scan fn pol (d + 1); scanArgs args pol d; return
  let n := args.size
  -- Lean's connectives
  if c == ``Not && n == 1 then return ← scan args[0]! pol.flip (d + 1)
  if (c == ``Iff) && n == 2 then return ← scanArgs args .both d
  -- Iris's
  if c.getRoot == `Iris then
    match lastStr c with
    | "wand" | "imp" | "Entails" =>
      if n ≥ 2 then
        scan args[n-2]! pol.flip (d + 1); scan args[n-1]! pol (d + 1); return
    | "iff" | "wandIff" => return ← scanArgs args .both d
    | "wp" | "totalWp" =>
      if n ≥ 2 then
        checkSubject args[n-2]! pol false
        scan args[n-2]! pol (d + 1); scan args[n-1]! pol (d + 1); return
    | _ => pure ()
  if pol == .neg && (← sysGlobalAddr? e) then return
  -- a proof (a theorem, the agent's `_proof_` auxiliaries among them) says nothing a statement
  -- could depend on (proof irrelevance)
  if let some (.thmInfo _) ← findConst c then return
  if ← isAgent c then
    if let some (s, sargs) ← isStructApp? e then return ← expandStruct s sargs pol d
    match ← unfoldHead? e with
    | some e' => return ← scan e' pol (d + 1)
    | none =>
      let some ci ← findConst c | err s!"`{c}`: unknown"; return
      -- the agent's structures' constructors and projections are fine; anything else is not
      if ci matches .ctorInfo _ then return ← scanArgs args pol d
      err s!"`{c}`: the agent's {kindOf ci}, which premcheck cannot see through"
      return
  if let some why ← denied c then err why; return
  scanArgs args pol d

partial def kindOf (ci : ConstantInfo) : String := match ci with
  | .axiomInfo _ => "axiom" | .opaqueInfo _ => "opaque constant" | .thmInfo _ => "theorem"
  | .inductInfo _ => "inductive type" | .recInfo _ => "recursor" | .quotInfo _ => "quotient"
  | .ctorInfo _ => "constructor" | .defnInfo _ => "definition"

/-- A structure applied to its parameters: every field, a `Prop` field as `spec` when `specs`
(positions where a spec is required), else scanned. -/
partial def expandStruct (s : Name) (args : Array Expr) (pol : Pol) (d : Nat)
    (specs : Bool := false) : M Unit := do
  let env ← getEnv
  let ctor := getStructureCtor env s
  if args.size != ctor.numParams then
    err s!"`{s}` applied to {args.size} arguments, not its {ctor.numParams} parameters"; return
  let ty ← instantiateForall ctor.type args
  forallTelescope ty fun fs _ => do
    for f in fs do
      let decl ← f.fvarId!.getDecl
      inPath decl.userName.toString do
        if ← isPropTy decl.type then
          if specs then spec decl.type (d + 1) else scan decl.type pol (d + 1)
        else scan decl.type .both (d + 1)

/-- A weakest precondition's subject: at a spec's top (`top`), a library function or method;
elsewhere at positive polarity, one or a variable (a closure the library returned); at negative
polarity, anything (a callback the caller supplies). -/
partial def checkSubject (e : Expr) (pol : Pol) (top : Bool) : M Unit := do
  if pol == .neg then return
  let conf ← read
  match ← subjectOf e with
  | some cs =>
    let mut lib := 0
    let mut bad := 0
    for c in cs do
      if let some p ← codePkg? c then
        if let some dd := conf.deny.find? (·.isPrefixOf p) then
          err s!"the triple's subject `{c}` is a function of the system or driver package `{dd}`"
          bad := bad + 1
        else if let some mm := conf.model.find? (·.isPrefixOf p) then
          err s!"the triple's subject `{c}` is a function of the model package `{mm}` (its specs are proved, not assumed)"
          bad := bad + 1
        else
          lib := lib + 1
          modify fun s => if s.about.contains c then s else { s with about := s.about.push c }
    if lib == 0 && bad == 0 && top then
      err s!"the triple's subject is not a library function or method: {← ppS e}"
  | none =>
    if top then err s!"the triple's subject is not a call of a library function or method: {← ppS e}"

/-- A position where a library spec is required (positive). -/
partial def spec (e : Expr) (d : Nat) : M Unit := do
  if d > (← read).maxDepth then err "too deep (a recursive definition?)"; return
  let e ← norm e
  match e with
  | .forallE n t b bi =>
    if ← isPropTy t then scan t .neg (d + 1) else scan t .both (d + 1)
    withLocalDecl n bi t fun x => spec (b.instantiate1 x) (d + 1)
  | _ =>
  let fn := e.getAppFn
  let args := e.getAppArgs
  let .const c _ := fn | err s!"not a library spec: {← ppS e}"; return
  if c == ``True then return
  if (c == ``And || c == ``Or) && args.size == 2 then
    spec args[0]! (d + 1); spec args[1]! (d + 1); return
  if c == ``Exists && args.size == 2 then
    scan args[0]! .both (d + 1)
    let p ← norm args[1]!
    match p with
    | .lam n t b bi => withLocalDecl n bi t fun x => spec (b.instantiate1 x) (d + 1)
    | _ => err s!"not a library spec: {← ppS e}"
    return
  if c.getRoot == `Iris && lastStr c == "Entails" && args.size ≥ 2 then
    scan args[args.size-2]! .neg (d + 1); specI args.back! (d + 1); return
  let agent ← isAgent c
  if !agent then
    if let some why ← denied c then err why; return
    if lastStr c == "InitHyp" && isClass (← getEnv) c then
      modify fun s => if s.about.contains c then s else { s with about := s.about.push c }
      return ← scanArgs args .pos d
  if let some (s, sargs) ← isStructApp? e then
    if ← isPropTy e then return ← expandStruct s sargs .pos d (specs := true)
  match ← unfoldHead? e with
  | some e' => spec e' (d + 1)
  | none => err s!"not a library spec (a triple about a library function, an `InitHyp`, or data): {← ppS e}"

/-- An Iris proposition at a spec's top: must reach a weakest precondition. -/
partial def specI (e : Expr) (d : Nat) : M Unit := do
  if d > (← read).maxDepth then err "too deep (a recursive definition?)"; return
  let e ← norm e
  let fn := e.getAppFn
  let args := e.getAppArgs
  let n := args.size
  if let .const c _ := fn then
    if c.getRoot == `Iris then
      match lastStr c with
      | "forall" | "exists" =>
        if n ≥ 2 then
          scan args[n-2]! .both (d + 1)
          let p ← norm args[n-1]!
          match p with
          | .lam x t b bi => return ← withLocalDecl x bi t fun v => specI (b.instantiate1 v) (d + 1)
          | _ => pure ()
      | "wand" | "imp" =>
        if n ≥ 2 then scan args[n-2]! .neg (d + 1); return ← specI args[n-1]! (d + 1)
      | "sep" | "and" | "or" =>
        if n ≥ 2 then specI args[n-2]! (d + 1); return ← specI args[n-1]! (d + 1)
      | "later" | "laterN" | "except0" | "affinely" | "absorbingly" | "fupd" | "bupd"
      | "persistently" | "intuitionistically" | "plainly" =>
        if n ≥ 1 then return ← specI args[n-1]! (d + 1)
      | "wp" | "totalWp" =>
        if n ≥ 2 then
          checkSubject args[n-2]! .pos true
          scan args[n-2]! .pos (d + 1); scan args[n-1]! .pos (d + 1); return
      | _ => pure ()
    if ← isAgent c then
      if let some e' ← unfoldHead? e then return ← specI e' (d + 1)
    else
      if let some why ← denied c then err why; return
      -- the tree's own spec definitions (a triple's notation is a definition in some trees)
      if let some e' ← unfoldHead? e then
        if (e'.find? fun x => match x with | .const k _ => lastStr k == "wp" | _ => false).isSome then
          return ← specI e' (d + 1)
  err s!"not a Hoare triple about a library function: {← ppS e}"

end

/-! ## The class -/

def checkClass : M Unit := do
  let conf ← read
  let env ← getEnv
  let c := conf.kitlibs
  unless isStructure env c do err s!"`{c}` is not a structure or class"; return
  unless ← isAgent c do err s!"`{c}` is not declared in the KitLibs module"; return
  let ctor := getStructureCtor env c
  forallBoundedTelescope ctor.type ctor.numParams fun ps body => do
    for p in ps do
      let decl ← p.fvarId!.getDecl
      inPath s!"(parameter {decl.userName})" do scan decl.type .both 0
    forallTelescope body fun fs _ => do
      for f in fs do
        let decl ← f.fvarId!.getDecl
        modify fun s => { s with about := #[] }
        let isP ← isPropTy decl.type
        inPath decl.userName.toString do
          if isP then spec decl.type 0 else scan decl.type .both 0
        let about := (← get).about.map toString |>.toList
        let kind := if isP then "premise" else "data"
        let line := s!"field {decl.userName}: {kind}; about {about}"
        modify fun s => { s with notes := s.notes.push line }

/-- The module's own declarations: no axiom, no opaque constant, no instance; and no instance of the
class anywhere. -/
def checkModuleDecls : M Unit := do
  let conf ← read
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    let own := (← modOf n) == conf.kitlibsMod
    if own then
      match ci with
      | .axiomInfo _ => err s!"the KitLibs module declares the axiom `{n}`"
      | .opaqueInfo _ => err s!"the KitLibs module declares the opaque constant `{n}`"
      | _ => pure ()
      if isInstanceCore env n then err s!"the KitLibs module declares the instance `{n}`"
    if isInstanceCore env n then
      let ty := ci.type.getForallBody
      if ty.getAppFn.constName? == some conf.kitlibs then
        err s!"`{n}` is an instance of `{conf.kitlibs}` (none may exist)"

/-! ## The statement and the instance -/

def leanAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def countInstBinders (e : Expr) : Nat := Id.run do
  let mut e := e
  let mut k := 0
  while true do
    match e with
    | .forallE _ _ b bi => if bi.isInstImplicit then k := k + 1; e := b else break
    | _ => break
  return k

def checkStatement : M Unit := do
  let conf ← read
  let (some sp, some pr) := (conf.spec, conf.premise) | return
  let some spi ← findConst sp | err s!"no statement `{sp}`"; return
  let some pri ← findConst pr | err s!"no premise definition `{pr}`"; return
  let some sv := spi.value? | err s!"`{sp}` is not a definition"; return
  let some pv := pri.value? | err s!"`{pr}` is not a definition"; return
  unless (pv.find? (·.isConstOf conf.kitlibs)).isSome do
    err s!"`{pr}` does not mention `{conf.kitlibs}`"
  let k := countInstBinders pv
  let ok ← forallBoundedTelescope sv k fun xs sb => do
    if xs.size != k then return false
    let pb ← instantiateForall pv xs
    match sb.consumeMData with
    | .forallE _ h _ _ => isDefEq h pb
    | _ => return false
  unless ok do err s!"`{sp}`'s first premise after its {k} instance binders is not `{pr}`'s body"
  modify fun s => { s with notes := s.notes.push s!"statement `{sp}`: its KitLibs premise is `{pr}`" }

/-- Check one axiom of the instance: rule 1 or 2 (about a library function). -/
def checkAxiomShape (a : Name) : M Unit := do
  let some ci ← findConst a | err s!"no axiom `{a}`"; return
  inPath s!"axiom {a}" do spec ci.type 0

def checkInstance : M Unit := do
  let conf ← read
  let some i := conf.inst | return
  let some ci ← findConst i | err s!"no non-vacuity instance `{i}` (it must build)"; return
  if let some pr := conf.premise then
    unless ← isDefEq ci.type (mkConst pr) do
      err s!"`{i}`'s type is not `{pr}`: {← ppS ci.type}"
  let axs ← collectAxioms i
  let mut lean := 0
  for a in axs.qsort (·.toString < ·.toString) do
    if leanAxioms.contains a then lean := lean + 1; continue
    if [``sorryAx, ``Lean.ofReduceBool, ``Lean.ofReduceNat, ``Lean.trustCompiler].contains a then
      err s!"the instance rests on `{a}`"; continue
    let m ← modOf a
    if m.isSome && m == conf.instMod then
      let ty ← ppS (← findConst a).get!.type
      modify fun s => { s with notes := s.notes.push s!"instance axiom `{a}` (to judge: true of Go?): {ty}" }
      checkAxiomShape a
    else
      match conf.fixed, m with
      | some fx, some mm =>
        if fx.contains mm then
          modify fun s => { s with notes := s.notes.push s!"trust-base axiom `{a}` ({mm})" }
        else err s!"the instance rests on `{a}`, declared in `{mm}`: neither the instance module nor the challenge's fixed tree"
      | _, mm =>
        modify fun s => { s with notes := s.notes.push s!"axiom `{a}` ({mm.getD `none})" }
  modify fun s => { s with notes := s.notes.push s!"instance `{i}`: {axs.size} axioms, {lean} of Lean's" }

/-! ## The file -/

def okOption (n : Name) : Bool :=
  (`linter).isPrefixOf n || [`maxHeartbeats, `maxRecDepth, `autoImplicit, `relaxedAutoImplicit].contains n

def okAttr (stx : Syntax) : Bool :=
  -- an attribute instance: its name is the first identifier or atom in it
  let s := stx.reprint.getD (toString stx)
  let s := s.trimAscii.toString
  ["reducible", "irreducible", "expose"].contains s

partial def findKind (stx : Syntax) (k : SyntaxNodeKind) : Bool :=
  stx.getKind == k || stx.getArgs.any (findKind · k)

partial def collectKind (stx : Syntax) (k : SyntaxNodeKind) : Array Syntax :=
  (if stx.getKind == k then #[stx] else #[]) ++ stx.getArgs.flatMap (collectKind · k)

partial def checkCommand (stx : Syntax) : Except String Unit := do
  let k := stx.getKind
  if k == ``Lean.Parser.Command.in then
    checkCommand stx[0]; checkCommand stx[2]; return
  if [``Lean.Parser.Command.moduleDoc, ``Lean.Parser.Command.namespace, ``Lean.Parser.Command.end,
      ``Lean.Parser.Command.open, ``Lean.Parser.Command.variable,
      ``Lean.Parser.Command.universe].contains k then return
  if k == ``Lean.Parser.Command.section then
    if (stx.reprint.getD "").splitOn "meta " |>.length |> (· > 1) then throw "meta section"
    return
  if k == ``Lean.Parser.Command.attribute then
    -- only `attribute [local instance] ...` (scoped to the file)
    let ok := (collectKind stx ``Lean.Parser.Term.attrInstance).all fun a =>
      let s := (a.reprint.getD "").trimAscii.toString
      s == "local instance"
    if ok then return
    throw "attribute (only `attribute [local instance] ...`)"
  if k == ``Lean.Parser.Command.set_option then
    let n := stx[1].getId
    if okOption n then return
    throw s!"set_option {n}"
  if k == ``Lean.Parser.Command.declaration then
    let decl := stx[1]
    let dk := decl.getKind
    unless [``Lean.Parser.Command.definition, ``Lean.Parser.Command.abbrev,
            ``Lean.Parser.Command.structure].contains dk do
      throw s!"a declaration of kind {dk}"
    -- no deriving (it adds instances)
    for d in collectKind decl ``Lean.Parser.Command.optDeriving do
      if d.getNumArgs > 0 && !d[0].isMissing && d[0].getNumArgs > 0 then throw "deriving"
    -- modifiers: attributes only reducible/irreducible/expose; no unsafe/partial
    let mods := stx[0]
    for a in collectKind mods ``Lean.Parser.Term.attrInstance do
      unless okAttr a do throw s!"attribute {a.reprint.getD ""}"
    if findKind mods ``Lean.Parser.Command.unsafe || findKind mods ``Lean.Parser.Command.partial
        || findKind mods ``Lean.Parser.Command.meta then
      throw "unsafe/partial/meta"
    return
  throw s!"a command of kind {k}"

/-- The file's text rules: the file is elaborated over its own imports (so that scoped notation
parses as in the build), and every command it holds is checked; an elaboration error refuses it.
Returns the refusals and, as `import M` lines, its imports. -/
unsafe def checkFile (file : String) : IO (Array String) := do
  let src ← IO.FS.readFile file
  let inputCtx := Parser.mkInputContext src file
  let (header, mps, msgs) ← Parser.parseHeader inputCtx
  let mut errs : Array String := #[]
  for m in msgs.toList do
    if m.severity == .error then errs := errs.push s!"{file}: header: {← m.toString}"
  let mods := (collectKind header ``Lean.Parser.Module.import).flatMap fun i =>
    i.getArgs.filter (·.isIdent) |>.map (·.getId)
  -- (a previous `importModules` turned initializer execution off again)
  enableInitializersExecution
  let (env, msgs) ← Elab.processHeader ⟨header⟩ {} msgs inputCtx
  for m in msgs.toList do
    if m.severity == .error then errs := errs.push s!"{file}: imports: {← m.toString}"
  let st ← IO.processCommands inputCtx mps (Command.mkState env {} {})
  for m in st.commandState.messages.toList do
    if m.severity == .error then errs := errs.push s!"{file}: does not elaborate: {← m.toString}"
  for cmd in st.commands do
    if Parser.isTerminalCommand cmd then continue
    match checkCommand cmd with
    | .ok _ => pure ()
    | .error e =>
      let pos := inputCtx.fileMap.toPosition (cmd.getPos?.getD 0)
      errs := errs.push s!"{file}:{pos.line}: not allowed in KitLibs.lean: {e}"
  return errs ++ (mods.map fun m => s!"import {m}")

/-! ## Running -/

def runMetaP (env : Environment) (x : MetaM α) : IO α := do
  let opts : Options := ({} : Options) |>.setBool `pp.universes false |>.setBool `pp.proofs false
    |>.insert `maxRecDepth (.ofNat 100000)
  let ctx : Core.Context := { fileName := "<premcheck>", fileMap := default, options := opts,
                              maxHeartbeats := 0 }
  let (a, _) ← (x.run' {} {}).toIO ctx { env }
  return a

def runM (env : Environment) (conf : Conf) (x : M Unit) : IO St := do
  runMetaP env do
    let (_, st) ← (x.run conf).run {}
    return st

def parseConf (file : String) : IO Conf := do
  let mut c : Conf := {}
  for l in ← IO.FS.lines file do
    let l := l.trimAscii.toString
    if l.isEmpty || l.startsWith "#" then continue
    let some i := l.find? (· == '=') |>.map (·) | continue
    let parts := l.splitOn "="
    let k := parts[0]!.trimAscii.toString
    let v := ("=".intercalate parts.tail).trimAscii.toString
    let _ := i
    match k with
    | "kitlibs" => c := { c with kitlibs := v.toName }
    | "kitlibs_module" => c := { c with kitlibsMod := some v.toName }
    | "kitlibs_file" => c := { c with kitlibsFile := some v }
    | "spec" => c := { c with spec := some v.toName }
    | "premise" => c := { c with premise := some v.toName }
    | "instance" => c := { c with inst := some v.toName }
    | "instance_module" => c := { c with instMod := some v.toName }
    | "system" | "driver" => c := { c with deny := c.deny.push v.toName }
    | "model" => c := { c with model := c.model.push v.toName }
    | "deny_module" => c := { c with denyMods := c.denyMods.push v.toName }
    | "fixed" =>
      let ms := (← IO.FS.lines v).filter (· ≠ "") |>.map String.toName
      c := { c with fixed := some (Std.HashSet.ofArray ms) }
    | _ => pure ()
  return c

def report (tag : String) (st : St) : IO Bool := do
  for n in st.notes do IO.println s!"premcheck: {tag}note: {n}"
  for e in st.errs do IO.println s!"premcheck: {tag}REFUSED: {e}"
  return st.errs.isEmpty

/-- The selftest: the file's classes `ok*`/`bad*` (last component, any case) are checked as KitLibs
classes of the file itself; a `bad` class's docstring `expect: TEXT` must occur in a reason. Axioms
`axOk*`/`axBad*` are checked as an instance module's axioms. -/
def runSelftest (env : Environment) (conf : Conf) (file : String) : IO UInt32 := do
  let src ← IO.FS.readFile file
  let inputCtx := Parser.mkInputContext src file
  let cmdState := Command.mkState env {} {}
  let s ← IO.processCommands inputCtx {} cmdState
  let mut nerr := 0
  for m in s.commandState.messages.toList do
    if m.severity == .error then
      nerr := nerr + 1
      IO.println s!"premcheck: selftest: elaboration error: {← m.toString}"
  let env' := s.commandState.env
  let mut names : Array Name := #[]
  for (n, ci) in env'.constants.map₂.toList do
    let l := (lastStr n).toLower
    if ci matches .inductInfo _ then
      if (l.startsWith "ok" || l.startsWith "bad") && isStructure env' n then names := names.push n
    if ci matches .axiomInfo _ then
      if l.startsWith "axok" || l.startsWith "axbad" then names := names.push n
  names := names.qsort (·.toString < ·.toString)
  let mut fails := 0
  for n in names do
    let l := (lastStr n).toLower
    let isAx := l.startsWith "ax"
    let good := l.startsWith "ok" || l.startsWith "axok"
    let st ← runM env' { conf with kitlibs := n, kitlibsMod := none, instMod := none }
      (if isAx then checkAxiomShape n else checkClass)
    let doc := (← findDocString? env' n).getD ""
    let expect := (doc.splitOn "expect: ").tail.head?.map (fun t => ((t.splitOn "\n").head!).trimAscii.toString)
    let pass := if good then st.errs.isEmpty else
      !st.errs.isEmpty && (expect.all fun t => st.errs.any fun e => (e.splitOn t).length > 1)
    IO.println s!"premcheck: selftest {if pass then "PASS" else "FAIL"} {n} ({if good then "accept" else "refuse"}{expect.map (s!", expect '{·}'") |>.getD ""}): {st.errs.toList}"
    unless pass do fails := fails + 1
  IO.println s!"premcheck: selftest: {names.size} cases, {fails} failed, {nerr} elaboration errors"
  return if fails + nerr > 0 then 1 else 0

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let confFile := args.findSome? fun a => (a.dropPrefix? "--conf=").map (·.toString)
  let stFile := args.findSome? fun a => (a.dropPrefix? "--selftest=").map (·.toString)
  let fileOnly := args.findSome? fun a => (a.dropPrefix? "--file=").map (·.toString)
  let mods : Array Name := (args.filter (!·.startsWith "--")).toArray.map String.toName
  if mods.isEmpty then
    IO.eprintln "usage: etc/PremCheck.lean --conf=FILE [--selftest=FILE | --file=KITLIBS.lean] MODULE..."
    return 2
  let conf ← match confFile with | some f => parseConf f | none => pure {}
  let env ← importModules (mods.map fun m => { module := m, importAll := true }) {} (loadExts := true)
  if let some f := stFile then return ← runSelftest env conf f
  if args.contains "--print-modules" then
    for m in env.header.moduleNames do IO.println m
    return 0
  if let some f := fileOnly then
    -- the text check alone (selftests of the file rules)
    let errs ← checkFile f
    let bad := errs.filter (!·.startsWith "import ")
    for e in bad do IO.println s!"premcheck: REFUSED: {e}"
    return if bad.isEmpty then 0 else 1
  if conf.kitlibs.isAnonymous then IO.eprintln "premcheck: the conf names no kitlibs="; return 2
  let some _ := env.find? conf.kitlibs | IO.eprintln s!"premcheck: no class `{conf.kitlibs}`"; return 2
  let mut ok := true
  -- the file
  if let some f := conf.kitlibsFile then
    let lines ← checkFile f
    for l in lines do
      if let some m := l.dropPrefix? "import " then
        let m := m.toString.toName
        match conf.fixed with
        | some fx => unless fx.contains m do
            IO.println s!"premcheck: REFUSED: {f} imports `{m}`, not a module of the challenge as exported"
            ok := false
        | none => pure ()
      else
        IO.println s!"premcheck: REFUSED: {l}"; ok := false
  let st ← runM env conf do
    inPath "KitLibs" checkClass
    checkModuleDecls
    checkStatement
    checkInstance
  ok := (← report "" st) && ok
  IO.println s!"premcheck: {if ok then "ACCEPTED" else "REFUSED"} `{conf.kitlibs}`"
  return if ok then 0 else 1
