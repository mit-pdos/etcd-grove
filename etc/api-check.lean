/-
The uses of a package's proof by its clients, against the package's signature.  Not part
of the lakefile; run with

    lake env lean --run etc/api-check.lean --sig=NAMESPACE --own=PREFIX... MODULE...

(normally via `etc/api-check.py`, which chooses the modules: the clients').  A module is
the package's when its name is an `--own` prefix or starts with one followed by `.`; a
client declaration is any other declaration of this repository's (`Spec.*`, `Proof.*`,
`EtcdDeps.*`).  The signature is the namespace `NAMESPACE` (`Spec/<pkg>/Sig.lean`,
`Proof/<pkg>/Sig.lean`): `NAMESPACE.specs` and `NAMESPACE.vocab` (`List Name`), its
structures (the laws) and its theorems (their proofs).

A client may use a constant of the package that is
* `api`:     a spec of `specs`, a `Link` result whose statement is one, the package's
             initialization (`wp_initialize'`, and the package's `Init` module), a
             declaration of the signature's namespace;
* `vocab`:   in `vocab`, or named by a spec of `specs` or a field of a law structure;
* `field`:   a field, constructor or recursor of a structure or inductive of `vocab`;
* `instance`: an instance;
* `pure`:    a theorem whose statement names no `Iris` constant, nor a package constant
             that is not `api`/`vocab`/`field`.
Anything else is a `violation`.  Unfolding a predicate whose body names something else
shows up as a use of that something else.  One JSON object per line, for each package
constant a client uses: name, module, kind, class (the above), clients
([client declaration, client module], ...).
-/
import Lean
open Lean

def jstr (s : String) : String := (Json.str s).compress

def modOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i.toNat]!
  | none => .anonymous

/-- The nearest enclosing constant with a source range (the user-facing declaration). -/
partial def rootOf (env : Environment) (n : Name) : Name :=
  let rec go (m : Name) : Option Name :=
    match m with
    | .anonymous => none
    | _ =>
      if (env.find? m).isSome && (declRangeExt.find? env m (level := .private)).isSome
      then some m else go m.getPrefix
  privateToUserName ((go n).getD n)

def kindOf : ConstantInfo → String
  | .defnInfo _ => "def" | .thmInfo _ => "theorem" | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque" | .inductInfo _ => "inductive" | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec" | .quotInfo _ => "quot"

def usedOf (ci : ConstantInfo) : Array Name :=
  ci.type.getUsedConstants ++
    ((ci.value? (allowOpaque := true)).map (·.getUsedConstants) |>.getD #[])

/-- The `Name` literals of a `List Name` definition's body (`[``a, ``b.c]`). -/
partial def nameLits (e : Expr) : Array Name :=
  let rec lit (e : Expr) : Option Name :=
    match e.getAppFn.constName?, e.getAppArgs with
    | some ``Name.anonymous, #[] => some .anonymous
    | some ``Name.mkStr, #[p, .lit (.strVal s)] => (lit p).map (·.str s)
    | some ``Name.str, #[p, .lit (.strVal s)] => (lit p).map (·.str s)
    | some ``Name.mkNum, #[p, .lit (.natVal k)] => (lit p).map (·.num k)
    | some ``Name.num, #[p, .lit (.natVal k)] => (lit p).map (·.num k)
    | some c, args =>
      -- `Name.mkStr1` ... `Name.mkStr8`
      if c.getPrefix == ``Name && (c.toString.drop "Lean.Name.mkStr".length).all Char.isDigit
          && args.all (· matches .lit (.strVal _)) then
        some (args.foldl (fun n a => match a with | .lit (.strVal s) => n.str s | _ => n) .anonymous)
      else none
    | _, _ => none
  match lit e with
  | some n => #[n]
  | none => match e with
    | .app f a => nameLits f ++ nameLits a
    | .mdata _ b => nameLits b
    | _ => #[]

def listOf (env : Environment) (n : Name) : Array Name :=
  match env.find? n with
  | some ci => match ci.value? with | some v => nameLits v | none => #[]
  | none => #[]

/-- A `∀`-telescope's body. -/
partial def stripForall : Expr → Expr
  | .forallE _ _ b _ => stripForall b
  | .mdata _ b => stripForall b
  | e => e

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let pre (p : String) := args.filterMap fun a => (a.dropPrefix? p).map (·.toString)
  let own := pre "--own="
  let some sig := (pre "--sig=").head?.map String.toName
    | IO.eprintln "usage: etc/api-check.lean --sig=NAMESPACE --own=PREFIX... MODULE..."; return 2
  let mods : Array Name := (args.filter (!·.startsWith "--")).toArray.map String.toName
  -- `loadExts`: the instance attribute's imported state (`instanceExtension`)
  let env ← importModules (mods.map fun m => { module := m }) {} (loadExts := true)
  let isOwnMod (m : Name) : Bool :=
    let s := m.toString
    own.any (fun p => s == p || s.startsWith (p ++ "."))
  let isRepoMod (m : Name) : Bool :=
    ["Spec.", "Proof.", "EtcdDeps."].any (m.toString.startsWith ·)
  let isOwn (n : Name) : Bool := isOwnMod (modOf env n)
  let specs : NameSet := (listOf env (sig ++ `specs)).foldl (·.insert ·) {}
  if specs.isEmpty then
    IO.eprintln s!"api-check: no {sig}.specs in the imported modules"; return 2
  -- the signature's own declarations, and its law structures' fields
  let mut sigDecls : NameSet := {}
  let mut vocab : NameSet := (listOf env (sig ++ `vocab)).foldl (·.insert ·) {}
  for (n, _) in env.constants.map₁.toList do
    if sig.isPrefixOf n then
      sigDecls := sigDecls.insert n
      if let some info := getStructureInfo? env n then
        for f in info.fieldNames do
          if let some p := env.find? (n ++ f) then
            for u in (stripForall p.type).getUsedConstants ++ p.type.getUsedConstants do
              if isOwn u && !sig.isPrefixOf u then vocab := vocab.insert (rootOf env u)
  for s in specs.toList do
    if let some ci := env.find? s then
      for u in usedOf ci do
        if isOwn u then vocab := vocab.insert (rootOf env u)
  let insts := (Meta.instanceExtension.getState env).instanceNames
  let isField (n : Name) : Bool :=
    let p := n.getPrefix
    vocab.contains p && (match env.find? p with | some (.inductInfo _) => true | _ => false)
  let isApi (n : Name) : Bool :=
    specs.contains n || sigDecls.contains n ||
    n.getString! == "wp_initialize'" || (modOf env n).getString! == "Init" ||
    (match env.find? n with
     | some ci@(.thmInfo _) =>
       (modOf env n).getString! == "Link" &&
         (match (stripForall ci.type).getAppFn.constName? with
          | some c => specs.contains c | none => false)
     | _ => false)
  let classify (n : Name) : String :=
    if isApi n then "api"
    else if vocab.contains n then "vocab"
    else if isField n then "field"
    else if insts.contains n then "instance"
    else match env.find? n with
      | some ci@(.thmInfo _) =>
        let us := ci.type.getUsedConstants
        if us.any (fun u => (`Iris).isPrefixOf u) then "violation"
        else if us.all (fun u => !isOwn u || isApi u || vocab.contains (rootOf env u) ||
            isField u) then "pure" else "violation"
      | _ => "violation"
  let mut uses : Std.HashMap Name (Array (Name × Name)) := {}
  for (n, ci) in env.constants.map₁.toList do
    let cm := modOf env n
    if !isRepoMod cm || isOwnMod cm then continue
    let client := rootOf env n
    for u in usedOf ci do
      if !isOwn u then continue
      let r := rootOf env u
      let prev := uses.getD r #[]
      if !prev.contains (client, cm) then uses := uses.insert r (prev.push (client, cm))
  let out ← IO.getStdout
  for (r, cs) in uses.toList do
    let k := match env.find? r with | some ci => kindOf ci | none => "?"
    let cl := ",".intercalate (cs.toList.map fun (c, m) => s!"[{jstr c.toString},{jstr m.toString}]")
    out.putStrLn s!"\{\"name\":{jstr r.toString},\"module\":{jstr (modOf env r).toString},\"kind\":{jstr k},\"class\":{jstr (classify r)},\"clients\":[{cl}]}"
  return 0
