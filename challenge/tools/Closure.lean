import Lean
-- (challenge/tools/gen.py runs a copy of this file with the theorem's module imported first.)

/-!
# The trusted part of a theorem, for challenge/tools/gen.py

Run (`lake env lean`) in a built checkout, with env `THEOREM` (the theorem's full name), `OUT`
(the output file), `REPO` (the checkout's root), `REPO_DIRS` (`:`-separated top-level directories
whose modules are the repository's; every other module is a dependency's), `EXTRA` (a file of
names, one per line: more seeds, see below; optional) and `FORCE_MODS` (`,`-separated modules
whose declarations to list although none is reached; optional).

The axioms are those the comparator's `checkAxioms` finds: every axiom reached from the theorem
through statements, values (theorems' and opaques' too) and inductive types' constructors and
recursors (`Util.lean`'s `runForUsedConsts`). It then computes what the comparator's `compareAt`
compares: the axioms themselves, and from the theorem's statement and from the axioms' statements
(the targets, of which only the statement counts), every constant reached the same way.
Each `EXTRA` name adds itself and what it reaches, but through proofs' statements only: what
elaborating the kept declarations needs beyond what their terms mention (an instance found during
elaboration and then unfolded away), found by gen.py from the build's errors. A name that is not a
constant stands for every repository constant whose name ends with it.

Output lines:
* `AXIOM <name> <module>`: an axiom the theorem depends on;
* `DECL <keep|drop> <module> <name> <line> <col> <endLine> <endCol>`: every declaration with a
  source range in a repository module that holds a reached constant: keep when it, or a constant it
  declares (a structure's constructor and projections, a definition's equation lemmas, ...), is
  reached;
* `INST <name> <class> <constant>...`: every instance of a repository module (reached or not), its
  class and the constants in its class's arguments;
* `SORRY <name>`: a declaration reached only from the extra seeds whose value is a proof: its
  proof becomes `sorry` (only its statement is reached);
* `NORANGE <name> <module>`: a reached constant of a repository module with no declaration (none of
  its own, nor of a prefix of its name, in its module).
-/

open Lean Meta

namespace ChallengeClosure

def usedConsts (info : ConstantInfo) : Array Name := Id.run do
  let mut out := info.type.getUsedConstants
  out := out.push info.name
  if let some v := info.value? (allowOpaque := true) then
    out := out ++ v.getUsedConstants
  match info with
  | .inductInfo i => out := out ++ i.ctors.toArray ++ i.all.toArray
  | .ctorInfo i => out := out.push i.induct
  | .recInfo i =>
    for r in i.rules do
      out := out.push r.ctor ++ r.rhs.getUsedConstants
  | _ => pure ()
  return out

def modOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i.toNat]!
  | none => `_

/-- The declaration whose source declares `n`: `n` or its nearest prefix with a range, in the
same module; for a private name, also the prefixes of its public spelling, private or not. -/
def rootOf (env : Environment) (m : Name) (n : Name) : MetaM (Option Name) := do
  let mut k := n
  while !k.isAnonymous do
    if env.contains k && modOf env k == m then
      if (← findDeclarationRanges? k).isSome then return some k
    k := k.getPrefix
  if let some u := privateToUserName? n then
    let mut k' := u
    while !k'.isAnonymous do
      for c in [k', mkPrivateName env k'] do
        if env.contains c && modOf env c == m then
          if (← findDeclarationRanges? c).isSome then return some c
      k' := k'.getPrefix
  return none

/-- The closure from `work`, through statements only for `stmtOnly` names, through everything
for the others. -/
def closure (env : Environment) (stmtOnly : Std.HashSet Name) (work : Array Name)
    (seen : Std.HashSet Name) (proofsToo : Bool := true) :
    MetaM (Std.HashSet Name × Std.HashSet Name) := do
  let mut work := work
  let mut seen := seen
  let mut proofs : Std.HashSet Name := {}
  while !work.isEmpty do
    let n := work.back!
    work := work.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some info := env.find? n | throwError "missing {n}"
    let isProof ← if proofsToo then pure false else
      match info with
      | .thmInfo _ => pure true
      | .defnInfo _ | .opaqueInfo _ => isProp info.type
      | _ => pure false
    if isProof then proofs := proofs.insert n
    if stmtOnly.contains n || isProof then
      work := work ++ info.type.getUsedConstants
    else
      work := work ++ (usedConsts info).filter (!seen.contains ·)
  return (seen, proofs)

def main : MetaM Unit := do
  let env ← getEnv
  let thm := (Syntax.decodeNameLit ("`" ++ (← IO.getEnv "THEOREM").get!)).get!
  let repoDirs := ((← IO.getEnv "REPO_DIRS").getD "").splitOn ":" |>.filter (· ≠ "")
  let repoRoot := (← IO.getEnv "REPO").get!
  let isRepo (m : Name) : IO Bool := do
    if !repoDirs.contains (m.getRoot.toString (escape := false)) then return false
    System.FilePath.pathExists
      (repoRoot ++ "/" ++ ((m.toString (escape := false)).replace "." "/") ++ ".lean")
  let extra ← match (← IO.getEnv "EXTRA") with
    | some f => do
      let ls := (← IO.FS.readFile f).splitOn "\n" |>.filter (· ≠ "")
      pure (ls.map fun s => (Syntax.decodeNameLit ("`" ++ s)).getD s.toName).toArray
    | none => pure #[]
  let some ti := env.find? thm | throwError "no theorem {thm}"
  -- the axioms the theorem depends on, by the comparator's own walk (`checkAxioms`: from the
  -- theorem, through statements, values, and inductive types' constructors and recursors), which
  -- reaches some `collectAxioms` does not (a constructor's inductive type, a recursor's rules)
  let (proofClosure, _) ← closure env {} #[thm] {}
  let axs := proofClosure.toArray.filter fun n =>
    match env.find? n with | some (.axiomInfo _) => true | _ => false
  let targets : Std.HashSet Name := Std.HashSet.ofArray (axs.push thm)
  -- the axioms themselves (declared here, the comparator compares their statements), and what
  -- their statements and the theorem's reach
  let mut work : Array Name := ti.type.getUsedConstants ++ axs
  let (compared, _) ← closure env targets work {}
  -- the extra seeds (not the comparator's, only elaboration's): reached through values, but for
  -- proofs (theorems, Prop-valued definitions), through statements only: no compared term holds
  -- them (or they would be compared) and elaboration does not unfold a proof, so gen.py makes them
  -- `sorry` (`SORRY` lines). A seed that is not a constant is a name as written in a source (`etcdStorage`): every
  -- repository constant whose name ends with it
  let partial_ := extra.filter (!env.contains ·)
  let mut extra := extra.filter env.contains
  if !partial_.isEmpty then
    let mut repoMods : Std.HashSet Nat := {}
    for i in [0:env.header.moduleNames.size] do
      if ← isRepo env.header.moduleNames[i]! then repoMods := repoMods.insert i
    let sufs := partial_.map (·.toString)
    for (c, _) in env.constants.map₁.toList do
      let some i := env.getModuleIdxFor? c | continue
      if !repoMods.contains i.toNat then continue
      let s := c.toString
      if sufs.any fun x => s.endsWith ("." ++ x) then extra := extra.push c
  let (reached, proofs) ← closure env targets extra (compared.insert thm) (proofsToo := false)
  let out ← IO.FS.Handle.mk (System.FilePath.mk (← IO.getEnv "OUT").get!) .write
  for a in axs do
    out.putStrLn s!"AXIOM {a} {modOf env a}"
  for n in proofs.toArray do
    let m := modOf env n
    if ← isRepo m then
      if let some r ← rootOf env m n then
        if r == n then out.putStrLn s!"SORRY {n}"
  let mut keepRoots : Std.HashSet Name := {}
  let mut mods : Std.HashSet Name := {}
  let mut norange : Nat := 0
  for n in reached.toArray do
    let m := modOf env n
    if ← isRepo m then
      mods := mods.insert m
      match ← rootOf env m n with
      | some r => keepRoots := keepRoots.insert r
      | none =>
        out.putStrLn s!"NORANGE {n} {m}"
        norange := norange + 1
  -- modules gen.py keeps for what they register (env `FORCE_MODS`, `,`-separated)
  for s in ((← IO.getEnv "FORCE_MODS").getD "").splitOn "," do
    if s != "" then mods := mods.insert ((Syntax.decodeNameLit ("`" ++ s)).getD s.toName)
  for m in mods.toArray do
    let some idx := env.getModuleIdx? m | throwError "no module {m}"
    for c in env.header.moduleData[idx.toNat]!.constNames do
      if let some r ← findDeclarationRanges? c then
        let k := if keepRoots.contains c then "keep" else "drop"
        out.putStrLn s!"DECL {k} {m} {c} {r.range.pos.line} {r.range.pos.column} {r.range.endPos.line} {r.range.endPos.column}"
  -- every repository instance, reached or not, in any module: an instance elaboration needs can be
  -- in a module of which nothing is reached
  for m in env.header.moduleNames do
    if !(← isRepo m) then continue
    let some idx := env.getModuleIdx? m | continue
    for c in env.header.moduleData[idx.toNat]!.constNames do
      if !(← isInstance c) then continue
      let some info := env.find? c | continue
      let concl ← forallTelescopeReducing info.type fun _ b => pure b
      if let some cls := concl.getAppFn.constName? then
        let args := concl.getAppArgs.foldl (fun a e => a ++ e.getUsedConstants) #[]
        out.putStrLn s!"INST {c} {cls} {" ".intercalate (args.toList.map toString)}"
  logInfo m!"theorem {thm}: {axs.size} axioms, {compared.size} constants compared, \
    {reached.size - compared.size - 1} more for elaboration ({extra.size} seeds), \
    {mods.size} repository modules, {keepRoots.size} declarations kept, {norange} without range"

end ChallengeClosure

set_option maxHeartbeats 0 in
run_meta ChallengeClosure.main
