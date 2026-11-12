/- `solve_pkg_init` (Perennial `Pkg.lean`, used by `iPkgInit`) with the packages it has explored
remembered (2026-10-22, a build-speed workaround; `notes/perennial-changes.md`).

Perennial's search unfolds each intuitionistic `isPkgInit` hypothesis into its dependencies,
depth first, until it meets the goal's package. It does not remember the packages it has
explored, and etcd's import graph has many diamonds: the same subtrees are walked again for each
path to them and for each hypothesis, about 10s a call in the examples' `Main` proofs. Whether a
package's dependencies reach the goal's package does not depend on the path to it, so a package
explored without success is skipped when met again. The search visits the rest in the same order
and returns the same proof (the same chain of `isPkgInit_unfold_deps` and `∗` eliminations).

Importing this module overrides `solve_pkg_init` (and so `iPkgInit`) in every module that imports
it, directly or not: an `elab_rules` for the same syntax, tried before Perennial's. Imported where it was measured faster: the examples' `Main` proofs
(their context holds the main package's `isPkgInit`, whose dependency tree the search walks),
`v3rpc/Server`, `EtcdServer.Range`/`Txn`/`applyEntryNormal`. -/
module

public import Perennial.Golang.Theory.Pkg
public meta import Perennial.Golang.Theory.Pkg

@[expose] public section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Lean Elab Tactic Meta Qq Iris.ProofMode

/-- Perennial's `pkgInitChain` with `failed`, the packages whose dependencies were unfolded
without reaching `target`, skipped when met again (and filled as they fail). A package is recorded
only if its search never ran out of `fuel` (`cut` says whether one did), so a failure recorded does
not depend on the path to it. -/
meta partial def pkgInitChainMemo (failed : IO.Ref (Std.HashSet Lean.Expr)) (cut : IO.Ref Bool)
    (target P : Lean.Expr) (fuel : Nat := 200) : MetaM (Option Lean.Expr) := do
  if fuel == 0 then cut.set true; return none
  let P ← instantiateMVars P
  if ← withReducible (isDefEq P target) then
    return some (← mkAppOptM ``BIBase.Entails.rfl #[none, none, some P])
  let P' ← whnfR P
  if P'.isAppOfArity ``isPkgInit 4 then
    let pkg := P'.getArg! 2
    if (← failed.get).contains pkg then return none
    let rec instFields (inst : Lean.Expr) (fuel : Nat) : MetaM (Option Lean.Expr) := do
      let inst := (← instantiateMVars inst).headBeta
      if inst.isAppOfArity ``IsPkgInit.mk 5 then return some (inst.getArg! 3)
      if fuel == 0 then return none
      match ← unfoldDefinition? inst with
      | some i => instFields i (fuel - 1)
      | none => return none
    let some deps ← instFields (P'.getArg! 3) 20 | return none
    let cut0 ← cut.get
    cut.set false
    let r ← pkgInitChainMemo failed cut target deps (fuel - 1)
    let cutHere ← cut.get
    cut.set (cut0 || cutHere)
    let some c := r
      | unless cutHere do failed.modify (·.insert pkg)
        return none
    let pf1 ← mkAppOptM ``isPkgInit_unfold_deps #[none, none, some pkg, some (P'.getArg! 3)]
    return some (← mkAppM ``BIBase.Entails.trans #[pf1, c])
  if P'.isAppOfArity ``BIBase.sep 4 then
    if let some c ← pkgInitChainMemo failed cut target (P'.getArg! 2) (fuel - 1) then
      return some (← mkAppOptM ``pkg_init_sep_l
        #[none, none, none, some (P'.getArg! 2), some (P'.getArg! 3), none, some c])
    if let some c ← pkgInitChainMemo failed cut target (P'.getArg! 3) (fuel - 1) then
      return some (← mkAppOptM ``pkg_init_sep_r
        #[none, none, none, some (P'.getArg! 2), some (P'.getArg! 3), none, some c])
    return none
  if P'.isAppOfArity ``BIBase.intuitionistically 3 then
    if let some c ← pkgInitChainMemo failed cut target (P'.getArg! 2) (fuel - 1) then
      return some (← mkAppM ``pkg_init_intuitionistically #[c])
  return none

/-- Perennial's `solve_pkg_init`, by `pkgInitChainMemo` (one memo for all the hypotheses). -/
elab_rules : tactic
  | `(tactic| solve_pkg_init) => do
    ProofModeM.runTactic `solve_pkg_init fun mvar { hyps, goal, .. } => do
      let target ← whnfR (← instantiateMVars goal)
      unless target.isAppOfArity ``isPkgInit 4 do
        throwIPMError "not an isPkgInit goal: {goal}"
      let failed ← IO.mkRef ({} : Std.HashSet Lean.Expr)
      let cut ← IO.mkRef false
      for (_, ivar, p, P) in hypsList hyps do
        unless isTrue p do continue
        if let some c ← pkgInitChainMemo failed cut target P then
          let r := hyps.remove true ivar
          mvar.assign (← mkAppOptM ``pkg_init_from_hyp
            #[none, none, none, none, some r.e', some r.out', none, some r.p, some r.pf, some c])
          return
      throwIPMError "could not prove {goal} from the intuitionistic context"

end EtcdGrove
end Perennial
