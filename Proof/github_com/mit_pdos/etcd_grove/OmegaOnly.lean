/- `omega_only [h₁, …, hₙ]`: `omega` over the listed hypotheses only (2026-11-17, a build-speed
helper).

`omega` reads every hypothesis of the context that is a fact about integers or naturals (with
`∧`, `∨`, `¬`, `→`, `↔` between them) and splits the disjunctions, `min`, `max`, `/` and `%` it
finds. Inside a long WP proof the context holds dozens of such facts (a loop invariant's
disjunction, every bound collected so far), and one `omega` there can take minutes where its goal
needs two of them: `os.File.WriteAt`'s chunk bounds took 1318s (`Proof/os/File__WriteAtExt.lean`),
`bbolt`'s write loop several calls of a minute (`Proof/go_etcd_io/bbolt/Commit/WriteExtRun.lean`).

`omega_only [h₁, …]` first clears every hypothesis that is a proposition, other than the listed
ones and those something left depends on, then runs `omega`. Clearing hypotheses only removes what
a proof may use, so the proof `omega` then finds is checked as any other. The list documents what
the step rests on; a missing fact makes it fail (then add it). -/
module

public import Lean
public meta import Lean.Elab.Tactic.ElabTerm
public meta import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace OmegaOnly

open Lean Elab Tactic Meta

/-- `omega_only [h₁, …, hₙ]`: `omega` after clearing every propositional hypothesis but `hᵢ`. -/
syntax (name := omegaOnly) "omega_only" " [" term,* "]" : tactic

@[tactic omegaOnly] meta def evalOmegaOnly : Tactic := fun stx => do
  let hs := stx[2].getSepArgs
  -- the listed facts: a hypothesis by name is kept; a term is added as a new hypothesis first
  let mut keep : Array FVarId := #[]
  for h in hs do
    let g ← getMainGoal
    match ← g.withContext (observing? (getFVarId h)) with
    | some fv => keep := keep.push fv
    | none =>
      let (fv, g') ← g.withContext do
        let e ← Term.elabTerm h none
        Term.synthesizeSyntheticMVarsNoPostponing
        let e ← instantiateMVars e
        let g' ← g.assert `h_only (← inferType e) e
        g'.intro1P
      replaceMainGoal [g']
      keep := keep.push fv
  let g ← getMainGoal
  let g ← g.withContext do
    let mut drop : Array FVarId := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail || keep.contains d.fvarId then continue
      if ← isProp d.type then drop := drop.push d.fvarId
    g.tryClearMany drop
  replaceMainGoal [g]
  evalTactic (← `(tactic| omega))

end OmegaOnly
end EtcdGrove
end Perennial
