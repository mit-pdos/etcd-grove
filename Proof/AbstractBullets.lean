/-
Abstracting the proof of a long `·` block into an auxiliary theorem (option `abstractBullets`).

A tactic proof is elaborated into one proof term, which, once the proof is complete, is
instantiated (`instantiateMVars`), shared (`ShareCommon`) and checked by the kernel as a whole.
For the long Iris proofs this final work is a large part of the time: 31 of the 88s of
`watchGRPCStream.serveSubstream`'s proof (18s of it the kernel). It is also all that is left to
do after an edit near the end of a proof in an editor or `etc/lean-check.py`, which re-run the
tactics only from the edit on, and for the longest proofs it is minutes.

With `set_option abstractBullets N` (N > 0), a `·` block spanning at least N lines proves its
goal as an auxiliary theorem (`Lean.Meta.mkAuxTheorem`, over the free variables and
metavariables the proof mentions): the block's proof is instantiated and checked by the kernel
when the block ends, and the enclosing proof term only applies the auxiliary theorem. The work
done when the proof is complete is then that of the proof outside the long blocks, and a block's
work is part of the snapshot after it, which an editor or `etc/lean-check.py` reuses after an
edit elsewhere. Nothing changes in what is proved: the auxiliary theorem is checked by the
kernel like the proof it replaces. (`debug.skipKernelTC` skips both.)

A block that fails (it is admitted, after its error) or whose proof mentions `sorry` is left as
it is. N = 0 (the default) leaves every block as it is.
-/
module

public meta import Lean.Elab.Tactic.BuiltinTactic
public meta import Lean.Meta.Closure

@[expose] public section

namespace Perennial
open Lean Elab Tactic Meta

meta register_option abstractBullets : Nat := {
  defValue := 0
  descr := "prove each `·` block spanning at least this many lines as an auxiliary theorem, \
    checked when the block ends (0: none); see `Proof/AbstractBullets.lean`"
}

/-- The number of lines `stx` spans. -/
meta def lineSpan (stx : Syntax) : CoreM Nat := do
  let fm ← getFileMap
  let some r := stx.getRange? | return 0
  return (fm.toPosition r.stop).line - (fm.toPosition r.start).line + 1

/-- `·` with `abstractBullets`: the builtin `·` on a fresh goal of the same type and context,
whose proof then becomes an auxiliary theorem proving the goal. Declines (to the builtin `·`)
when the option is off or the block is shorter. -/
@[tactic Lean.cdot, incremental] meta def evalCDotAbstract : Tactic := fun stx => do
  let n := abstractBullets.get (← getOptions)
  if n == 0 then throwUnsupportedSyntax
  if (← lineSpan stx) < n then throwUnsupportedSyntax
  let g :: gs ← getUnsolvedGoals | throwUnsupportedSyntax
  let tag ← g.getTag
  -- (instantiated: otherwise every tactic of the block instantiates it again, which made the
  -- fresh elaboration of `watchGRPCStream.serveSubstream` a third slower)
  let g' ← g.withContext do mkFreshExprSyntheticOpaqueMVar (← instantiateMVars (← g.getType)) tag
  setGoals (g'.mvarId! :: gs)
  evalTacticCDot stx
  let pf ← instantiateMVars g'
  if pf.hasSorry then
    g.assign pf
    return
  let pf' ← g.withContext do
    try
      mkAuxTheorem (← instantiateMVars (← g.getType)) pf (kind? := `_bullet) (cache := false)
    catch _ => pure pf
  g.assign pf'

end Perennial
