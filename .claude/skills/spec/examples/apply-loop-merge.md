# `apply`/`applyEntries`: a spec pair merged into one at the environment's mode (2026-10-30)

**Target.** `EtcdServer.apply` and `applyEntries` (the server's apply loop), each with a `spec` (auth
off) and a `specOn` (auth on), to become one spec each, as the user decided for the auth-mode merge
(`notes/auth-mode-merge-plan.md`, step 2: the mode is the environment's, `E.authOn`, `.any` excluded,
the on-only rows gated by it). The callee `applyEntryNormal.spec` had just been merged the same way.

**Candidate 1.** Each pair replaced by its `specOn` with the on-only rows through their mode-indexed
forms (`isServerM E.authOn`, `srvLessorNilM`, `logShapeM`, `srvApplyKVM`, `kvAppliedM`; `srvTokRights`,
`True` off, unconditional), the receipts' bound under `E.authOn = true →`, `sa` bound in both modes.
The old pair as corollaries, following the precedent: `specOff` = the old `spec` plus `E.authOn =
false`. Claimed: `applyAll`, the caller, is untouched but for the name of the spec it takes.

**Review (spec reviewer, round 1).** Sound and complete; but the claim was false: `applyAll`'s off proof
calls `applyEntries` before it obtains `E.authOn = false`, so a `specOff` with that premise forces an
edit in a proof another track (the snapshot verification) is rewriting. Small: the assumed
`logShapeM_false`/`_true` did not exist; the receipts' bound placed differently from the precedent.

**Candidate 2 (approved by the user).** The off corollaries are exactly the old off statements, and
derive the mode from the precondition (the off server's view has auth off, `authOn_false_of_off`). The
lemmas added; the bound's placement kept and recorded as the loops' convention.

**What it shows.**
- A corollary that restores an old statement should state it exactly, deriving what the merged spec
  needs from what the old precondition already holds, so callers do not move (PRINCIPLES: know the
  margin; a mode gate, not two specs).
- Check a "callers untouched" claim against the order in which the caller's proof obtains the facts.
