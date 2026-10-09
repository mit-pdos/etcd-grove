/-
`word` with a checked proof cache.

Perennial's `word` keeps a process-global cache of the proofs it found
(`Perennial/Std/Word/Cache.lean`). A cached proof usually is `D._proof_1_N args`, where
`D._proof_1_N` is the auxiliary lemma `omega` created (`mkAuxTheorem`); the cache only checks
that a constant of that *name* exists. In a long-lived Lean process -- the language server
behind `./ide`, which re-elaborates a declaration after every edit in the same process -- the
declaration is elaborated again from scratch and the same names `D._proof_1_N` are issued again,
now for different `omega` goals. A cache hit then returns a proof applying the new lemma to the
old arguments: it elaborates (the elaborator does not re-check it; `./ide upto` also skips the
kernel), and the kernel rejects the declaration with
`(kernel) application type mismatch  D._proof_1_N ...`. A fresh `lean FILE` (`./check`) is
not affected.

This module redefines `word` (the newest `macro_rules` wins, also inside `wp_bounds`,
`list_seg` and other macros that call `word`) as `word_checked`: run Perennial's `word`, type
check the proof it produced (`Meta.check`, cheap: the omega proofs are behind auxiliary
lemmas), and if the check fails, clear the caches and run `word` again.
-/
import Perennial.Std.Word.Automation

namespace Perennial.word
open Lean Elab Tactic Meta

/-- Forget all cached `word` proofs and failures. -/
def cacheClear : IO Unit := do
  wordCache.set {}
  failCache.set {}

/-- Is `pf` a well-typed proof of the type of `g`? -/
def proofChecks (g : MVarId) : MetaM Bool := g.withContext do
  let pf ← instantiateMVars (mkMVar g)
  if pf.hasExprMVar then return true   -- not closed by `word` alone; nothing to check
  try
    check pf
    isDefEq (← inferType pf) (← g.getType)
  catch _ => return false

/-- `word`, with the proof checked; a stale cached proof (see the module docstring) clears
the caches and `word` runs again. -/
elab "word_checked" : tactic => do
  let g ← getMainGoal
  let s ← saveState
  evalTactic (← `(tactic| word_cached))
  unless ← proofChecks g do
    s.restore
    cacheClear
    evalTactic (← `(tactic| word_cached))

end Perennial.word

macro_rules
  | `(tactic| word) => `(tactic| word_checked)
