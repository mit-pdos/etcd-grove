/-
Lean-first (no Rocq counterpart).

# The checker's state values, shared (2026-10-19)

A model's `rep v s` need not be persistent (`ModelSpec`): etcd's robustness model sorts its
states in place in `Equal` (`issues/etcd-robustness-model-equal-mutates.md`). `checkSingle`
keeps a state value in several places at once (the current state, the stack's frames, the
cache's entries), so it shares each one in a non-atomic invariant (iris-lean's
`NonAtomicInvariant`) of a pool `p` allocated at its start, whose token `na_own p ⊤` it keeps
through the loop: `shared S p k v s` is persistent, and opening it with the token and a later
credit gives `rep k v s` for one call of the model (`shared_acc`), after which the token comes back
once `rep k v s` is put back.

All the state invariants have one namespace (`stateN`): the checker never opens two at once
(`StepContext` opens the current state's, `Equal` in `cacheContains` one cached entry's against
the candidate, which is owned, not yet shared), so the masks need not be disjoint.

The pool's camera is `NaInvG GF`, which Perennial's `allG` does not provide yet: the porcupine
results assume the instance (`notes/STATUS.md`, "Porcupine").
-/
module

public import Proof.github_com.anishathalye.porcupine.Defs
public import Iris.Instances.Lib.NaInvariants

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProofMode Iris.Std

namespace github_com.anishathalye.porcupine

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [NaInvG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]
variable {σ : Type}

/-- The namespace of the checker's state invariants. -/
abbrev stateN : Namespace := nroot.@"porcupine_state"

/-- A state value `v` of `s` (of index `k`), shared in the pool `p` (see the file header). -/
def shared (S : ModelSpec GF σ) (p : NaInvPoolName) (k : Nat) (v : GoInterface) (s : σ) :
    IProp GF :=
  NonAtomicInvariant.inv p stateN (S.rep k v s)

instance shared_persistent (S : ModelSpec GF σ) (p : NaInvPoolName) (k : Nat)
    (v : GoInterface) (s : σ) : Persistent (shared S p k v s) := by
  unfold shared; infer_instance

/-- Share a state value. -/
theorem shared_alloc (S : ModelSpec GF σ) (p : NaInvPoolName) (E : CoPset) (k : Nat)
    (v : GoInterface) (s : σ) : S.rep k v s ⊢ |={E}=> shared S p k v s := by
  iintro H
  unfold shared
  iapply NonAtomicInvariant.inv_alloc
  inext
  iexact H

end defs

section acc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NaInvG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]
variable {σ : Type}

/-- Open a shared state value, with the pool's token and a later credit; putting the value
back gives the token back. -/
theorem shared_acc (S : ModelSpec GF σ) (p : NaInvPoolName) (k : Nat) (v : GoInterface)
    (s : σ) :
    shared S p k v s ∗ NonAtomicInvariant.own p ⊤ ∗ £ 1 ⊢
      |={⊤}=> S.rep k v s ∗ (S.rep k v s -∗ |={⊤}=> NonAtomicInvariant.own p ⊤) := by
  iintro ⟨#Hsh, Htok, Hlc⟩
  unfold shared
  imod NonAtomicInvariant.inv_acc (E := ⊤) (F := ⊤) CoPset.subseteq_top CoPset.subseteq_top
    $$ Hsh Htok with ⟨Hrep, Hrest, Hclose⟩
  imod lc_fupd_elim_later $$ Hlc Hrep with Hrep
  imodintro
  iframe Hrep
  iintro Hrep
  iapply Hclose
  iframe Hrest
  inext
  iexact Hrep

end acc

end github_com.anishathalye.porcupine

end Perennial
