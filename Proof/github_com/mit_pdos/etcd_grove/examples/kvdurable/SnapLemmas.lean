/-
Lean-first (no Rocq counterpart).

# Lemmas of `putSnapshot`'s and `getSnapshot`'s proofs (2026-10-31)

* `dfrac_split`: every discardable fraction is the sum of two (so that a snapshot's metadata,
  read at `dq`, can be read twice: its conf state lent out by `GetConfState` while `GetIndex` and
  `GetTerm` read the other part).
* `csOptA_csOpt_acc`: a snapshot's nested conf state (`csOptA`: nil, owned or frozen) is, at some
  fraction, an ordinary one (`csOpt`), which the getters take, and gives it back.
-/
module

public import Proof.go_etcd_io.raft.v3.InvPb

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-- Every discardable fraction is the sum of two. -/
theorem dfrac_split (dq : DFrac) : ∃ dq1 dq2 : DFrac, dq = dq1 • dq2 := by
  cases dq with
  | own q => exact ⟨_, _, dfrac_own_half_half q⟩
  | discard => exact ⟨DFrac.discard, DFrac.discard, rfl⟩
  | ownDiscard q =>
    refine ⟨DFrac.ownDiscard q.half, DFrac.own q.half, ?_⟩
    show DFrac.ownDiscard q = DFrac.ownDiscard (q.half + q.half)
    rw [Qp.half_add_half]

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- A snapshot's nested conf state, as an ordinary one at some fraction, and back. -/
theorem csOptA_csOpt_acc (p : Loc) (dq : DFrac) (c : ConfStateM) :
    csOptA (GF := GF) p dq c ⊢
      ∃ dq' : DFrac, csOpt p dq' c ∗ (csOpt p dq' c -∗ csOptA p dq c) := by
  iintro H
  iunfold csOptA at H
  icases H with (%Hn | H | #H)
  · iexists dq
    isplitl []
    · iunfold csOpt; ileft; ipureintro; exact Hn
    iintro -
    iunfold csOptA; ileft; ipureintro; exact Hn
  · iexists dq
    isplitl [H]
    · iunfold csOpt; iright; iexact H
    iintro H
    iunfold csOpt at H
    icases H with (%Hn | H)
    · iunfold csOptA; ileft; ipureintro; exact Hn
    · iunfold csOptA; iright; ileft; iexact H
  · iexists DFrac.discard
    isplitl []
    · iunfold csOpt; iright; iapply csPts_weaken; iexact H
    iintro -
    iunfold csOptA; iright; iright; iexact H

end lemmas

end kvdurable
end EtcdGrove
end Perennial
