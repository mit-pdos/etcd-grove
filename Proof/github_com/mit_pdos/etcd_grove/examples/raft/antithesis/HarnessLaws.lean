/-
Lean-first (no Rocq counterpart). #33 parity B1: the proofs of `HarnessRun.lean`'s two laws of the
node tokens and views (`nodeLive_over.law`, `view_update.law`): ghost-state facts over the
invariant's list `[∗list] k ∈ List.finRange R.N`, node `j` its element at position `j.val`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessRun

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

theorem finRange_getElem? {N : Nat} (j : Fin N) : (List.finRange N)[j.val]? = some j := by
  simp

theorem finRange_getElem?_val {N : Nat} {k : Nat} {y : Fin N} (h : (List.finRange N)[k]? = some y) :
    y.val = k := by
  rw [List.getElem?_eq_some_iff] at h
  obtain ⟨hk, hy⟩ := h
  rw [← hy]; simp

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]

/-- **The run is not over while a node goroutine holds its `live` token** (the token is
exclusive). -/
theorem nodeLive_over : nodeLive_over.law (GF := GF) := by
  intro γ j
  iintro ⟨Hl, Hall⟩
  icases (BigSepL.bigSepL_lookup_acc_impl (Φ := fun _ k => nodeLive (GF := GF) γ k)
    (finRange_getElem? j)) $$ Hall with ⟨Hl', -⟩
  unfold nodeLive
  ihave %Hv := dghostVar_valid_2 (GF := GF) (γ.live j) () (DFrac.own 1) () (DFrac.own 1) $$ Hl Hl'
  exact absurd Hv.1 (dfrac_own_one_op_invalid _)

/-- **Node `j`'s view updated**: the goroutine's half and the invariant's agree, and both move. -/
theorem view_update : view_update.law (GF := GF) := by
  intro E γ j V v v'
  iintro ⟨Hv, Hall⟩
  icases (BigSepL.bigSepL_lookup_acc_impl
    (Φ := fun _ k => ghostVar (GF := GF) (γ.view k) (1 : Qp).half (V k))
    (finRange_getElem? j)) $$ Hall with ⟨Hj, Hback⟩
  unfold viewFrag
  ihave %Heq := ghostVar_agree (GF := GF) (γ.view j) v (1 : Qp).half (V j) (1 : Qp).half $$ Hv Hj
  imod ghostVar_update_halves (GF := GF) v' (γ.view j) v (V j) $$ Hv Hj with ⟨Hv, Hj⟩
  imodintro
  isplitr
  · ipureintro; exact Heq.symm
  iframe Hv
  ihave Hj' : ghostVar (GF := GF) (γ.view j) (1 : Qp).half (AntSim.setV V j v' j) $$ [Hj]
  · simp only [AntSim.setV, ite_true]; iexact Hj
  iapply Hback $$ %(fun (_ : Nat) (k : Fin γ.R.N) =>
    ghostVar (GF := GF) (γ.view k) (1 : Qp).half (AntSim.setV V j v' k)) [] Hj'
  · iintro !> %k %y %hy %hki Hy
    have hyj : y ≠ j := by
      intro h; apply hki; rw [← finRange_getElem?_val hy, h]
    simp only [AntSim.setV, if_neg hyj]
    iexact Hy

end laws

end AntHarness
end EtcdGrove
end Perennial
