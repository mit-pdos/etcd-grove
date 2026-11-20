/-
`typed.mergingWalker.doScalar`: proved (Prove phase, 2026-11-19): both sides validate (conforming), so
no errors; then `doLeaf`.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker__doScalar
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker__doLeaf
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.validateScalar
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsBPers
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsB

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : typed.Assumptions]

theorem typed.mergingWalker.doScalar.wp_proof
    (h_mergingWalker_doLeaf : typed.mergingWalker.doLeaf.spec (GF := GF))
    (h_validateScalar : typed.validateScalar.spec (GF := GF)) :
    typed.mergingWalker.doScalar.spec (GF := GF) :=
    fun w sc S st dql dqr l r tp s sp => by
  wp_start as ⟨Hown, Hl, Hr, #Htp, %Hpre⟩
  obtain ⟨Hfind, Hlr, Hcl, Hcr, Hleaf⟩ := Hpre
  iNamed Hown
  icases Hown with ⟨Hcore, Hps, Hsp, Ha⟩
  iNamed Hcore
  icases Hcore with ⟨Hw, #Htr, #Hsc, %HWF, #Hrule, #Ho⟩
  wp_auto
  wp_apply h_validateScalar tp s st.lhs dql l $$ [Hl] as %le ⟨Hl, Hle⟩
  · iframe; isplitr; · iexact Htp
    ipureintro
    exact (by cases l with | none => trivial | some x => exact LawB.conf_scalar S st.t s x Hfind Hcl)
  wp_apply h_validateScalar tp s st.rhs dqr r $$ [Hr] as %re ⟨Hr, Hre⟩
  · iframe; isplitr; · iexact Htp
    ipureintro
    exact (by cases r with | none => trivial | some x => exact LawB.conf_scalar S st.t s x Hfind Hcr)
  ihave %Hlen := noErrs_len $$ Hle
  rw [show decide (sint.Z (W64 0) < sint.Z le.len) = false by simp [Hlen]]
  wp_auto
  rw [Hleaf]
  ihave Hown : mwOwn w sc S st sp $$ [Hw Hps Hsp Ha]
  · unfold mwOwn mwCore
    iexists ps
    iframe
    rw [Hleaf]
    iframe
    isplitr; iexact Htr
    isplitr; iexact Hsc
    isplitr; ipureintro; exact HWF
    isplitr; iexact Hrule
    iexact Ho
  wp_apply h_mergingWalker_doLeaf w sc S st dql dqr l r sp $$ [Hown Hl Hr] as ⟨Hl, Hr, Hown⟩
  · iframe; ipureintro; exact Hlr
  rw [Hleaf]
  simp only [Bool.false_eq_true, ↓reduceIte]
  iapply HΦ
  rw [LawB.mergeO_scalar S st.t s l r Hfind]
  iframe
  iapply noErrs_nil

end proof

end smd
end EtcdGrove
end Perennial
