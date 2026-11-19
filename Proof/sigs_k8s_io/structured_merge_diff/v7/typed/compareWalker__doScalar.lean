/-
`typed.compareWalker.doScalar`: proved (Prove phase, 2026-11-19): both sides validate (conforming), so
no errors; then `doLeaf`.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker__doScalar
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker__doLeaf
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

theorem typed.compareWalker.doScalar.wp_proof
    (h_compareWalker_doLeaf : typed.compareWalker.doLeaf.spec (GF := GF))
    (h_validateScalar : typed.validateScalar.spec (GF := GF)) :
    typed.compareWalker.doScalar.spec (GF := GF) :=
    fun w sc S st c C dql dqr l r tp s => by
  wp_start as ⟨Hown, Hl, Hr, #Htp, %Hpre⟩
  obtain ⟨Hfind, Hlr, Hcl, Hcr, Hleaf, Hc1, Hc2, Hc3⟩ := Hpre
  rw [LawB.cmpO_scalar S st.t s st.path l r Hfind] at Hc1 Hc2 Hc3
  iNamed Hown
  icases Hown with ⟨Hcore, Hps, Hsp, Ha, Hc⟩
  iNamed Hcore
  icases Hcore with ⟨Hw, #Htr, #Hsc, %HWF⟩
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
  ihave Hown : cwOwn w sc S st c C $$ [Hw Hps Hsp Ha Hc]
  · unfold cwOwn cwCore
    iexists ps, sp, a
    iframe
    rw [Hleaf]
    iframe
    isplitr; iexact Htr
    isplitr; iexact Hsc
    ipureintro; exact HWF
  wp_apply h_compareWalker_doLeaf w sc S st c C dql dqr l r $$ [Hown Hl Hr] as ⟨Hl, Hr, Hown⟩
  · iframe; ipureintro; exact ⟨Hlr, Hc1, Hc2, Hc3⟩
  rw [Hleaf]
  simp only [Bool.false_eq_true, ↓reduceIte]
  iapply HΦ
  rw [LawB.cmpBelow_scalar S st.t s st.path l r Hfind]
  iframe
  iapply noErrs_nil


end proof

end smd
end EtcdGrove
end Perennial
