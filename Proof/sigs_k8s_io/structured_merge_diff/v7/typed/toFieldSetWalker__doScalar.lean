/-
`typed.toFieldSetWalker.doScalar`: proved (Prove phase, 2026-11-20): the walker's path inserted into
its set is the scalar's fields (`LawA.fieldsAt_scalar`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.toFieldSetWalker__doScalar
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Insert
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsAPure
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsBPers

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

theorem typed.toFieldSetWalker.doScalar.wp_proof
    (h_Set_Insert : fieldpath.Set.Insert.spec (GF := GF)) :
    typed.toFieldSetWalker.doScalar.spec (GF := GF) :=
    fun w sc S st s F dq x tp => by
  wp_start as ⟨Hown, Hv, %Hpre⟩
  obtain ⟨⟨s', Hfind⟩, Hc, Hcard⟩ := Hpre
  rw [LawA.fieldsAt_scalar S st.t s' st.path x Hfind Hc] at Hcard ⊢
  unfold twOwn
  icases Hown with ⟨%ps, %sp, Hcore, Hps, Hsp, Ha, Hs⟩
  unfold twCore
  icases Hcore with ⟨%tr, Hw, #Htr, #Hsc, %HWF⟩
  unfold ownPath
  icases Hps with ⟨Hpf, Hpc⟩
  wp_auto
  wp_apply h_Set_Insert s F ps (DFrac.own 1) st.path $$ [Hs Hpf] as ⟨Hs, Hpf⟩
  · iframe; ipureintro; exact LawB.cardLt_union_left _ _ _ Hcard
  iapply HΦ
  iframe
  isplitr
  · iapply noErrs_nil
  iframe #
  ipureintro; exact HWF

end proof

end smd
end EtcdGrove
end Perennial
