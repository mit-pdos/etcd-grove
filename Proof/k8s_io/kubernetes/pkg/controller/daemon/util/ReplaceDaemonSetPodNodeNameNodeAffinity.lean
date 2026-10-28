/-
Proof of `Spec/k8s_io/kubernetes/pkg/controller/daemon/util/ReplaceDaemonSetPodNodeNameNodeAffinity.lean`.
Lean-first.
-/
module

public import Spec.k8s_io.kubernetes.pkg.controller.daemon.util.ReplaceDaemonSetPodNodeNameNodeAffinity

@[expose] public section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.kubernetes.pkg.controller.daemon.util.Assumptions]

set_option hygiene false in
/-- The new node selector `selp`, owned with `nameSel n`. -/
macro "mk_sel" : tactic => `(tactic| (
  ihave Hsel : ownPtrD kd.core.NodeSelector.own selp (DFrac.own 1) (some (nameSel n)) $$ [Hvals Hmf Hts Hsr]
  · iunfold ownPtrD
    iexists _
    iframe Hsr
    iapply (ns_own_terms _ _ _).2
    iapply nameSel_terms_own
    iframe
    ipureintro; exact ⟨rfl, rfl, rfl, rfl, rfl⟩))

theorem ReplaceDaemonSetPodNodeNameNodeAffinity.wp_proof :
    ReplaceDaemonSetPodNodeNameNodeAffinity.spec (GF := GF) (hG := hG) := by
  intro aff da n
  wp_start as Ha
  wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %vals ⟨Hvals, -⟩
  wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %mf ⟨Hmf, -⟩
  wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %ts ⟨Hts, -⟩
  simp only [go.arrayLiteralSize, List.foldl]
  wp_auto
  icases ptrD_null _ _ _ _ $$ Ha with ⟨Ha, %Han⟩
  obtain ⟨selp, hselp⟩ : ∃ l, l = «$r0_ptr» := ⟨_, rfl⟩
  rw [← hselp]
  irename «$r0» => Hsr
  wp_if_destruct
  · -- no affinity: a new one
    have hda : da = none := Han.mp rfl
    subst hda
    mk_sel
    wp_alloc a as Hna
    wp_pures
    iapply HΦ
    isplitr
    · ipureintro; intro h; exact absurd rfl h
    iunfold ownPtrD
    iexists _
    iframe Hna
    unfold kd.core.Affinity.own
    simp only [replAff, Option.getD_none, named]
    isplitl
    · iunfold ownPtrD
      iexists _
      iframe «$v0»
      unfold kd.core.NodeAffinity.own
      simp only [named]
      iframe Hsel
      iapply ownSliceD_nil_of; rfl
    isplitl
    · iapply ownPtrD_none_of; rfl
    · iapply ownPtrD_none_of; rfl
  obtain ⟨a, rfl⟩ : ∃ a, da = some a := by
    cases da with
    | none => exact absurd (Han.mpr rfl) Hif
    | some a => exact ⟨a, rfl⟩
  iunfold ownPtrD at Ha
  icases Ha with ⟨%x, Hx, Hxo⟩
  icases aff_own_na_set _ _ _ $$ Hxo with ⟨Hna, Hxo⟩
  icases ptrD_null _ _ _ _ $$ Hna with ⟨Hna, %Hnan⟩
  wp_auto
  wp_if_destruct
  · -- no node affinity: a new one
    have hna : a.NodeAffinity' = none := Hnan.mp Hif
    have hr : replAff (some a) n =
        ⟨some ⟨some (nameSel n), []⟩, a.PodAffinity', a.PodAntiAffinity'⟩ := by
      simp [replAff, hna]
    mk_sel
    iapply HΦ
    isplitr
    · ipureintro; intro _; rfl
    rw [hr]
    iunfold ownPtrD
    iexists _
    iframe Hx
    iapply Hxo
    iunfold ownPtrD
    iexists _
    iframe «$r0»
    unfold kd.core.NodeAffinity.own
    simp only [named]
    iframe Hsel
    iapply ownSliceD_nil_of; rfl
  obtain ⟨na, hna⟩ : ∃ na, a.NodeAffinity' = some na := by
    cases h : a.NodeAffinity' with
    | none => exact absurd (Hnan.mpr h) Hif
    | some na => exact ⟨na, rfl⟩
  rw [hna]
  iunfold ownPtrD at Hna
  icases Hna with ⟨%y, Hy, Hyo⟩
  icases na_own_req_set _ _ _ $$ Hyo with ⟨Hre, Hyo⟩
  icases ptrD_null _ _ _ _ $$ Hre with ⟨Hre, %Hren⟩
  wp_auto
  wp_if_destruct
  · -- no required selector: the new one
    have hr : replAff (some a) n =
        ⟨some ⟨some (nameSel n), na.PreferredDuringSchedulingIgnoredDuringExecution'⟩,
          a.PodAffinity', a.PodAntiAffinity'⟩ := by
      simp [replAff, hna]
    mk_sel
    iapply HΦ
    isplitr
    · ipureintro; intro _; rfl
    rw [hr]
    iunfold ownPtrD
    iexists x
    iframe Hx
    iapply Hxo
    iunfold ownPtrD
    iexists _
    iframe Hy
    iapply Hyo
    iexact Hsel
  obtain ⟨dsel, hdsel⟩ : ∃ dsel, na.RequiredDuringSchedulingIgnoredDuringExecution' = some dsel := by
    cases h : na.RequiredDuringSchedulingIgnoredDuringExecution' with
    | none => exact absurd (Hren.mpr h) Hif
    | some s => exact ⟨s, rfl⟩
  have hr : replAff (some a) n =
      ⟨some ⟨some (nameSel n), na.PreferredDuringSchedulingIgnoredDuringExecution'⟩,
        a.PodAffinity', a.PodAntiAffinity'⟩ := by
    simp [replAff, hna]
  rw [hdsel]
  iunfold ownPtrD at Hre
  icases Hre with ⟨%z, Hz, -⟩
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %mf2 ⟨Hmf2, -⟩
  wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %ts2 ⟨Hts2, -⟩
  simp only [go.arrayLiteralSize, List.foldl]
  wp_auto
  iapply HΦ
  isplitr
  · ipureintro; intro _; rfl
  rw [hr]
  iunfold ownPtrD
  iexists x
  iframe Hx
  iapply Hxo
  iunfold ownPtrD
  iexists _
  iframe Hy
  iapply Hyo
  iunfold ownPtrD
  iexists _
  iframe Hz
  iapply (ns_own_terms _ _ _).2
  iapply nameSel_terms_own
  iframe
  ipureintro; exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end proof

end dsctl
end EtcdGrove
end Perennial
