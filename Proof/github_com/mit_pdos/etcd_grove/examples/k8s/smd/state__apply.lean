/-
`state.apply` (`examples/k8s/smd/smd.go`). Lean-first (2026-11-19, notes/smd-robustness.md).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.smd.state__apply
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.smd.state__typedObj
public import Spec.sigs_k8s_io.structured_merge_diff.v7.merge.Updater__Apply
public import Proof.sigs_k8s_io.structured_merge_diff.v7.OwnLaws

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_smd

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open smd

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.smd.Assumptions]

theorem state.apply.wp_proof
    (wp_typedObj : state.typedObj.spec (GF := GF))
    (wp_Apply : smd.merge.Updater.Apply.spec (GF := GF)) :
    state.apply.spec (GF := GF) := fun s sc st st' m kvs mgr msg ch hok h => by
  -- the model: the configuration validates, and `Apply` returns an object (or nil) and managers
  have hval : validate k8s_smd.sc rootRef (.map kvs) = false := by
    cases hv : validate k8s_smd.sc rootRef (.map kvs)
    · rfl
    · simp [stApply, stTyped, asTyped, hv] at h
  have hok' := hok
  simp only [stOk, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hok'
  wp_start as ⟨Hst, #Hm⟩
  unfold ownState
  icases Hst with ⟨%u, %lv, %mfm, Hs, Hsc, #Hu, #Hlv, #Hmf⟩
  wp_auto
  wp_apply (wp_typedObj s sc st m kvs hval) $$ [Hs Hsc] as %cp ⟨Hst, #Hcp⟩
  · unfold ownState
    isplitl
    · iexists u, lv, mfm
      iframe
      iframe #
    · iexact Hm
  unfold ownState
  icases Hst with ⟨%u', %lv', %mfm', Hs, Hsc, #Hu', #Hlv', #Hmf'⟩
  wp_auto
  have hnp : (match apply false k8s_smd.sc st.live ⟨some (.map kvs), rootRef⟩ version st.mf mgr false with
      | .panic => False | _ => True) := by
    cases ha : apply false k8s_smd.sc st.live ⟨some (.map kvs), rootRef⟩ version st.mf mgr false <;>
      simp_all [stApply, stTyped, asTyped]
  wp_apply (wp_Apply u' false sc k8s_smd.sc lv cp st.live ⟨some (.map kvs), rootRef⟩ version mfm' st.mf mgr
    false hok'.1 hok'.2 (by decide +kernel) hnp) $$ [Hsc] as %op %mfm2 %err ⟨Hsc, Hpost⟩
  · iframe
    iframe #
  cases ha : apply false k8s_smd.sc st.live ⟨some (.map kvs), rootRef⟩ version st.mf mgr false with
  | ok tvo mf =>
    simp only [applyPost]
    icases Hpost with ⟨%herr, #Hop, #Hmf2⟩
    subst herr
    cases tvo with
    | none =>
      simp only [stApply, stTyped, asTyped, hval, Bool.false_eq_true, ite_false] at h
      rw [ha] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      simp only [ownTVOpt]
      icases Hop with %hop
      subst hop
      obtain ⟨rfl, rfl⟩ := h
      wp_auto
      iapply HΦ
      iexists u', lv', mfm2
      iframe
      iframe #
    | some o =>
      simp only [stApply, stTyped, asTyped, hval, Bool.false_eq_true, ite_false] at h
      rw [ha] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      simp only [ownTVOpt]
      obtain ⟨rfl, rfl⟩ := h
      ihave %hop : ⌜op ≠ null⌝ $$ [Hop]
      · unfold ownTV
        icases Hop with ⟨%v, %tr, Hp, -, -⟩
        iapply typedPointsto_not_null $$ Hp
      wp_auto
      simp only [hop, decide_false]
      wp_auto
      iapply HΦ
      iexists u', op, mfm2
      iframe
      iframe #
  | conflicts cs => simp [stApply, stTyped, asTyped, hval, ha] at h
  | error => simp [stApply, stTyped, asTyped, hval, ha] at h
  | panic => simp [stApply, stTyped, asTyped, hval, ha] at h

end proof

end k8s_smd
end EtcdGrove
end Perennial
