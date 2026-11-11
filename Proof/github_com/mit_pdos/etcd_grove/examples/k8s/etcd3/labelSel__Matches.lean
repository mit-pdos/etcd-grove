/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/k8s/etcd3/labelSel__Matches.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.labelSel__Matches
public import Spec.k8s_io.apimachinery.pkg.labels.Set__Get
public import Spec.k8s_io.apimachinery.pkg.labels.Set__Has

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProofMode k8s
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj labelSel fieldSel)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem labelSel.Matches.wp_proof
    (wp_Get : labels.Set.Get.spec (GF := GF) (hG := hG))
    (wp_Has : labels.Set.Has.spec (GF := GF) (hG := hG))
    : labelSel.Matches.spec (GF := GF) (hG := hG) := by
  intro s m M
  wp_start as #Hm
  ihave #Pl : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.labels $$ []
  · iPkgInit
  wp_auto
  cases ha : s.all'
  · wp_auto
    iunfold mapRO at Hm
    icases Hm with (⟨%hm, %hM⟩ | #Hm)
    · subst hm hM
      wp_method_call
      wp_call
      wp_auto
      have h : lmL s ∅ = false := by simp [lmL, ha]
      rw [h]
      iapply HΦ
      itrivial
    · wp_apply (wp_Has m DFrac.discard M go!"app") $$ [$Hm] as -
      cases hk : (M !! go!"app").isSome
      · wp_auto
        have h : lmL s M = false := by simp [lmL, ha, hk]
        rw [h]
        iapply HΦ
        itrivial
      · wp_auto
        wp_apply (wp_Get m DFrac.discard M go!"app") $$ [$Hm] as -
        (try wp_auto)
        have h : lmL s M = decide ((M !! go!"app").getD [] = s.app') := by simp [lmL, ha, hk]
        rw [h]
        iapply HΦ
        itrivial
  · wp_auto
    have h : lmL s M = true := by simp [lmL, ha]
    rw [h]
    iapply HΦ
    itrivial

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
