/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/etcd3/shouldStream.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.shouldStream

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

theorem shouldStream.wp_proof : shouldStream.spec (GF := GF) (hG := hG) := by
  intro opts Obj S sel emp
  wp_start as ⟨#Hsel, #Hoff⟩
  ihave #Pft : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.features $$ []
  · iPkgInit
  ihave #Hft : (k8s_io.apiserver.pkg.storage.etcd3.featuresInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Pft
  icases Hft with ⟨%g, #Hg, #Hgate⟩
  iunfold EtcdGrove.k8sfeature.featureGateOk at Hgate
  icases Hgate with ⟨#Hen, -⟩
  iunfold rangeStreamOff at Hoff
  icases Hoff with ⟨%g', #Hg', #Hoff⟩
  ihave %Hag := typedPointsto_agree_wand _ _ _ _ _ $$ Hg Hg'
  cases Hag
  unfold selPredOk
  icases Hsel with ⟨%hsel, #HM, #HE⟩
  wp_auto
  cases hr : opts.Recursive'
  · wp_auto
    iapply HΦ
    itrivial
  · wp_auto
    iStructNamed opts
    by_cases hl : sint.Z (W64 0) < sint.Z opts.Predicate'.Limit'
    · rw [decide_eq_true hl]
      (try wp_auto)
      wp_bind
      iapply HE $$ Predicate
      inext
      iintro Predicate
      cases emp
      · (try wp_auto)
        iapply HΦ
        itrivial
      · (try wp_auto)
        wp_apply Hen as %b Hb
        · ipureintro; decide
        ihave %hb := Hb $$ Hoff
        subst hb
        (try wp_auto)
        iapply HΦ
        itrivial
    · rw [decide_eq_false hl]
      (try wp_auto)
      wp_apply Hen as %b Hb
      · ipureintro; decide
      ihave %hb := Hb $$ Hoff
      subst hb
      (try wp_auto)
      iapply HΦ
      itrivial

end proof

end k8s
end EtcdGrove
end Perennial
