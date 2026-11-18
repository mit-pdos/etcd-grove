/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/etcd3/isInitialEventsEndBookmarkRequired.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.isInitialEventsEndBookmarkRequired

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

theorem isInitialEventsEndBookmarkRequired.wp_proof : isInitialEventsEndBookmarkRequired.spec (GF := GF) (hG := hG) := by
  intro opts sie
  wp_start as ⟨#Hsie, #Hon⟩
  ihave #Pft : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.features $$ []
  · iPkgInit
  ihave #Hft : (k8s_io.apiserver.pkg.storage.etcd3.featuresInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Pft
  icases Hft with ⟨%g, #Hg, #Hgate⟩
  iunfold EtcdGrove.k8sfeature.featureGateOk at Hgate
  icases Hgate with ⟨#Hen, -⟩
  iunfold watchListOn at Hon
  icases Hon with ⟨%g', #Hg', #Hon⟩
  ihave %Hag := typedPointsto_agree_wand _ _ _ _ _ $$ Hg Hg'
  cases Hag
  wp_auto
  iStructNamed opts
  cases sie with
  | none =>
    iunfold sendInitIs at Hsie
    icases Hsie with %hn
    rw [hn]
    wp_apply Hen as %b Hb
    · ipureintro; decide
    icases Hb with ⟨-, Hb⟩
    ihave %hb := Hb $$ Hon
    subst hb
    (try wp_auto)
    simp only [reduceCtorEq, false_and, decide_false]
    iapply HΦ
    itrivial
  | some v =>
    iunfold sendInitIs at Hsie
    ihave %hnn := typedPointsto_not_null _ _ _ $$ Hsie
    wp_apply Hen as %b Hb
    · ipureintro; decide
    icases Hb with ⟨-, Hb⟩
    ihave %hb := Hb $$ Hon
    subst hb
    (try wp_auto)
    try rw [decide_eq_false hnn]
    wp_auto
    cases v
    · wp_auto
      simp only [Option.some.injEq, Bool.false_eq_true, false_and, decide_false]
      iapply HΦ
      itrivial
    · iStructNamed Predicate
      wp_auto
      simp only [true_and, Bool.decide_eq_true]
      iapply HΦ
      itrivial

end proof

end k8s
end EtcdGrove
end Perennial
