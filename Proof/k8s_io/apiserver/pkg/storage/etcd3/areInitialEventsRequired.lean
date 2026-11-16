/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/etcd3/areInitialEventsRequired.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.areInitialEventsRequired

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

theorem areInitialEventsRequired.wp_proof : areInitialEventsRequired.spec (GF := GF) (hG := hG) := by
  intro rv opts sie
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
    wp_auto
    by_cases hr : rv = W64 0
    · subst hr
      wp_auto
      have h0 : uint.nat (W64 0) = 0 := rfl
      simp only [h0, _root_.true_and, reduceCtorEq, _root_.or_false, decide_true]
      iapply HΦ
      itrivial
    · rw [decide_eq_false hr]
      wp_auto
      wp_apply Hen as %b Hb
      · ipureintro; decide
      icases Hb with ⟨-, Hb⟩
      ihave %hb := Hb $$ Hon
      subst hb
      (try wp_auto)
      have hn0 : ¬ uint.nat rv = 0 := by intro h; apply hr; word
      simp only [hn0, reduceCtorEq, _root_.or_false, _root_.and_false, decide_false]
      iapply HΦ
      itrivial
  | some v =>
    iunfold sendInitIs at Hsie
    ihave %hnn := typedPointsto_not_null _ _ _ $$ Hsie
    (try wp_auto)
    try rw [decide_eq_false hnn]
    (try wp_auto)
    wp_apply Hen as %b Hb
    · ipureintro; decide
    icases Hb with ⟨-, Hb⟩
    ihave %hb := Hb $$ Hon
    subst hb
    (try wp_auto)
    try rw [decide_eq_false hnn]
    (try wp_auto)
    cases v
    · simp only [reduceCtorEq, false_and, Option.some.injEq, Bool.false_eq_true, or_self, decide_false]
      iapply HΦ
      itrivial
    · simp only [reduceCtorEq, false_and, or_true, decide_true]
      iapply HΦ
      itrivial

end proof

end k8s
end EtcdGrove
end Perennial
