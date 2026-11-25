/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/etcd3/watcher__getStartWatchResourceVersion.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.watcher__getStartWatchResourceVersion
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

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

theorem watcher.getStartWatchResourceVersion.wp_proof :
    watcher.getStartWatchResourceVersion.spec (GF := GF) (hG := hG) := by
  intro wp crv ctx rev opts sie R
  wp_start as ⟨Hlt, #Hcrvf, #Hsie, #Hon, Hcrv⟩
  wp_auto
  rw [show sint.Z (W64 0) = 0 from rfl]
  by_cases hr : 0 < sint.Z rev
  · rw [decide_eq_true hr]
    wp_auto
    iapply HΦ
    iframe Hlt
    simp only [hr, ↓reduceIte]
    itrivial
  rw [decide_eq_false hr]
  wp_auto
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
  wp_apply Hen as %b Hb
  · ipureintro; decide
  icases Hb with ⟨-, Hb⟩
  ihave %hb := Hb $$ Hon
  subst hb
  (try wp_auto)
  iStructNamed opts
  cases sie with
  | none =>
    iunfold sendInitIs at Hsie
    icases Hsie with %hn
    rw [hn]
    wp_auto
    iapply HΦ
    iframe Hlt
    simp only [hr, reduceCtorEq, ↓reduceIte]
    ipureintro; simp
  | some v =>
    iunfold sendInitIs at Hsie
    ihave %hnn := typedPointsto_not_null _ _ _ $$ Hsie
    (try wp_auto)
    try rw [decide_eq_false hnn]
    (try wp_auto)
    cases v with
    | true =>
      wp_auto
      iapply HΦ
      iframe Hlt
      simp only [hr, Option.some.injEq, Bool.true_eq_false, ↓reduceIte]
      ipureintro; simp
    | false =>
      (try wp_auto)
      have hpre : sint.Z rev ≤ 0 ∧ some false = some false := ⟨by omega, rfl⟩
      ispecialize Hcrv $$ %hpre Hlt
      wp_bind (App (Val _) (Val _))
      iapply (wp_wand) $$ [Hcrv]
      · iexact Hcrv
      iintro %v ⟨Hlt, %n, %err, %Hv, HR⟩
      subst Hv
      wp_auto
      cases err with
      | nil =>
        wp_auto
        iapply HΦ
        iframe Hlt
        simp only [hr, ↓reduceIte]
        iexists n
        isplitl [HR]
        · iexact HR
        · ipureintro; simp
      | ok ei =>
        wp_auto
        iapply HΦ
        iframe Hlt
        simp only [hr, ↓reduceIte, reduceCtorEq]
        iexists n
        isplitl [HR]
        · iexact HR
        · ipureintro; simp

end proof

end k8s
end EtcdGrove
end Perennial
