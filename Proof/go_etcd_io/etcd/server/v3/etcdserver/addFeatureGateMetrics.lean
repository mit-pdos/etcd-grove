/-
`addFeatureGateMetrics(fg, gaugeVec)` (`server.go`; see its spec): `fg`'s type assertion to
`MutableFeatureGate` (a `*featureGate`), `GetAll()` (a fresh map of the gate's registered features
`K`, `isFeatureGate`), and for each feature `Enabled` (registered: it is a key of `K`) and the gauge
vector's `With` of the labels `name` and `stage` (the package's `serverFeatureEnabled`, of those
label names by the package's fact; the values valid UTF-8, `featureLabelsOk`), whose `Set` returns.
featuregate-4, 2026-11-23; until then a trust-boundary axiom (server-construction unit N0,
2026-10-16).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.addFeatureGateMetrics
public import Spec.github_com.prometheus.client_golang.prometheus.GaugeVec__With

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode map
open go_etcd_io.etcd.server.v3.etcdserver

/-- A two-entry label map for a two-label vector (`addFeatureGateMetrics`' `name` and `stage`). -/
private theorem labelMapOk_two (a b va vb : GoString) (hab : a ≠ b) (ha : utf8Valid va)
    (hb : utf8Valid vb) :
    prometheus.labelMapOk [a, b] (<[b := vb]> (<[a := va]> (∅ : GMap GoString GoString))) := by
  refine ⟨by simp [hab], ?_, ?_⟩
  · intro k
    by_cases hkb : k = b
    · subst hkb; simp
    · by_cases hka : k = a
      · subst hka; simp [Ne.symm hab]
      · simp [hka, hkb, Ne.symm hka, Ne.symm hkb]
  · intro k w hw
    by_cases hkb : b = k
    · subst hkb; simp at hw; subst hw; exact hb
    · by_cases hka : a = k
      · subst hka; simp [hkb] at hw; subst hw; exact ha
      · simp [hka, hkb] at hw

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem addFeatureGateMetrics.wp_proof
    (wp_With : prometheus.GaugeVec.With.spec (GF := GF) (hG := hG)) :
    addFeatureGateMetrics.spec (GF := GF) (hG := hG) := by
  intro fg gv
  wp_start as ⟨%Hfg, #Hgate, #Hgv⟩
  obtain ⟨p, Hpnn, rfl⟩ := Hfg
  ihave Hsi : (srvInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  iunfold srvInit at Hsi
  icases Hsi with ⟨⟨-, -, -, -, -, ⟨%gvf, #Hgvf, %Hgvfl⟩, -⟩, -⟩
  ihave %Hag := typedPointsto_agree_wand _ _ _ _ _ $$ Hgv Hgvf
  subst Hag
  iunfold isFeatureGate at Hgate
  icases Hgate with ⟨%fi, %K, %Hfi, ⟨%HKs, %HKl⟩, #HEn, #HGetAll⟩
  ihave #Hppkg : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.prometheus.client_golang.prometheus $$ []
  · iPkgInit
  cases Hfi
  wp_auto
  have hset : go.typeSetContains
      (go.GoType.PointerType _root_.Perennial.go_etcd_io.etcd.pkg.v3.featuregate.featureGate.ty)
      _root_.Perennial.go_etcd_io.etcd.pkg.v3.featuregate.MutableFeatureGate.ty = true := by
    go_type_set
  simp only [hset, ↓reduceIte]
  wp_auto
  wp_apply HGetAll as %m Hm
  ipersist fg
  ipersist guageVec
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (_ : List GoString) (_ : Int) => iprop(
      (∃ x : GoString, feature_ptr ↦ x) ∗
      (∃ y : _root_.Perennial.go_etcd_io.etcd.pkg.v3.featuregate.FeatureSpec, featureSpec_ptr ↦ y)))
    $$ Hm
  iintro %keys -
  isplitl [feature featureSpec]
  · isplitl [feature]
    · iexists _; iexact feature
    · iexists _; iexact featureSpec
  isplitr
  · imodintro
    iintro %i %key %sp ⟨-, %Hkv⟩ ⟨⟨%x, feature⟩, ⟨%y, featureSpec⟩⟩
    wp_auto
    wp_apply HEn $$ [] as %b -
    · ipureintro; simp [Hkv]
    have Hlab := HKl key sp Hkv
    cases b <;> wp_auto <;>
    · wp_apply wp_map_make1 (K := GoString) (V := GoString) as %lm Hlm
      wp_apply wp_mapInsert go.string lm _ _ _ $$ [$Hlm] as Hlm
      wp_apply wp_mapInsert go.string lm _ _ _ $$ [$Hlm] as Hlm
      (try wp_auto)
      wp_apply wp_With gv lm [go!"name", go!"stage"] _ _ $$ [Hlm] as %g ⟨%gi, %Hg, #Hgset, -⟩
      · iframe Hlm; ipureintro
        exact ⟨Hgvfl, labelMapOk_two _ _ _ _ (by decide) Hlab.1 Hlab.2⟩
      subst Hg
      (try wp_auto)
      wp_apply Hgset
      (try wp_auto)
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      isplitl [feature]
      · iexists _; iexact feature
      · iexists _; iexact featureSpec
  · iintro - -
    wp_auto
    iapply HΦ
    itrivial

end proof

end EtcdGrove
end Perennial
