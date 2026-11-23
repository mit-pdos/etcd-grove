/-
`features.NewDefaultServerFeatureGate` (see its spec): `featuregate.New` of `fmt.Sprintf`'s name,
`Add(DefaultEtcdServerFeatureGates)` (the server's features are not featuregate's own: `addCompat`,
so no error and no panic), the gate given up read-only (`ownGate_freeze`), and `Enabled`'s spec
(the server's features are registered) gives the contract. featuregate-3, 2026-11-23; until then a
trust-boundary axiom (2026-10-18, item 9, point 7).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.features.NewDefaultServerFeatureGate
public import Spec.go_etcd_io.etcd.pkg.v3.featuregate.New
public import Spec.go_etcd_io.etcd.pkg.v3.featuregate.featureGate__Add
public import Spec.go_etcd_io.etcd.pkg.v3.featuregate.featureGate__Enabled
public import Spec.go_etcd_io.etcd.pkg.v3.featuregate.featureGate__GetAll
public import Perennial.Proof.fmt.Results

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode map go_etcd_io.etcd.server.v3

/-- The server's features are not featuregate's own (`AllAlpha`, `AllBeta`). -/
theorem serverFeatureSpecs_addCompat [GooseExts] :
    featuregate.addCompat serverFeatureSpecs featuregate.defaultKnown := by
  intro k v h
  left
  by_cases h1 : go!"AllBeta" = k
  · subst h1
    simp (config := { decide := true }) [serverFeatureSpecs, GMap.lookup_insert_eq_iff] at h
  by_cases h2 : go!"AllAlpha" = k
  · subst h2
    simp (config := { decide := true }) [serverFeatureSpecs, GMap.lookup_insert_eq_iff] at h
  simp [featuregate.defaultKnown, GMap.lookup_insert_eq_iff, h1, h2]

/-- The server's features are registered in the gate `NewDefaultServerFeatureGate` makes. -/
theorem serverFeatures_registered [GooseExts] (f : GoString) (hf : f ∈ serverFeatures) :
    ((serverFeatureSpecs ∪ featuregate.defaultKnown) !! f).isSome := by
  simp only [serverFeatures, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with h|h|h|h|h|h|h|h|h|h <;> subst h <;>
    simp (config := { decide := true }) [serverFeatureSpecs, GMap.lookup_insert_eq_iff]

/-- The gate's features (the server's and featuregate's own) make valid metric labels: ASCII names
and `PreRelease`s. -/
theorem serverGate_featureLabelsOk [GooseExts] :
    featureLabelsOk (serverFeatureSpecs ∪ featuregate.defaultKnown) := by
  apply featureLabelsOk_union
  all_goals
    try unfold serverFeatureSpecs
    try unfold featuregate.defaultKnown
    repeat (apply featureLabelsOk_insert _ _ _ (by decide) (by dsimp only; decide))
    exact featureLabelsOk_empty

/-- `CompactHashCheck` and `LeaseCheckpoint` are off by default, and nothing sets them. -/
theorem gateValue_CompactHashCheck [GooseExts] :
    featuregate.gateValue (serverFeatureSpecs ∪ featuregate.defaultKnown) ∅ go!"CompactHashCheck" =
      false := by
  simp (config := { decide := true }) [featuregate.gateValue, serverFeatureSpecs,
    GMap.lookup_insert_eq_iff, featuregate.spec]

theorem gateValue_LeaseCheckpoint [GooseExts] :
    featuregate.gateValue (serverFeatureSpecs ∪ featuregate.defaultKnown) ∅ go!"LeaseCheckpoint" =
      false := by
  simp (config := { decide := true }) [featuregate.gateValue, serverFeatureSpecs,
    GMap.lookup_insert_eq_iff, featuregate.spec]

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : features.Assumptions]

theorem features.NewDefaultServerFeatureGate.wp_proof
    (wp_New : featuregate.New.spec (GF := GF) (hG := hG))
    (wp_Add : featuregate.featureGate.Add.spec (GF := GF) (hG := hG))
    (wp_Enabled : featuregate.featureGate.Enabled.spec (GF := GF) (hG := hG))
    (wp_GetAll : featuregate.featureGate.GetAll.spec (GF := GF) (hG := hG)) :
    features.NewDefaultServerFeatureGate.spec (GF := GF) (hG := hG) := by
  intro name lg
  wp_start as #Hpkg
  ihave #Hfact : featuresInit (GF := GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  iunfold featuresInit at Hfact
  icases Hfact with ⟨%m, #Hdm, #Hm⟩
  wp_auto
  wp_apply wp_slice_literal (V := GoInterface) [interface.mkOk go.string #name]
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_auto
  wp_apply _root_.Perennial.fmt.wp_Sprintf_argsWf _ _ _ _
    (_root_.Perennial.fmt.ArgsWf.cons_string name _ _root_.Perennial.fmt.ArgsWf.nil) $$ [$Hsl]
    as %gname -
  wp_apply wp_New as %p ⟨%Hpnn, Hg⟩
  wp_apply +noauto (wp_Add p m featuregate.defaultKnown serverFeatureSpecs ∅ DFrac.discard
    serverFeatureSpecs_addCompat) $$ [Hg] as ⟨Hg, -⟩
  · iframe Hg; iexact Hm
  imod (featuregate.ownGate_freeze _ _ _) $$ Hg with #Hgate
  ihave #Hfg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.featuregate $$ []
  · iPkgInit
  try wp_auto
  iapply HΦ
  isplitr
  · ipureintro; exact Hpnn
  isplitl []
  · unfold isFeatureGate
    iexists _, (serverFeatureSpecs ∪ featuregate.defaultKnown)
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; exact ⟨serverFeatures_registered, serverGate_featureLabelsOk⟩
    isplitr
    · iintro %f
      imodintro
      iintro %Φ' %hf
      imodintro
      iintro HΦ'
      wp_apply (wp_Enabled p _ ∅ f (Or.inr hf))
      · iexact Hgate
      iapply HΦ'
      itrivial
    · iintro !> %Φ'
      imodintro
      iintro - HΦ'
      wp_apply (wp_GetAll p _ ∅) as %m Hm
      · iexact Hgate
      iapply HΦ'
      iexact Hm
  isplitl []
  · unfold featureIs
    iexists _
    isplitr
    · ipureintro; rfl
    iintro !> %Φ'
    imodintro
    iintro - HΦ'
    wp_apply (wp_Enabled p _ ∅ go!"CompactHashCheck"
      (Or.inr (serverFeatures_registered _ (by simp [serverFeatures]))))
    · iexact Hgate
    rw [gateValue_CompactHashCheck]
    iapply HΦ'
    itrivial
  · unfold featureIs
    iexists _
    isplitr
    · ipureintro; rfl
    iintro !> %Φ'
    imodintro
    iintro - HΦ'
    wp_apply (wp_Enabled p _ ∅ go!"LeaseCheckpoint"
      (Or.inr (serverFeatures_registered _ (by simp [serverFeatures]))))
    · iexact Hgate
    rw [gateValue_LeaseCheckpoint]
    iapply HΦ'
    itrivial

end proof

end EtcdGrove
end Perennial
