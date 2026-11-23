/-
`featuregate.New` (see its spec): `maps.Clone(defaultFeatures)` (Perennial's `maps.wp_Clone`; the
clone made read-only), a fresh `featureGate` (its mutex given no invariant), the clone and an empty
map stored into its fresh `Value`s.
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.featuregate.New
public import Spec.go_uber_org.zap.NewNop
public import Perennial.Proof.sync.atomic.Link
public import Perennial.Proof.maps.Link

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode map

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.go_etcd_io.etcd.pkg.v3.featuregate.Assumptions]

theorem featuregate.New.wp_proof
    (wp_NewNop : zap.NewNop.spec (GF := GF) (hG := hG)) :
    featuregate.New.spec (GF := GF) (hG := hG) := by
  intro name lg
  wp_start as #Hpkg
  ihave #Hfact : featuregate.featuregateInit (GF := GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  iunfold featuregate.featuregateInit at Hfact
  icases Hfact with ⟨%dm, %sm, #Hdf, #Hdm, #Hsf⟩
  wp_alloc res as Hres
  wp_auto
  wp_if_destruct
  all_goals
    try (wp_apply wp_NewNop as %l -)
    try wp_auto
    wp_apply (_root_.Perennial.maps.wp_Clone (K := GoString)
      (V := _root_.Perennial.go_etcd_io.etcd.pkg.v3.featuregate.FeatureSpec)).1 $$ Hdm as %km ⟨-, Hkm⟩
    try wp_auto
    icases typedPointsto_not_null_dup _ _ _ $$ «$r0» with ⟨«$r0», %Hpnn⟩
    iStructNamed «$r0»
    imod (sync.init_Mutex iprop(True) ⊤ _) $$ lock [] with #Hmu
    · inext; itrivial
    ihave Hkn := (sync.atomic.ownValue_zero _ _).1 $$ known
    ihave Hen := (sync.atomic.ownValue_zero _ _).1 $$ enabled
    wp_apply_core sync.atomic.Value.wp_Store _ _ (by simp) $$ [] [-]
    · iPkgInit
    iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ from Std.LawfulSet.empty_subset)
    iintro Hcl
    inext
    iexists _
    iframe Hkn
    isplitr
    · ipureintro; trivial
    iintro Hkn
    imod Hcl with -
    imodintro
    wp_auto
    wp_apply (wp_map_make1 (K := GoString) (V := Bool)
      _root_.Perennial.go_etcd_io.etcd.pkg.v3.featuregate.Feature.ty go.bool) as %em Hem
    try wp_auto
    wp_apply_core sync.atomic.Value.wp_Store _ _ (by simp) $$ [] [-]
    · iPkgInit
    iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ from Std.LawfulSet.empty_subset)
    iintro Hcl
    inext
    iexists _
    iframe Hen
    isplitr
    · ipureintro; trivial
    iintro Hen
    imod Hcl with -
    imodintro
    ipersist Hkm
    ipersist Hem
    wp_auto
    iapply HΦ
    isplitr
    · ipureintro; exact Hpnn
    unfold featuregate.ownGate
    iexists km, em
    iframe
    isplitl []
    · iexact Hmu
    isplitl []
    · iexact Hkm
    · iexact Hem

end proof

end EtcdGrove
end Perennial
