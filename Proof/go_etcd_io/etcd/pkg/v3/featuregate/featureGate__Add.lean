/-
`(*featureGate).Add` (see its spec): under the gate's lock (no invariant: the caller owns the gate),
`known` loaded and copied (`maps.Copy`, into a fresh map), each of `features` inserted (a known one
skipped: by `addCompat` it has the same spec, so the conflict's error is unreachable), the copy stored
back into `known` (a map of the same type, so the `Store` does not panic).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.featuregate.featureGate__Add
public import Spec.maps.Copy
public import Proof.maps.CopyPrefix
public import Perennial.Proof.sync.atomic.Link
public import Perennial.Proof.sync.Link

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

theorem featuregate.featureGate.Add.wp_proof
    (wp_Copy : maps.Copy.spec (GF := GF) (hG := hG)) :
    featuregate.featureGate.Add.spec (GF := GF) (hG := hG) := by
  intro p fm K F E dq Hcompat
  unfold featuregate.ownGate
  wp_start
  icases Hpre with ⟨⟨%km, %em, #Hmu, Hk, #HK, He, #HE, Hcl⟩, Hfm⟩
  wp_alloc res as Hres
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hmu] as ⟨Hlocked, -⟩
  try wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := _root_.Perennial.go_etcd_io.etcd.pkg.v3.featuregate.FeatureSpec)
    _root_.Perennial.go_etcd_io.etcd.pkg.v3.featuregate.Feature.ty
    _root_.Perennial.go_etcd_io.etcd.pkg.v3.featuregate.FeatureSpec.ty) as %nm Hnm
  try wp_auto
  wp_apply_core sync.atomic.Value.wp_Load _ (DFrac.own 1) $$ [] [-]
  · iPkgInit
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ from Std.LawfulSet.empty_subset)
  iintro Hclose
  inext
  iexists _
  iframe Hk
  iintro Hk
  imod Hclose with -
  imodintro
  try wp_auto
  wp_apply (wp_Copy (K := GoString) (V := _root_.Perennial.go_etcd_io.etcd.pkg.v3.featuregate.FeatureSpec)
    nm km DFrac.discard ∅ K) $$ [Hnm] as ⟨Hnm, -⟩
  · iframe Hnm; iexact HK
  try wp_auto
  rw [GMap.map_union_empty]
  wp_apply (wp_map_for_range (fun keys i => iprop(
      "known" ∷ known_ptr ↦ nm ∗
      "Hnm" ∷ nm ↦$ (maps.copyPrefix F K (keys.take i.toNat)) ∗
      "spec" ∷ (∃ sv : _root_.Perennial.go_etcd_io.etcd.pkg.v3.featuregate.FeatureSpec, spec_ptr ↦ sv) ∗
      "name" ∷ (∃ nv : GoString, name_ptr ↦ nv) ∗
      "%Hi" ∷ ⌜0 ≤ i⌝))) $$ Hfm
  iintro %keys ⟨%Hmem, %Hsize, %Hnd⟩
  isplitl [known Hnm spec name]
  · iframe
    isplitl [Hnm]
    · simp only [Int.toNat_zero, List.take_zero, maps.copyPrefix_nil]
      iexact Hnm
    isplitl [spec]
    · iexists _; iframe
    isplitl [name]
    · iexists _; iframe
    ipureintro; simp
  isplitr
  · imodintro
    iintro %i %key %vl ⟨%Hkey, %Hlook⟩ ⟨known, Hnm, ⟨%sv, spec⟩, ⟨%nv, name⟩, %Hi⟩
    wp_auto
    have htake : keys.take (i + 1).toNat = keys.take i.toNat ++ [key] := by
      rw [show (i + 1).toNat = i.toNat + 1 by omega, List.take_add_one, Hkey]; rfl
    have hnotin := maps.nodup_getElem_notin_take keys i.toNat key Hnd Hkey
    have hlk := maps.copyPrefix_lookup_notin F K _ key hnotin
    wp_apply +noauto wp_map_lookup2 $$ Hnm as Hnm
    rw [hlk]
    cases hK : K !! key with
    | none =>
      simp only [Option.isSome_none, Option.getD_none]
      wp_auto
      wp_apply wp_mapInsert $$ Hnm as Hnm
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iframe
      isplitl [Hnm]
      · rw [htake, ← maps.copyPrefix_snoc F K _ key vl Hlook]
        iexact Hnm
      isplitl [spec]
      · iexists _; iframe
      isplitl [name]
      · iexists _; iframe
      ipureintro; omega
    | some ex =>
      have hex : ex = vl := by
        rcases Hcompat key vl Hlook with h | h <;> rw [hK] at h
        · cases h
        · exact Option.some.inj h
      subst hex
      simp only [Option.isSome_some, _root_.decide_true, Option.getD_some]
      wp_auto
      unfold forMapPostcondition
      ileft
      isplitr
      · ipureintro; rfl
      iframe
      isplitl [Hnm]
      · rw [htake, ← maps.copyPrefix_snoc_same F K _ key ex Hlook (by rw [hlk, hK])]
        iexact Hnm
      isplitl [spec]
      · iexists _; iframe
      isplitl [name]
      · iexists _; iframe
      ipureintro; omega
  · iintro ⟨known, Hnm, spec, name, %Hi⟩ Hfm
    rw [show ((GMap.size F : Nat) : Int).toNat = keys.length by omega, List.take_length,
      maps.copyPrefix_all F K keys Hmem]
    wp_auto
    wp_apply_core sync.atomic.Value.wp_Store _ _ (by simp) $$ [] [-]
    · iPkgInit
    iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ from Std.LawfulSet.empty_subset)
    iintro Hclose
    inext
    iexists _
    iframe Hk
    isplitr
    · ipureintro; rfl
    iintro Hk
    imod Hclose with -
    imodintro
    ipersist Hnm
    wp_auto
    wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked]
    · itrivial
    try wp_auto
    iapply HΦ
    iframe Hfm
    iexists nm, em
    iframe
    isplitl []
    · iexact Hmu
    isplitl []
    · iexact Hnm
    · iexact HE

end proof

end EtcdGrove
end Perennial
