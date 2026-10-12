module
public import Spec.go_etcd_io.bbolt.internal.freelist.shared__Copyall
public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas
public import Spec.go_etcd_io.bbolt.internal.freelist.shared__PendingCount
public import Spec.go_etcd_io.bbolt.internal.freelist.shared__pendingPageIds
public import Spec.sort.Sort
public import Spec.go_etcd_io.bbolt.internal.common.Mergepgids

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.freelist

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

theorem shared.Copyall.wp_proof (hPC : shared.PendingCount.spec (GF := GF) (hG := hG))
    (hPP : shared.pendingPageIds.spec (GF := GF) (hG := hG))
    (hSort : sort.Sort.spec (GF := GF) (hG := hG))
    (hMerge : Mergepgids.spec (GF := GF) (hG := hG)) :
    shared.Copyall.spec (GF := GF) (hG := hG) := by
  intro I s σ dst ds hFPI Hds
  wp_start as ⟨Hsh, Hown, Hdst⟩
  ihave #Hc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  wp_auto
  wp_bind (App (Val #(methods (go.GoType.PointerType shared.ty) go!"PendingCount" #s)) (Val #()))
  iapply (hPC s _ σ) $$ [Hsh]
  · iframe Hsh; iexact Hpkg
  inext
  iintro Hsh
  try wp_auto
  unfold ownShared ownSharedC
  icases Hsh with ⟨%sv, %c, Hsh, %Hok⟩
  iNamed Hsh
  have Hpc : σ.pendingCount < 2 ^ 63 := by
    have := Hok.2.2.2.2.1
    unfold FLState.allIds at this; unfold FLState.pendingCount
    simp only [List.length_append] at this; omega
  wp_apply (wp_slice_make3 (V := w64) (W64 0) (W64 (σ.pendingCount : Int)) ⟨by word, by word⟩)
    as %msl ⟨Hm, Hmcap, -⟩
  try wp_auto
  wp_bind (App (Val #(methods (go.GoType.PointerType shared.ty) go!"pendingPageIds" #s)) (Val #()))
  iapply (hPP s sv (DFrac.own 1)) $$ [Hs]
  · iframe Hs; iexact Hpkg
  inext
  iintro Hs
  try wp_auto
  ihave %Hdom := BigSepM2.bigSepM2_lookup_iff $$ Hpds
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List w64) (i : Int) => iprop(∃ (tp : Loc) (ml : GoSlice),
      "%Hi" ∷ ⌜0 ≤ i⌝ ∗
      "Hpds" ∷ ([∗map] _t ↦ p;pd ∈ pp;σ.pending, ownPending p pd) ∗
      "txp" ∷ txp_ptr ↦ tp ∗ "m" ∷ m_ptr ↦ ml ∗
      "Hm" ∷ ml ↦* (keys.take i.toNat).flatMap (fun t => (σ.pendingOf t).ids) ∗
      "Hmcap" ∷ ownSliceCap w64 ml (DFrac.own 1))) $$ Hpending
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [Hpds txp m Hm Hmcap]
  · iexists _, msl
    simp only [Int.toNat_zero, List.take_zero, List.flatMap_nil]
    iframe
    ipureintro; exact Int.le_refl _
  isplitr
  · imodintro
    iintro %i %key %p ⟨%Hkey, %Hp⟩ HP
    iNamed HP
    obtain ⟨pd, Hpd⟩ := Option.isSome_iff_exists.1
      ((Hdom key).1 (by simp only [show Std.get? pp key = some p from Hp, Option.isSome_some]))
    icases BigSepM2.bigSepM2_lookup_acc Hp Hpd $$ Hpds with ⟨Hpo, Hback2⟩
    iNamed Hpo
    wp_auto
    wp_apply wp_slice_append $$ [Hm Hmcap Hids] as %ml2 ⟨Hm, Hmcap, Hids⟩
    · iframe
    try wp_auto
    ihave Hpds := Hback2 $$ [Hp Hids Hids_cap Hatx Hatx_cap]
    · unfold ownPending; iexists tv; iframe; ipureintro; exact Hlrb
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists p, ml2
    have Htake : keys.take (i + 1).toNat = keys.take i.toNat ++ [key] := by
      rw [show (i + 1).toNat = i.toNat + 1 by omega, List.take_add_one, Hkey]; rfl
    have Hpo : σ.pendingOf key = pd := by
      simp [FLState.pendingOf, show σ.pending !! key = some pd from Hpd]
    rw [Htake, List.flatMap_append, List.flatMap_singleton, Hpo]
    iframe
    ipureintro; omega
  iintro HP Hpending
  iNamed HP
  rw [show (GMap.size pp : Int).toNat = keys.length by omega, List.take_length] at *
  have Hperm := pendingIds_perm_keys σ keys (fun k => (Hkset k).trans (Hdom k)) Hknodup
  try wp_auto
  wp_apply (hSort _ ml _ (Or.inl rfl)) $$ [Hm] as %ys ⟨%Hys, Hm⟩
  · iexact Hm
  try wp_auto
  wp_method_call
  wp_call
  wp_auto
  rw [Hiface]
  unfold FLImpl.iface
  wp_auto
  wp_bind (App (Val #(methods I.ity go!"freePageIds" I.iv)) (Val #()))
  iapply (hFPI s σ.free) $$ Hown
  inext
  iintro %r ⟨Hr, Hback⟩
  try wp_auto
  have Hyl : ys.length = σ.pendingIds.length := by rw [Hys.2.length_eq, Hperm.length_eq]
  have Hal : σ.free.length + ys.length = σ.allIds.length := by
    unfold FLState.allIds; rw [List.length_append, Hyl]
  wp_apply (hMerge dst r ml ds σ.free ys (DFrac.own 1) (DFrac.own 1) (by omega)
    (pgidsSorted_of_incr Hok.2.2.2.1) Hys.1) $$ [Hdst Hr Hm] as %out ⟨%Hout, Hdst, Hr, Hm⟩
  · iframe
  try wp_auto
  ihave Hown := Hback $$ Hr
  iapply HΦ
  rw [Hal]
  iframe
  isplitr
  · ipureintro
    refine ⟨Hout.1, Hout.2.trans ?_⟩
    unfold FLState.allIds
    exact List.Perm.append_left _ (Hys.2.trans Hperm)
  ipureintro; exact ⟨Hiface, Hok⟩

end proof

end bbolt
end EtcdGrove
end Perennial
