/-
`shared.Copyall(dst)` (U2 internal): the free and pending ids, sorted, into `dst`.
-/
module

public import Proof.go_etcd_io.bbolt.internal.freelist.Impl.shared__PendingCount
public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.Sorters
public import Spec.go_etcd_io.bbolt.internal.common.Mergepgids

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs
namespace internal
namespace freelist

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.freelist

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

/-- `t.Copyall(dst)`: the free and pending ids, sorted, at the start of `dst` (which has room
for them). -/
abbrev shared.Copyall.spec (I : FLImpl (GF := GF)) : Prop :=
  ∀ (s : Loc) (fl : FLPg) (dst : GoSlice) (ds : List w64),
  fl.allIds.length ≤ ds.length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗
      ownSh s I.iface fl ∗ I.own fl.free ∗ dst ↦* ds }}
    (App (Val #(methods (go.GoType.PointerType shared.ty) go!"Copyall" #s)) (Val #dst))
  {{ RET #(); ownSh s I.iface fl ∗ I.own fl.free ∗
      dst ↦* (sortPgids fl.allIds ++ ds.drop fl.allIds.length) }}

theorem shared.Copyall.wp_proof (I : FLImpl (GF := GF)) (hF : I.FreePageIdsSpec)
    (hMerge : _root_.Perennial.EtcdGrove.bbolt.Mergepgids.spec (GF := GF) (hG := hG)) :
    shared.Copyall.spec I := by
  intro s fl dst ds Hds
  wp_start as ⟨Hsh, Hown, Hdst⟩
  ihave #Hc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  ihave #Hsp : isPkgInit (PROP := IProp GF) pkg_id.sort $$ []
  · iPkgInit
  iunfold ownSh at Hsh
  icases Hsh with ⟨%c, Hsh, %Hok⟩
  wp_auto
  wp_apply (shared.PendingCount.wp_proof s _ fl c) $$ [Hsh] as Hsh
  · iframe
  iunfold ownShC at Hsh
  iNamed Hsh
  have Hpc : fl.pendingIds.length < 2 ^ 63 := by
    have := Hok.2.2.2.2.1
    unfold FLPg.allIds at this
    simp only [List.length_append] at this; omega
  wp_apply (wp_slice_make3 (V := w64) (W64 0) (W64 (fl.pendingIds.length : Int)) ⟨by word, by word⟩)
    as %msl ⟨Hm, Hmcap, -⟩
  wp_method_call
  wp_call
  wp_auto
  ihave %Hdom := BigSepM2.bigSepM2_lookup_iff $$ Hpds
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List w64) (i : Int) => iprop(∃ (tp : Loc) (ml : GoSlice),
      "%Hi" ∷ ⌜0 ≤ i⌝ ∗
      "Hpds" ∷ ([∗map] _t ↦ p;pd ∈ pp;fl.pending, ownPend p pd) ∗
      "txp" ∷ txp_ptr ↦ tp ∗ "m" ∷ m_ptr ↦ ml ∗
      "Hm" ∷ ml ↦* (keys.take i.toNat).flatMap (fun t => (fl.pendingOf t).ids) ∗
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
    iunfold ownPend at Hpo
    icases Hpo with ⟨%Hpnn, Hpo⟩
    iunfold ownPending at Hpo
    icases Hpo with ⟨%ids, %atx, Hidsf, Hids, Hidc, Hatxf, Hatx, Hatxc, Hlrb⟩
    wp_auto
    wp_apply wp_slice_append $$ [Hm Hmcap Hids] as %ml2 ⟨Hm, Hmcap, Hids⟩
    · iframe
    try wp_auto
    ihave Hpds := Hback2 $$ [Hidsf Hids Hidc Hatxf Hatx Hatxc Hlrb]
    · iunfold ownPend; isplitr
      · ipureintro; exact Hpnn
      iunfold ownPending; iexists ids, atx; iframe
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists p, ml2
    have Htake : keys.take (i + 1).toNat = keys.take i.toNat ++ [key] := by
      rw [show (i + 1).toNat = i.toNat + 1 by omega, List.take_add_one, Hkey]; rfl
    have Hpo : fl.pendingOf key = pd := by
      simp [FLPg.pendingOf, show fl.pending !! key = some pd from Hpd]
    rw [Htake, List.flatMap_append, List.flatMap_singleton, Hpo]
    iframe
    ipureintro; omega
  iintro HP Hpending
  iNamed HP
  rw [show (GMap.size pp : Int).toNat = keys.length by omega, List.take_length] at *
  have Hperm := pendingIds_perm_keys fl keys (fun k => (Hkset k).trans (Hdom k)) Hknodup
  try wp_auto
  icases ownSlice_w64_len _ _ _ $$ Hm with ⟨Hm, %Hmb⟩
  wp_apply (sort.wp_Sort (interface.mk go_etcd_io.bbolt.internal.common.Pgids.ty #ml)
    (fun l => ml ↦* l) pgLt slices.StrictWeakOrder_unsigned_lt _)
    $$ [Hm] as %ys' ⟨Hm, %Hp', %Hsorted⟩
  · iframe
    isplitl []
    · iapply Pgids_isSorter
    ipureintro; omega
  have Hys' := sort_post_eq Hp' Hsorted
  subst Hys'
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  wp_apply (hF fl.free) $$ [Hown] as %r ⟨Hr, Hback⟩
  · iframe
  have Hyl : (sortPgids (keys.flatMap (fun t => (fl.pendingOf t).ids))).length =
      fl.pendingIds.length := by rw [(sortPgids_perm _).length_eq, Hperm.length_eq]
  have Hal : fl.free.length + (sortPgids (keys.flatMap (fun t => (fl.pendingOf t).ids))).length =
      fl.allIds.length := by
    unfold FLPg.allIds; rw [List.length_append, Hyl]
  have Hfs : PgidsSorted fl.free := Hok.2.2.2.1.imp fun h => by simp only [uint.Z]; omega
  have Hsrt : PgidsSorted (sortPgids (keys.flatMap (fun t => (fl.pendingOf t).ids))) :=
    (sortPgids_sorted _).imp fun h => by simp only [uint.Z]; omega
  wp_apply (hMerge dst r ml ds fl.free _ (DFrac.own 1) (DFrac.own 1) (by omega) Hfs Hsrt)
    $$ [Hdst Hr Hm] as %out ⟨%Hout, Hdst, Hr, Hm⟩
  · iframe
  ihave Hown := Hback $$ Hr
  have Hout' : out = sortPgids fl.allIds := by
    refine (sortPgids_eq_of_sorted (Hout.1.imp fun h => by simp only [uint.Z] at h; omega)
      (Hout.2.trans ?_)).symm
    unfold FLPg.allIds
    exact List.Perm.append_left _ ((sortPgids_perm _).trans Hperm)
  rw [Hal, Hout']
  iapply HΦ
  iframe
  iunfold ownSh
  iexists c
  iunfold ownShC
  isplitl
  · iexists al, ca, pe, pp
    iframe
  · ipureintro; exact Hok

end proof

end freelist
end internal
end bbolt
end EtcdGrove
end Perennial
