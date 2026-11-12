/-
`shared.Free(txid, p)` (U2 internal).
-/
module

public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.Callees
public import Spec.go_etcd_io.bbolt.internal.common.Page__Id
public import Spec.go_etcd_io.bbolt.internal.common.Page__Overflow

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

abbrev shared.Free.spec : Prop :=
  ∀ (s : Loc) (fli : GoInterface) (fl : FLPg) (txid : w64) (p : Loc)
    (hdr : go_etcd_io.bbolt.internal.common.Page) (dq : DFrac),
  fl.canFree txid hdr.id' (1 + hdr.overflow'.toNat) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗
      ownSh s fli fl ∗ p ↦{dq} hdr }}
    (App (App (Val #(methods (go.GoType.PointerType shared.ty) go!"Free" #s)) (Val #txid)) (Val #p))
  {{ RET #(); ownSh s fli (fl.freePages txid hdr.id' (1 + hdr.overflow'.toNat)) ∗ p ↦{dq} hdr }}

theorem shared.Free.wp_proof
    (hId : _root_.Perennial.EtcdGrove.bbolt.internal.common.Page.Id.spec (GF := GF) (hG := hG))
    (hOv : _root_.Perennial.EtcdGrove.bbolt.internal.common.Page.Overflow.spec (GF := GF) (hG := hG))
    (hVerify : _root_.Perennial.EtcdGrove.bbolt.internal.common.Verify.spec (GF := GF) (hG := hG)) :
    shared.Free.spec (GF := GF) (hG := hG) := by
  intro s fli fl txid p pv dq Hcan
  wp_start as ⟨Hsh, Hp⟩
  ihave #Hc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  iunfold ownSh at Hsh
  icases Hsh with ⟨%c, Hsh, %Hok⟩
  iunfold ownShC at Hsh
  iNamed Hsh
  obtain ⟨Hid2, Hidb, Hncached, Hatx, Hlen⟩ := Hcan
  ihave %Hdom := BigSepM2.bigSepM2_lookup_iff $$ Hpds
  wp_auto
  wp_apply (hId p pv dq) $$ [Hp] as Hp
  · iframe
  rw [decide_eq_false (show ¬ uint.Z pv.id' ≤ uint.Z (W64 1) by word)]
  try wp_auto
  wp_apply wp_map_lookup1 $$ [Hpending] as Hpending
  · iexact Hpending
  try wp_auto
  wp_join iprop(∃ (tp : Loc), "txp" ∷ txp_ptr ↦ tp ∗
      "Hpending" ∷ pe ↦$ (<[txid := tp]> pp) ∗
      "Hpd" ∷ ownPend tp (fl.pendingOf txid) ∗
      "Hpds" ∷ ([∗map] _t ↦ p;pd ∈ GMap.delete txid pp;GMap.delete txid fl.pending, ownPend p pd) ∗
      "Hpe" ∷ structFieldRef shared go!"pending" s ↦ pe ∗ "t" ∷ t_ptr ↦ s ∗ "txid" ∷ txid_ptr ↦ txid)
    with [txp Hpending Hpds Hpe t txid] as ⟨%tp, txp, Hpending, Hpd, Hpds, Hpe, t, txid⟩
  · rcases hpt : pp !! txid with _ | p0
    rotate_left
    · rw [hpt] at Hif
      simp only [Option.getD_some] at Hif
      obtain ⟨pd0, hpd0⟩ := Option.isSome_iff_exists.1
        ((Hdom txid).1 (by simp only [show Std.get? pp txid = some p0 from hpt, Option.isSome_some]))
      icases BigSepM2.bigSepM2_lookup_acc (show Std.get? pp txid = some p0 from hpt) hpd0 $$ Hpds
        with ⟨Hpo, -⟩
      iunfold ownPend at Hpo
      icases Hpo with ⟨%Hnn, -⟩
      exact absurd Hif Hnn
    have hpd : fl.pending !! txid = none := by
      have := Hdom txid
      simp only [show Std.get? pp txid = pp !! txid from rfl, hpt, Option.isSome_none] at this
      cases h : fl.pending !! txid
      · rfl
      · simp [show Std.get? fl.pending txid = fl.pending !! txid from rfl, h] at this
    try wp_auto
    wp_apply wp_mapInsert $$ [Hpending] as Hpending
    · iexact Hpending
    wp_join_done
    iexists «$r0_ptr»
    iframe
    rw [delete_of_none hpt, delete_of_none hpd]
    iframe
    ihave %Hnn := typedPointsto_not_null _ _ _ $$ «$r0»
    iStructNamed «$r0»
    iunfold ownPend
    isplitr
    · ipureintro; exact Hnn
    iunfold ownPending
    iexists slice.nil, slice.nil
    simp only [FLPg.pendingOf, hpd, Option.getD_none]
    iframe
    isplitl []
    · iapply ownSlice_nil
    isplitl []
    · iapply ownSliceCap_nil
    isplitl []
    · iapply ownSlice_nil
    iapply ownSliceCap_nil
  · rcases hpt : pp !! txid with _ | p0
    · rw [hpt] at Hif; exact absurd rfl Hif
    obtain ⟨pd0, hpd0⟩ := Option.isSome_iff_exists.1
      ((Hdom txid).1 (by simp only [show Std.get? pp txid = some p0 from hpt, Option.isSome_some]))
    icases (BigSepM2.bigSepM2_delete (show Std.get? pp txid = some p0 from hpt) hpd0).1 $$ Hpds
      with ⟨Hpo, Hpds⟩
    iexists p0
    rw [GMap.insert_id pp txid p0 hpt]
    simp only [Option.getD_some]
    iframe
    simp only [FLPg.pendingOf, show fl.pending !! txid = some pd0 from hpd0, Option.getD_some]
    iframe
  wp_apply (hId p pv dq) $$ [Hp] as Hp
  · iframe
  wp_apply wp_map_lookup2 $$ [Hallocs] as Hallocs
  · iexact Hallocs
  try wp_auto
  wp_apply (hVerify _ iprop(allocTxid_ptr ↦ (fl.allocs !! pv.id').getD (zero_val w64) ∗
      txid_ptr ↦ txid)) $$ [allocTxid txid]
  · isplit
    · wp_auto
      wp_if_destruct
      · first | exact absurd rfl Hatx | exact absurd ‹_› Hatx | exact absurd (Eq.symm ‹_›) Hatx
      try wp_auto
      iframe
    · iframe
  iintro ⟨allocTxid, txid⟩
  try wp_auto
  wp_join iprop(al ↦$ GMap.delete pv.id' fl.allocs ∗ structFieldRef shared go!"allocs" s ↦ al ∗
      t_ptr ↦ s ∗ p ↦{dq} pv ∗ p_ptr ↦ p)
    with [Hallocs Hal t Hp p] as ⟨Hallocs, Hal, t, Hp, p⟩
  · try wp_auto
    wp_apply (hId p pv dq) $$ [Hp] as Hp
    · iframe
    wp_apply wp_mapDelete $$ [Hallocs] as Hallocs
    · iexact Hallocs
    wp_join_done
  · have h : fl.allocs !! pv.id' = none := by
      cases h : fl.allocs !! pv.id' <;> simp_all
    rw [delete_of_none h]
    iframe
  wp_apply (hId p pv dq) $$ [Hp] as Hp
  · iframe
  iunfold ownPend at Hpd
  icases Hpd with ⟨%Htpnn, Hpd⟩
  iunfold ownPending at Hpd
  icases Hpd with ⟨%ids0, %atx0, Hidsf, Hids, Hids_cap, Hatxf, Hatx, Hatx_cap, Hlrb⟩
  have Hn : pv.id'.toNat + (pv.overflow'.toNat + 1 : Nat) ≤ 2 ^ 64 := by omega
  ihave IH : iprop(∃ (m : Nat) (ids atx : GoSlice) (cm : GMap w64 Unit),
      "id" ∷ id_ptr ↦ (pv.id' + W64 (m : Int)) ∗
      "Hidsf" ∷ structFieldRef txPending go!"ids" tp ↦ ids ∗
      "Hids" ∷ ids ↦* ((fl.pendingOf txid).ids ++ runIds pv.id' m) ∗
      "Hids_cap" ∷ ownSliceCap w64 ids (DFrac.own 1) ∗
      "Hatxf" ∷ structFieldRef txPending go!"alloctx" tp ↦ atx ∗
      "Hatx" ∷ atx ↦* ((fl.pendingOf txid).alloctx ++
        List.replicate m ((fl.allocs !! pv.id').getD 0)) ∗
      "Hatx_cap" ∷ ownSliceCap w64 atx (DFrac.own 1) ∗
      "Hcache" ∷ ca ↦$ cm ∗ "Hp" ∷ p ↦{dq} pv ∗
      "%Hm" ∷ ⌜m ≤ pv.overflow'.toNat + 1 ∧
        ∀ x, (cm !! x).isSome ↔ (c !! x).isSome ∨ x ∈ runIds pv.id' m⌝)
      $$ [id Hidsf Hids Hids_cap Hatxf Hatx Hatx_cap Hcache Hp]
  · iexists 0, ids0, atx0, c
    simp only [runIds, List.range_zero, List.map_nil, List.append_nil, List.replicate_zero]
    rw [show pv.id' + W64 ((0 : Nat) : Int) = pv.id' by word]
    iframe
    ipureintro
    exact ⟨by omega, fun x => by simp⟩
  wp_for IH
  wp_apply (hId p pv dq) $$ [Hp] as Hp
  · iframe
  try wp_auto
  wp_apply (hOv p pv dq) $$ [Hp] as Hp
  · iframe
  try wp_auto
  have hiff : uint.Z (pv.id' + W64 (m : Int)) ≤ uint.Z (pv.id' + W64 (uint.Z pv.overflow')) ↔
      m < pv.overflow'.toNat + 1 := by
    constructor <;> intro h <;> word
  wp_if_destruct
  · have hlt := hiff.1 (of_decide_eq_true (go.intoVal_inj Hif))
    try wp_auto
    wp_apply wp_map_lookup2 $$ [Hcache] as Hcache
    · iexact Hcache
    have hx : (cm !! (pv.id' + W64 (m : Int))).isSome = false := by
      cases h : (cm !! (pv.id' + W64 (m : Int))).isSome
      · rfl
      · exfalso
        rcases (Hm.2 _).1 h with h' | h'
        · apply Hncached _ ?_ ((Hok.1 _).1 h')
          rw [mem_runIds (by omega)]; constructor <;> word
        · have := ((mem_runIds (by omega)).1 h').2; word
    rw [hx]
    try wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply wp_slice_append $$ [Hids Hids_cap Hsl] as %ids2 ⟨Hids, Hids_cap, -⟩
    · iframe
    try wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    wp_apply wp_slice_append $$ [Hatx Hatx_cap Hsl2] as %atx2 ⟨Hatx, Hatx_cap, -⟩
    · iframe
    try wp_auto
    wp_apply wp_mapInsert $$ [Hcache] as Hcache
    · iexact Hcache
    try wp_auto
    wp_for_post
    iframe
    iexists (m + 1), ids2, atx2, (<[pv.id' + W64 (m : Int) := ()]> cm)
    rw [runIds_succ, List.replicate_succ', ← List.append_assoc, ← List.append_assoc,
      show pv.id' + W64 ((m + 1 : Nat) : Int) = pv.id' + W64 (m : Int) + W64 1 by word]
    iframe
    ipureintro
    refine ⟨by omega, fun x => ?_⟩
    by_cases hx : pv.id' + W64 (m : Int) = x
    · subst hx; simp
    · rw [GMap.lookup_insert_ne _ _ hx, Hm.2 x]
      simp only [List.mem_append, List.mem_singleton]
      constructor
      · rintro (h | h); exact Or.inl h; exact Or.inr (Or.inl h)
      · rintro (h | h | h); exact Or.inl h; exact Or.inr h; exact absurd h.symm hx
  · try wp_auto
    have hmn : m = pv.overflow'.toNat + 1 := by
      have := Hm.1
      have : ¬ m < pv.overflow'.toNat + 1 := fun h => Hif (by rw [decide_eq_true (hiff.2 h)])
      omega
    subst hmn
    have hP : ¬ (uint.Z (pv.id' + W64 ((pv.overflow'.toNat + 1 : Nat) : Int)) ≤
        uint.Z (pv.id' + W64 (uint.Z pv.overflow'))) := fun h => by have := hiff.1 h; omega
    simp only [hP, decide_false]
    try simp only [decide_true, ↓reduceIte]
    try simp only [Bool.false_eq_true, ↓reduceIte]
    try wp_auto
    obtain ⟨Hcached', Hwf'⟩ := freePages_ok (txid := txid) Hok.2
      ⟨Hid2, Hidb, Hncached, Hatx, Hlen⟩
    iapply HΦ
    iframe Hp
    iunfold ownSh
    iexists cm
    isplitl
    · iunfold ownShC
      iexists al, ca, pe, (<[txid := tp]> pp)
      simp only [FLPg.freePages]
      iframe
      iapply (BigSepM2.bigSepM2_insert_delete).2
      iframe
      iunfold ownPend
      isplitr
      · ipureintro; exact Htpnn
      iunfold ownPending
      iexists ids, atx
      isimp only [FLPg.pendingOf] at Hids Hatx
      rw [show 1 + pv.overflow'.toNat = pv.overflow'.toNat + 1 by omega]
      iframe
    · ipureintro
      refine ⟨fun x => ?_, Hwf'⟩
      rw [Hm.2 x, Hcached' x, Hok.1 x]
      rw [show 1 + pv.overflow'.toNat = pv.overflow'.toNat + 1 by omega]
end proof

end freelist
end internal
end bbolt
end EtcdGrove
end Perennial
