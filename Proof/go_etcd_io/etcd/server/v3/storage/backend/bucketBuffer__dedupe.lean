/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/bucketBuffer__dedupe.lean`.
Lean-first (no Rocq counterpart).

`sort.Stable` sorts the buffer, a `sort.Interface` by its `Len`, `Less` and `Swap`
(`bb_sorter`), into `es.mergeSort entLe`; the loop then keeps, in place, the last entry of each
run of one key: after `ridx` entries the first `widx + 1` slots hold `dedupLast` of the first
`ridx` (`dedupLast_take_succ`), and the slots from `ridx` on are still the sorted entries'.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.bucketBuffer__dedupe
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.bucketBuffer__Len
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.bucketBuffer__Less
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.bucketBuffer__Swap
public import Spec.sort.Stable
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.ModelLemmas
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.MergeLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend backend

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

theorem backend.entsSorted_short (es : List Ent) (h : es.length ≤ 1) : entsSorted es := by
  unfold entsSorted
  match es, h with
  | [], _ => exact List.Pairwise.nil
  | [_], _ => exact List.pairwise_singleton _ _

/-- A bucket buffer is a `sort.Interface` over its entries, ordered by key. -/
theorem backend.bb_sorter
    (hLen : backend.bucketBuffer.Len.spec (GF := GF) (hG := hG))
    (hLess : backend.bucketBuffer.Less.spec (GF := GF) (hG := hG))
    (hSwap : backend.bucketBuffer.Swap.spec (GF := GF) (hG := hG)) (bb : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ⊢
      sorterSpec (interface.mk (go.GoType.PointerType bucketBuffer.ty) #bb) (ownBB bb)
        (fun a b : Ent => decide (strLt a.1 b.1)) := by
  iintro #Hpkg
  unfold sorterSpec
  isplitr
  · imodintro
    iintro %l
    iintro !> %Φ Hl HΦ
    iapply (hLen bb l) $$ [$Hpkg $Hl] HΦ
  isplitr
  · imodintro
    iintro %l %i %j %a %b %Hij
    iintro !> %Φ Hl HΦ
    obtain ⟨hi, hj, ha, hb⟩ := Hij
    iapply (hLess bb l i j a b hi hj ha hb) $$ [$Hpkg $Hl] HΦ
  imodintro
  iintro %l %i %j %a %b %Hij
  iintro !> %Φ Hl HΦ
  obtain ⟨hi, hj, ha, hb⟩ := Hij
  iapply (hSwap bb l i j a b hi hj ha hb) $$ [$Hpkg $Hl] HΦ

theorem backend.bucketBuffer.dedupe.wp_proof
    (hStable : sort.Stable.spec (GF := GF) (hG := hG))
    (hLen : backend.bucketBuffer.Len.spec (GF := GF) (hG := hG))
    (hLess : backend.bucketBuffer.Less.spec (GF := GF) (hG := hG))
    (hSwap : backend.bucketBuffer.Swap.spec (GF := GF) (hG := hG)) :
    backend.bucketBuffer.dedupe.spec (GF := GF) (hG := hG) := by
  intro bb es
  wp_start as Hbb
  iunfold ownBB at Hbb
  icases Hbb with ⟨%p, Hbb, %Hok⟩
  iunfold bbAt at Hbb
  icases Hbb with ⟨Hbb, Hbuf, Hcap, #Hro, #Hents⟩
  have Hlen : es.length < 2 ^ 61 := by unfold bbOk at Hok; omega
  wp_auto
  wp_if_destruct
  · have hc : canon es = es := canon_of_sorted (entsSorted_short es (by word))
    rw [hc]
    iapply HΦ
    iunfold ownBB
    iexists p
    iunfold bbAt
    iframe
    iframe Hro Hents
    ipureintro; exact Hok
  ihave Hbb : ownBB bb es $$ [Hbb Hbuf Hcap]
  · iunfold ownBB
    iexists p
    iunfold bbAt
    iframe
    iframe Hro Hents
    ipureintro; exact Hok
  iclear Hro Hents
  ihave #Hsorter := backend.bb_sorter hLen hLess hSwap bb $$ Hpkg
  wp_apply (hStable Ent (interface.mk (go.GoType.PointerType bucketBuffer.ty) #bb) (ownBB bb)
      (fun a b : Ent => decide (strLt a.1 b.1)) es entLt_swo) $$ [$Hsorter $Hbb] as Hbb
  · ipureintro; omega
  obtain ⟨L, hL⟩ : ∃ L, L = es.mergeSort entLe := ⟨_, rfl⟩
  have hLlen : L.length = es.length := by rw [hL, List.length_mergeSort]
  rw [show (es.mergeSort fun a b : Ent => !decide (strLt b.1 a.1)) = L from hL.symm]
  iunfold ownBB at Hbb
  icases Hbb with ⟨%q, Hbb, %Hokq⟩
  iunfold bbAt at Hbb
  icases Hbb with ⟨Hbb, Hbuf, Hcap, #Hro, #Hents⟩
  ihave %Hql := ownSlice_len _ _ _ $$ Hbuf
  ihave HI : (∃ (r w : w64) (ks : List kv),
      "ridx" ∷ ridx_ptr ↦ r ∗ "widx" ∷ widx_ptr ↦ w ∗
      "Hbuf" ∷ q.buf ↦* ks ∗
      "#Hro" ∷ slotsRO ks ∗
      "#HD" ∷ entsIn ks (dedupLast (L.take (sint.nat r))) ∗
      "#Htail" ∷ entsIn (ks.drop (sint.nat r)) (L.drop (sint.nat r)) ∗
      "%Hr" ∷ ⌜1 ≤ sint.Z r ∧ sint.Z r ≤ L.length ∧ ks.length = q.kvs.length ∧
        sint.nat w + 1 = (dedupLast (L.take (sint.nat r))).length ∧ 0 ≤ sint.Z w⌝ : IProp GF) $$ [ridx widx Hbuf]
  · iexists (W64 1), (W64 0), q.kvs
    iframe
    have h1 : sint.nat (W64 1) = 1 := rfl
    rw [h1, dedupLast_take_one]
    ihave #Ht := entsIn_take_es _ _ 1 $$ Hents
    ihave #Hd := entsIn_drop _ _ 1 $$ Hents
    iframe Hro Ht Hd
    ipureintro
    refine ⟨by word, by word, rfl, ?_, by word⟩
    rw [List.length_take]; word
  iclear Hro Hents
  wp_for HI
  have hNq : L.length < q.kvs.length ∧ q.kvs.length ≤ 2 ^ 61 := ⟨Hokq.1, Hokq.2.2⟩
  have hq2 : 2 ≤ q.kvs.length := Hokq.2.1
  wp_if_destruct
  · obtain ⟨D, hD⟩ : ∃ D, D = dedupLast (L.take (sint.nat r)) := ⟨_, rfl⟩
    rw [← hD] at Hr
    rw [← hD]
    have hrlt : sint.nat r < L.length := by word
    have hbr : 0 ≤ sint.Z r ∧ sint.Z r < sint.Z q.buf.len := by word
    simp only [hbr, _root_.and_self, ite_true]
    list_elem L (sint.nat r) as b
    list_elem L (sint.nat r - 1) as a
    list_elem ks (sint.nat r) as xr
    obtain ⟨hD1, hD2, hD3⟩ := dedupLast_take_facts L (sint.nat r) a (by word) Ha_lookup
    rw [← hD] at hD1 hD2 hD3
    have hw : sint.nat w = D.length - 1 := by omega
    list_elem ks (sint.nat w) as xw
    ihave #Hxr := entsIn_slot (ks.drop (sint.nat r)) (L.drop (sint.nat r)) 0 xr b
      (by rw [List.getElem?_drop, Nat.add_zero]; exact Hxr_lookup)
      (by rw [List.getElem?_drop, Nat.add_zero]; exact Hb_lookup) $$ Htail
    ihave #Hxw := entsIn_slot ks D (sint.nat w) xw a Hxw_lookup (by rw [hw]; exact hD3) $$ HD
    icases Hxr with ⟨#Hxrk, #Hxrv⟩
    icases Hxw with ⟨#Hxwk, #Hxwv⟩
    icases ownSlice_elem_acc (sint.Z r) xr q.buf _ ks (by word) Hxr_lookup $$ Hbuf with ⟨Hel, Hback⟩
    wp_auto
    ihave Hbuf := Hback $$ %xr Hel
    rw [list_set_lookup_self ks (sint.Z r).toNat xr Hxr_lookup]
    have hbw : 0 ≤ sint.Z w ∧ sint.Z w < sint.Z q.buf.len := by
      have h1 := Hr.2.2.2.2; have h2 := Hr.2.2.1; have h3 := Hql.1
      clear hD Hb_lookup Ha_lookup Hxr_lookup hD3 Hxw_lookup hL
      word
    simp only [hbw, _root_.and_self, ite_true]
    icases ownSlice_elem_acc (sint.Z w) xw q.buf _ ks (by word) Hxw_lookup $$ Hbuf with ⟨Hel, Hback⟩
    wp_auto
    ihave Hbuf := Hback $$ %xw Hel
    rw [list_set_lookup_self ks (sint.Z w).toNat xw Hxw_lookup]
    wp_apply bytes.wp_Equal xr.key' xw.key' DFrac.discard DFrac.discard b.1 a.1 $$ [$Hxrk $Hxwk] as ⟨-, -⟩
    obtain ⟨wn, hwn⟩ : ∃ wn : Nat, wn = if a.1 = b.1 then D.length - 1 else D.length := ⟨_, rfl⟩
    have hwnle : wn ≤ D.length := by rw [hwn]; split <;> omega
    wp_join iprop(∃ w' : w64, widx_ptr ↦ w' ∗ ⌜sint.nat w' = wn ∧ 0 ≤ sint.Z w'⌝) with [widx]
      as ⟨%w', widx, %Hw'⟩
    · iexists w
      iframe
      ipureintro
      refine ⟨?_, Hr.2.2.2.2⟩
      rw [hwn, ite_eq_left Hif.symm]; exact hw
    · iexists (w + W64 1)
      iframe
      ipureintro
      have hne : ¬ a.1 = b.1 := fun h => Hif h.symm
      rw [hwn, ite_eq_right hne]
      have h1 := Hr.2.2.2.2; have h2 := Hr.2.2.2.1
      have h3 : D.length < 2 ^ 61 := by omega
      clear hD Hb_lookup Ha_lookup Hxr_lookup hD3 Hxw_lookup hL hwn
      constructor <;> word
    simp only [hbr, _root_.and_self, ite_true]
    wp_apply wp_load_slice_index q.buf (sint.Z r) ks _ xr hbr.1 $$ [Hbuf] as Hbuf
    · iframe; ipureintro; exact Hxr_lookup
    have hwnr : wn < sint.nat r + 1 := by omega
    have hwnk : wn < ks.length := by omega
    have hbw' : 0 ≤ sint.Z w' ∧ sint.Z w' < sint.Z q.buf.len := by
      have h1 := Hw'.1; have h2 := Hw'.2; have h3 := Hr.2.2.1; have h4 := Hql.1
      clear hD Hb_lookup Ha_lookup Hxr_lookup hD3 Hxw_lookup hL hwn
      word
    simp only [hbw', _root_.and_self, ite_true]
    wp_apply wp_store_slice_index q.buf (sint.Z w') ks xr $$ [Hbuf] as Hbuf
    · iframe; ipureintro
      refine ⟨hbw'.1, ?_⟩
      have h3 := Hr.2.2.1; have h4 := Hql.1; have h5 := hbw'.2
      clear hD Hb_lookup Ha_lookup Hxr_lookup hD3 Hxw_lookup hL hwn
      word
    wp_for_post
    have hw'n : (sint.Z w').toNat = wn := Hw'.1
    rw [hw'n]
    have hr1 : sint.nat (r + W64 1) = sint.nat r + 1 := by
      have h1 := Hr.1; have h2 := Hr.2.1
      clear hD Hb_lookup Ha_lookup Hxr_lookup hD3 Hxw_lookup hL hwn
      word
    have hstep := dedupLast_take_succ L (sint.nat r) a b (by omega) Ha_lookup Hb_lookup
    rw [← hD, ← hwn] at hstep
    ihave #HD' := entsIn_set_snoc ks D wn xr b hwnle hwnk $$ [$HD $Hxrk $Hxrv]
    ihave #Hro' := slotsRO_set ks wn xr $$ [$Hro]
    · iexists b.1, b.2; iframe Hxrk Hxrv
    ihave #Htail' := entsIn_drop _ _ 1 $$ Htail
    iframe
    iexists (r + W64 1), w', ks.set wn xr
    rw [hr1, hstep, List.drop_set_of_lt hwnr]
    simp only [List.drop_drop] at *
    iframe
    iframe Hro' HD'
    iframe Htail'
    ipureintro
    refine ⟨by word, by word, by rw [List.length_set]; exact Hr.2.2.1, ?_, Hw'.2⟩
    simp only [List.length_append, List.length_take, List.length_singleton]
    rw [Hw'.1]; omega
  · have hrN : sint.nat r = L.length := by
      have h1 := Hr.1; have h2 := Hr.2.1
      clear hL
      word
    rw [hrN, List.take_length] at Hr
    rw [hrN, List.take_length]
    have hcanon : canon es = dedupLast L := by rw [canon_eq, hL]
    have hDl : (dedupLast L).length ≤ L.length := by
      cases L with
      | nil => exact Nat.le_refl _
      | cons x l => exact (dedupLast_cons_facts x l).2.2
    have hused : w + W64 1 = W64 ((canon es).length : Int) := by
      rw [hcanon]
      have h1 := Hr.2.2.2.1; have h2 := Hr.2.2.2.2
      have h3 : (dedupLast L).length < 2 ^ 61 := by omega
      clear hL hcanon
      word
    rw [hused]
    iapply HΦ
    iunfold ownBB
    iexists { buf := q.buf, kvs := ks }
    iunfold bbAt
    rw [hcanon]
    iframe
    iframe Hro HD
    ipureintro
    unfold bbOk
    refine ⟨by rw [Hr.2.2.1]; omega, by rw [Hr.2.2.1]; exact hq2, by rw [Hr.2.2.1]; exact hNq.2⟩

end proof

end EtcdGrove
end Perennial
