module
public import Spec.go_etcd_io.bbolt.Tx__rollback_w
public import Spec.go_etcd_io.bbolt.Tx__close_w
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Txid
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Freelist
public import Spec.go_etcd_io.bbolt.DB__hasSyncedFreelist
public import Spec.go_etcd_io.bbolt.DB__meta
public import Spec.go_etcd_io.bbolt.DB__page
public import Proof.go_etcd_io.bbolt.DBAcc
public import Proof.go_etcd_io.bbolt.DBBegin

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- The meta `db.meta()` picks, lent out of the two. -/
theorem pick_acc (p : Bool) (l0 l1 : Loc) (v0 v1 : Meta) (q : DFrac) :
    (l0 ↦{q} v0 ∗ l1 ↦{q} v1 : IProp GF) ⊢
      (if p then l1 else l0) ↦{q} (if p then v1 else v0) ∗
      ((if p then l1 else l0) ↦{q} (if p then v1 else v0) -∗ l0 ↦{q} v0 ∗ l1 ↦{q} v1) := by
  cases p
  · simp only [Bool.false_eq_true, ↓reduceIte]
    iintro ⟨H0, H1⟩; iframe H0; iintro H0; iframe
  · simp only [↓reduceIte]
    iintro ⟨H0, H1⟩; iframe H1; iintro H1; iframe

/-- A slot no view sees is the database's whole half. -/
theorem rem_unseen (σ : DBState) (v0 v1 : Meta) (h : dbOK σ v0 v1) (s : Nat)
    (hlt : s < σ.nslots) (hs : slotUnseen σ s) : σ.rem s = halfQ := by
  obtain ⟨-, hr, hw, -⟩ := hs
  have H := h.2.2.2.2.2.2.2.2.2.2.2.1 s hlt
  have hn : readersQ σ.readers (fun r => r.sees s) = none :=
    readersQ_none _ _ (fun k r hk => by
      unfold Reader.sees; simp only [decide_eq_false_iff_not]; exact hr k r hk)
  rw [hn] at H
  unfold wQ at H
  cases hwr : σ.wr with
  | none => rw [hwr] at H; exact H
  | some w' =>
    rw [hwr] at H
    have : w'.sees s = false := by
      unfold Reader.sees; simp only [decide_eq_false_iff_not]; exact hw w' hwr
    simp only [this, Bool.false_eq_true, ↓reduceIte] at H
    exact H

theorem inRuns_one (a k s : Nat) : inRuns [(a, k)] s ↔ (a ≤ s ∧ s < a + k) := by
  unfold inRuns; simp

theorem fl_off (x : w64) (ps : Nat) (h : uint.nat x * ps < 2 ^ 62) :
    uint.Z (x * W64 (ps : Int)) = ((uint.nat x * ps : Nat) : Int) := by
  have hx : x = W64 ((uint.nat x : Nat) : Int) := by unfold uint.nat; word
  have e : x * W64 (ps : Int) = W64 ((uint.nat x * ps : Nat) : Int) := by
    conv => lhs; rw [hx]
    rw [← BitVec.ofInt_mul]; push_cast; rfl
  rw [e]
  generalize uint.nat x * ps = n at h ⊢
  word

end lemmas

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]

set_option maxHeartbeats 800000 in
theorem Tx.rollback.wp_wproof (hTxid : Meta.Txid.spec (GF := GF) (hG := hG))
    (hSynced : DB.hasSyncedFreelist.spec (GF := GF) (hG := hG))
    (hMeta : DB.meta.spec (GF := GF) (hG := hG))
    (hFl : Meta.Freelist.spec (GF := GF) (hG := hG))
    (hPage : DB.page.spec (GF := GF) (hG := hG))
    (hclose : Tx.close.wspec (GF := GF) (hG := hG)) :
    Tx.rollback.wspec (GF := GF) (hG := hG) := by
  intro I γ W txl txid σ T hRb hRl hFC hPC hEW Hwr Htdb Hroot Hmtx Hrbok
  wp_start as ⟨Hdbw, Hg, Hv⟩
  unfold dbWR
  icases Hdbw with ⟨Hdb, %Hdw⟩
  have Hdw' := Hdw
  obtain ⟨hAl, hrw, hdata, hps, hfli, w, hw, hwp, hwq, hwh, htx, htb⟩ := Hdw'
  subst htx
  icases ownDB_logger I W.dbl γ σ $$ Hdb with ⟨%lg, %dl, #Hlg, #Hdl, #Hdlok, %Hl, Hdb⟩
  have Hdbl := Hl.2
  icases ownDB_rollback I W.dbl γ σ w hw $$ Hdb with ⟨%fls, %hcan, Hfl, Hback⟩
  unfold ownWriteTxG
  icases Hg with ⟨Hrest, Hmv, Hpm, Hbufs, Hbs⟩
  unfold TxW_rest_root
  icases Hrest with ⟨Hwritable, Hmanaged, Htdbf, Hmetaf, Hpagesf, Hstatsf, Hch, HWF, %Htxlnn⟩
  unfold wView
  icases Hv with ⟨Hvd, #Hvps, #Hvlg, Hvfl, #Hvdl, %Hvlg', Hvpg⟩
  ihave #Hflpkg : (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist) $$ []
  · iPkgInit
  ihave #Hcpkg : (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common) $$ []
  · iPkgInit
  wp_auto
  rw [Htdb, decide_eq_false Hdbl]
  try wp_auto
  rw [Hwr]
  try wp_auto
  wp_apply hTxid T.t.meta' T.mv (DFrac.own 1) $$ [Hmv] as Hmv
  · iframe
  try wp_auto
  try rw [hfli]
  try simp only [FLImpl.iface, interface.mkOk]
  try wp_auto
  rw [Hmtx]
  wp_apply hRb fls σ.fl _ hcan $$ [Hfl] as Hfl
  · iframe
  ihave Hdb := Hback $$ Hfl
  -- the database rolled back, opened
  isimp only [ownDB] at Hdb
  iNamed Hdb
  isimp only [dbPlain] at Hplain
  iNamed Hplain
  have Hok' := Hok
  obtain ⟨Hps80, Hps32, Hns2, ⟨Hsz48, Hbs62⟩, Hdc, -, -, Hvalid, -⟩ := Hok'
  obtain ⟨Hdd, Hdps, -, Hdm0, Hdm1, -, -, Hdfl, -⟩ := id Hdv
  have Hdnn : W.data ≠ null := by rw [← hdata]; exact loc_ne_null_of_car _ Hdc
  simp only at Hdc Hdd Hdps Hdm0 Hdm1 Hok Hbs62 Hsz48 Hps80 Hps32
  try wp_auto
  rw [decide_eq_false Hdnn]
  try wp_auto
  -- the metas: `hasSyncedFreelist`, `meta()`
  have hc16 : (σ.data +ₗ 16).locCar ≠ 0 := by simpa [Loc.add] using Hdc
  have hc1 : (σ.data +ₗ ((σ.ps + 16 : Nat) : Int)).locCar ≠ 0 := by simpa [Loc.add] using Hdc
  icases slots_metas _ v0 v1 Hok $$ Hslots with ⟨HM0, HM1, Hmback⟩
  rw [Hdm0, Hdm1]
  wp_apply hSynced W.dbl _ _ (DFrac.own 1) _ _ v0 v1 hc16 hc1 Hvalid $$ [meta0 meta1 HM0 HM1]
    as ⟨meta0, meta1, HM0, HM1⟩
  · iframe
  obtain ⟨Hnofl, Hrb⟩ := Hrbok v0 v1 Hok
  rw [decide_eq_false Hnofl]
  try wp_auto
  wp_apply hMeta W.dbl _ _ (DFrac.own 1) _ _ v0 v1 hc16 hc1 Hvalid $$ [meta0 meta1 HM0 HM1]
    as ⟨-, meta0, meta1, HM0, HM1⟩
  · iframe
  icases pick_acc (GF := GF) (metaPick v0 v1) _ _ v0 v1 _ $$ [HM0 HM1] with ⟨HMc, HMback⟩
  · iframe
  wp_apply hFl _ _ _ $$ [HMc] as HMc
  · iframe
  ihave HMs := HMback $$ HMc
  icases HMs with ⟨HM0, HM1⟩
  ihave Hslots := Hmback $$ HM0 HM1
  try wp_auto
  -- the freelist page
  have Hn1 : ({ σ with fl := σ.fl.rollback (w.txid + W64 1) } : DBState).nslots = σ.nslots := rfl
  simp only [Hn1] at Hrb
  obtain ⟨Hfls, Hflag, Hfit, Hovc, Hnd, H2, Hlenp, Hne, Hfin⟩ := Hrb
  generalize Hcm : (if metaPick v0 v1 then v1 else v0) = cm at Hfls Hflag Hfit Hovc Hnd H2 Hlenp Hne Hfin ⊢
  generalize Hfid : uint.nat cm.freelist' = fid at Hfls Hflag Hfit Hovc Hnd H2 Hlenp Hne Hfin
  have Hsp := Hfls 0 (by unfold pageSpan; omega)
  have HNb := nslots_mul_le σ
  have HNsz : σ.nslots * σ.ps ≤ σ.sz := by
    unfold DBState.nslots; have := Nat.div_mul_le_self (min σ.sz σ.bs.length) σ.ps; omega
  have Hfidps : fid * σ.ps + σ.ps ≤ σ.nslots * σ.ps := by
    have := Nat.mul_le_mul_right σ.ps (show fid + 1 ≤ σ.nslots by have := Hsp.1; omega); rw [Nat.add_mul] at this; omega
  wp_apply hPage W.dbl σ.data (W64 (σ.ps : Int)) (DFrac.own σ.frem) DFrac.discard cm.freelist' Hdc
    (by rw [fl_off _ _ (by rw [Hfid]; omega)]; rw [Hfid]; omega) $$ [Hdata] as ⟨Hdata, -⟩
  · iframe; iframe #
  rw [fl_off _ _ (by rw [Hfid]; omega), Hfid]
  try wp_auto
  rw [Hdfl]
  try simp only [FLImpl.iface, interface.mkOk]
  try wp_auto
  -- the freelist page's cells, lent out of the database's slots
  have Hrem1 : ∀ s < σ.nslots, (fid ≤ s ∧ s < fid + pageSpan σ.bs σ.ps fid) → σ.rem s = halfQ := by
    intro s hs hin
    have := (Hfls (s - fid) (by omega)).2
    rw [show fid + (s - fid) = s by omega] at this
    exact rem_unseen _ v0 v1 Hok s hs this
  have Hspan := (Hfls (pageSpan σ.bs σ.ps fid - 1) (by unfold pageSpan; omega)).1
  rw [Hn1]
  icases (slots_out (GF := GF) σ.data σ.bs σ.ps σ.rem
    (fun s => fid ≤ s ∧ s < fid + pageSpan σ.bs σ.ps fid) σ.nslots Hrem1).1 $$ Hslots with ⟨Hout, Hcf⟩
  ihave Hcf := (cellsIf_ext (GF := GF) σ.data σ.bs σ.ps halfQ _ (inRuns [(fid, pageSpan σ.bs σ.ps fid)])
    σ.nslots (fun s _ => (inRuns_one _ _ s).symm)).1 $$ Hcf
  ihave Hcf := (cellsIf_runs (GF := GF) σ.data σ.bs σ.ps halfQ σ.nslots HNb
    [(fid, pageSpan σ.bs σ.ps fid)] (by intro r hr; simp at hr; subst hr; simp; omega)
    (List.pairwise_singleton _ _)).1 $$ Hcf
  icases BigSepL.bigSepL_singleton.1 $$ Hcf with Hpg
  ihave Hpg : bytesPointsto (σ.data +ₗ ((fid * σ.ps : Nat) : Int)) (DFrac.own halfQ)
      (pageAt σ.bs σ.ps fid) $$ [Hpg]
  · unfold pageAt runBytes; simp only; iexact Hpg
  have Hpgl : (pageAt σ.bs σ.ps fid).length < 2 ^ 62 := by
    unfold pageAt; simp only [List.length_take, List.length_drop]; omega
  have Hpc : (σ.data +ₗ ((fid * σ.ps : Nat) : Int)).locCar ≠ 0 := by simpa [Loc.add] using Hdc
  icases (flpage_bytes (GF := GF) _ (DFrac.own halfQ) (pageAt σ.bs σ.ps fid) Hpc Hfit Hpgl).1 $$ Hpg
    with ⟨Hh, Hcnt, Hids, Hpr⟩
  wp_apply hRl fls _ _ (pageOf (pageAt σ.bs σ.ps fid)) (DFrac.own halfQ) _ _ (DFrac.own halfQ) Hpc
    (by show W16 ((pageFlags (pageAt σ.bs σ.ps fid) : Nat) : Int) = W16 16; rw [Hflag]; rfl)
    Hovc Hnd H2 Hlenp Hne $$ [Hfl Hh Hcnt Hids] as %free' ⟨%Hfree, Hfl, Hh, Hcnt, Hids⟩
  · iframe
  -- the page's cells back into the slots
  ihave Hpg := (flpage_bytes (GF := GF) _ (DFrac.own halfQ) (pageAt σ.bs σ.ps fid) Hpc Hfit Hpgl).2
    $$ [Hh Hcnt Hids Hpr]
  · iframe
  ihave Hcf : ([∗list] r ∈ [(fid, pageSpan σ.bs σ.ps fid)],
      bytesPointsto (GF := GF) (σ.data +ₗ ((r.1 * σ.ps : Nat) : Int)) (DFrac.own halfQ)
        (runBytes σ.bs σ.ps r)) $$ [Hpg]
  · iapply BigSepL.bigSepL_singleton.2
    unfold pageAt runBytes; simp only; iexact Hpg
  ihave Hcf := (cellsIf_runs (GF := GF) σ.data σ.bs σ.ps halfQ σ.nslots HNb
    [(fid, pageSpan σ.bs σ.ps fid)] (by intro r hr; simp at hr; subst hr; simp; omega)
    (List.pairwise_singleton _ _)).2 $$ Hcf
  ihave Hcf := (cellsIf_ext (GF := GF) σ.data σ.bs σ.ps halfQ _ (inRuns [(fid, pageSpan σ.bs σ.ps fid)])
    σ.nslots (fun s _ => (inRuns_one _ _ s).symm)).2 $$ Hcf
  ihave Hslots := (slots_out (GF := GF) σ.data σ.bs σ.ps σ.rem
    (fun s => fid ≤ s ∧ s < fid + pageSpan σ.bs σ.ps fid) σ.nslots Hrem1).2 $$ [Hout Hcf]
  · iframe
  -- the database with the free ids reloaded
  have Hok2 := Hfin free' Hfree.1 Hfree.2
  ihave Hplain : dbPlain W.dbl (DFrac.own 1) dv $$ [StrictMode NoSync NoFreelistSync FreelistType
    NoGrowSync PreLoadFreelist MmapFlags MaxBatchSize MaxBatchDelay AllocSize MaxSize path openFile
    file dataref datasz meta0 meta1 opened rwtx stats batch ops readOnly]
  · simp only [dbPlain]; rw [Hdm0, Hdm1]; iframe
  ihave Hdb : ownDB I W.dbl γ { σ with fl := { σ.fl.rollback (w.txid + W64 1) with free := free' } }
    $$ [Hplain Hflf Hdata Hfp Hbytes Hmap Hslots Htail Hfl Hrwl Hmmaph Htoks Hstath Hstats Hrauth]
  · simp only [ownDB]
    iexists dv, fls, v0, v1, dl
    isplitr
    · ipureintro; exact Hdv
    isplitr
    · ipureintro; exact Hok2
    isplitr
    · ipureintro; exact Hdr
    isplitr
    · ipureintro; exact Hops
    have Hn2 : ({ σ with fl := { σ.fl.rollback (w.txid + W64 1) with free := free' } } : DBState).nslots =
      σ.nslots := rfl
    rw [Hn2, Hdfl]
    iframe
    iframe #
    try (ipureintro; exact Hlog)
  ihave Hg : ownWriteTxG W txl T $$ [Hwritable Hmanaged Htdbf Hmetaf Hpagesf Hstatsf Hch HWF Hmv Hpm Hbufs Hbs]
  · unfold ownWriteTxG TxW_rest_root; rw [Hwr, Htdb]; iframe; ipureintro; exact Htxlnn
  ihave Hv : wView W $$ [Hvd Hvfl Hvpg]
  · unfold wView; rw [hfli]; iframe; iframe #; ipureintro; exact Hvlg'
  ihave Hdbw : dbWR I γ W txl (w.txid + W64 1)
      { σ with fl := { σ.fl.rollback (w.txid + W64 1) with free := free' } } $$ [Hdb]
  · unfold dbWR; iframe; ipureintro; exact Hdw
  wp_apply hclose I γ W txl _ { σ with fl := { σ.fl.rollback (w.txid + W64 1) with free := free' } } T w
    hFC hPC hEW hw (fun v0 v1 h => dbOK_removeWriter _ v0 v1 h w hw (rb_pending_none _ _))
    Hwr Htdb Hroot $$ [Hdbw Hg Hv] as ⟨%t, Hdb, Htx, %Ht⟩
  · iframe
  try wp_auto
  iapply HΦ
  iexists w, free', t
  iframe
  ipureintro; exact ⟨⟨hw, Hfree.1⟩, Ht⟩

end proof

end bbolt
end EtcdGrove
end Perennial
