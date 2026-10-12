module
public import Spec.go_etcd_io.bbolt.Tx__close_w
public import Spec.go_etcd_io.bbolt.TxStats__add
public import Proof.go_etcd_io.bbolt.DBAcc

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]

theorem Stats_join (l : Loc) (dq : DFrac) (v : Stats) (x : TxStats) :
    structFieldRef Stats go!"TxStats" l ↦{dq} x ∗ Stats_rest_TxStats (GF := GF) l dq v ⊢
      l ↦{dq} ({ v with TxStats' := x } : Stats) :=
  (Stats_split_TxStats l dq { v with TxStats' := x }).2

theorem Tx_join (txl : Loc) (rv : Bucket) (v : Tx) :
    structFieldRef Tx go!"root" txl ↦ rv ∗ TxW_rest_root (GF := GF) txl (DFrac.own 1) v ⊢
      txl ↦ ({ v with root' := rv } : Tx) :=
  (TxW_split_root txl (DFrac.own 1) { v with root' := rv }).2

theorem Tx.close.wp_wproof (hadd : TxStats.add.spec (GF := GF) (hG := hG)) :
    Tx.close.wspec (GF := GF) (hG := hG) := by
  intro I γ W txl txid σ T w hFC hPC hEW hw hok' Hwr Htdb Hroot
  wp_start as ⟨Hdbw, Hg, Hv⟩
  unfold dbWR
  icases Hdbw with ⟨Hdb, %Hdw⟩
  obtain ⟨hAl, hrw, hdata, hps, hfli, w', hw', hwp, hwq, hwh, htx, htb⟩ := Hdw
  obtain rfl := Option.some.inj (hw'.symm.trans hw)
  simp only [ownDB]
  iNamed Hdb
  obtain ⟨Hdata', Hps', Hdsz, Hm0, Hm1, Hopen, Hfile', Hfl', Hrw, Hdbl⟩ := Hdv
  isimp only [dbPlain] at Hplain
  iNamed Hplain
  unfold ownWriteTxG
  icases Hg with ⟨Hrest, Hmv, Hpm, Hbufs, Hbs⟩
  unfold TxW_rest_root
  icases Hrest with ⟨Hwritable, Hmanaged, Htdbf, Hmetaf, Hpagesf, Hstatsf, Hch, HWF, %Htxlnn⟩
  obtain ⟨B, hB⟩ := Option.isSome_iff_exists.1 Hroot
  icases (BigSepM.bigSepM_delete (M := GMap Loc)
    (Φ := fun bl B => bktOwn (GF := GF) W bl B) hB).1 $$ Hbs with ⟨HB, -⟩
  unfold bktOwn
  icases HB with ⟨Hbv, -, -, -, -, -⟩
  unfold wView
  icases Hv with ⟨Hvd, #Hvps, #Hvlg, Hvfl, #Hvdl, %Hvlg', Hvpg⟩
  have Hrwnn : σ.rwtx ≠ null := by
    intro e; have := (Hok.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).2 e; rw [hw] at this; cases this
  ihave #Hflpkg : (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist) $$ []
  · iPkgInit
  wp_auto
  rw [Htdb, decide_eq_false Hdbl]
  try wp_auto
  rw [Hwr]
  try wp_auto
  try rw [Hfl']
  try rw [hfli]
  try simp only [FLImpl.iface, interface.mkOk]
  try wp_auto
  wp_apply hFC fls σ.fl $$ [Hfl] as Hfl
  · iframe
  try wp_auto
  try rw [Hfl']
  try rw [hfli]
  try simp only [FLImpl.iface, interface.mkOk]
  try wp_auto
  wp_apply hPC fls σ.fl $$ [Hfl] as Hfl
  · iframe
  try wp_auto
  try rw [Hfl']
  try rw [hfli]
  try simp only [FLImpl.iface, interface.mkOk]
  try wp_auto
  wp_apply hEW fls σ.fl $$ [Hfl] as Hfl
  · iframe
  try wp_auto
  -- the write lock released (held while the writer is open)
  simp only [decide_eq_false Hrwnn, Bool.false_eq_true, ↓reduceIte]
  wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hrwlock $Hrwl]
  · iframe; inext; itrivial
  try wp_auto
  -- the statistics merged
  icases Hstats with (%Hsn | ⟨%sv, Hsv⟩)
  focus
    rw [decide_eq_true Hsn]
    try wp_auto
    ihave Hstats : (⌜dv.stats' = null⌝ ∨ ∃ (sv : Stats), dv.stats' ↦ sv : IProp GF) $$ []
    · ileft; ipureintro; exact Hsn
  rotate_left
  focus
    icases typedPointsto_not_null_dup _ _ _ $$ Hsv with ⟨Hsv, %Hsnn⟩
    rw [decide_eq_false Hsnn]
    try wp_auto
    wp_apply sync.RWMutex.wp_Lock _ _ $$ [$Hstath] as ⟨Hsl, -⟩
    try wp_auto
    try simp only
    icases (Stats_split_TxStats _ _ _).1 $$ Hsv with ⟨HsT, Hsr⟩
    wp_apply hadd _ _ _ _ (DFrac.own 1) $$ [HsT Hstatsf] as %v' ⟨%Hv', HsT, Hstatsf⟩
    · iframe
    ihave Hsv := Stats_join _ _ _ _ $$ [HsT Hsr]
    · iframe
    try wp_auto
    wp_apply sync.RWMutex.wp_Unlock _ _ $$ [$Hsl] as Hstath
    · iframe; simp only [statsInv]; inext; itrivial
    try wp_auto
    ihave Hstats : (⌜dv.stats' = null⌝ ∨ ∃ (sv : Stats), dv.stats' ↦ sv : IProp GF) $$ [Hsv]
    · iright; iexists _; iframe
  all_goals
    try wp_auto
    -- the view's pages and part of `data` back into the database's slots
    rw [← hwq, ← hwp, ← hdata, ← hps] at *
    icases wend_give σ v0 v1 Hok w' hw W.dbl $$ [Hslots Hdata Hvpg Hvd] with ⟨Hslots, Hdata⟩
    · iframe
    -- the `freelist` field whole again
    simp only [flfQ, Hrwnn, ↓reduceIte]
    try rw [hfli]
    try rw [← Hfl']
    ihave Hflf := (pointsto_split _ _ halfQ halfQ).2 $$ [Hflf Hvfl]
    · iframe
    -- the transaction, its references cleared
    ihave Hrest : TxW_rest_root txl (DFrac.own 1)
        ({ T.t with db' := null, meta' := null, pages' := null, writable' := true } : Tx)
      $$ [Hwritable Hmanaged Htdbf Hmetaf Hpagesf Hstatsf Hch HWF]
    · unfold TxW_rest_root; iframe; ipureintro; exact Htxlnn
    ihave Htx := Tx_join _ _ _ $$ [Hbv Hrest]
    · iframe
    iapply HΦ
    iexists _
    isplitr [Htx]
    · try simp only [ownDB]
      iexists { dv with rwtx' := null }, fls, v0, v1, dl
      isplitr
      · ipureintro
        exact ⟨Hdata', Hps', Hdsz, Hm0, Hm1, Hopen, Hfile', Hfl', rfl, Hdbl⟩
      isplitr
      · ipureintro; exact hok' v0 v1 Hok
      isplitr
      · ipureintro; exact Hdr
      isplitr
      · ipureintro; exact Hops
      ihave Hplain : dbPlain W.dbl (DFrac.own 1) { dv with rwtx' := null } $$ [StrictMode NoSync NoFreelistSync FreelistType NoGrowSync PreLoadFreelist MmapFlags MaxBatchSize MaxBatchDelay AllocSize MaxSize path openFile file dataref datasz meta0 meta1 opened rwtx stats batch ops readOnly]
      · simp only [dbPlain]
        try simp only
        rw [Hopen]
        iframe
      simp only [DBState.removeWriter.proj_rwtx, DBState.removeWriter.proj_data,
        DBState.removeWriter.proj_ps, DBState.removeWriter.proj_sz, DBState.removeWriter.proj_file,
        DBState.removeWriter.proj_fd, DBState.removeWriter.proj_bs, DBState.removeWriter.proj_readers,
        DBState.removeWriter.proj_fl, DBState.removeWriter.proj_path, flfQ_null]
      simp only [_root_.decide_true, ↓reduceIte]
      try rw [show (halfQ + halfQ : Qp) = 1 by simp [halfQ, Qp.half_add_half]]
      have Hns : (σ.removeWriter w').nslots = σ.nslots := rfl
      rw [Hns, Hfl']
      try simp only [FLImpl.iface, interface.mkOk]
      iframe
      iframe #
      try (ipureintro; exact Hlog)
    · iframe; ipureintro; rfl

end proof

end bbolt
end EtcdGrove
end Perennial
