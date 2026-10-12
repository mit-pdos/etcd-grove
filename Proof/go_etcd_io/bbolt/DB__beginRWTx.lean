module
public import Spec.go_etcd_io.bbolt.DB__beginRWTx

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

theorem DB.beginRWTx.wp_proof (hinit : Tx.init.spec (GF := GF) (hG := hG)) :
    DB.beginRWTx.spec (GF := GF) (hG := hG) := by
  intro I dbl γ σ hRel hw hrng
  wp_start as Hdb
  simp only [ownDB]
  iNamed Hdb
  have hok := Hok
  obtain ⟨Hdata', Hps', Hdsz, Hm0, Hm1, Hopen, Hfile', Hfl', Hrw, Hdbl⟩ := Hdv
  isimp only [dbPlain] at Hplain
  iNamed Hplain
  ihave #Hei : (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.errors) $$ []
  · iPkgInit
  wp_apply wp_with_defer as %defer Hdefer
  try wp_auto
  cases hro : dv.readOnly'
  rotate_left
  · -- read-only: an error, the database as it was
    try wp_auto
    icases bboltError_access errors.ErrDatabaseReadOnly (by simp [bboltErrorNames]) $$ Hei
      with ⟨%e, #He, %Hne⟩
    try wp_auto
    iapply HΦ
    ileft
    isplitr
    · ipureintro; obtain ⟨t, p, rfl⟩ := Hne; exact fun h => by cases h
    ihave Hplain : dbPlain dbl (DFrac.own 1) dv $$ [StrictMode NoSync NoFreelistSync FreelistType NoGrowSync PreLoadFreelist MmapFlags MaxBatchSize MaxBatchDelay AllocSize MaxSize Mlock path openFile file dataref datasz meta0 meta1 opened rwtx stats batch ops readOnly]
    · simp only [dbPlain]; rw [hro]; iframe
    try simp only [ownDB]
    iexists dv, fls, v0, v1, dl
    isplitr
    · ipureintro; exact ⟨Hdata', Hps', Hdsz, Hm0, Hm1, Hopen, Hfile', Hfl', Hrw, Hdbl⟩
    isplitr
    · ipureintro; exact Hok
    iframe
    iframe #
    try (ipureintro; exact Hlog)
  try wp_auto
  -- no writer open: `rwlock` is free
  have hwr := hok.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hrw0 : σ.rwtx = null := hwr.1.1 hw
  rw [hrw0, decide_eq_true rfl] at *
  simp only [↓reduceIte]
  wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hrwlock] as ⟨Hrwlocked, -⟩
  try wp_auto
  wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hmetalock] as ⟨Hmlocked, -⟩
  try wp_auto
  rw [Hopen]
  try wp_auto
  obtain ⟨hps, hps2, hn, hsz, hdc, hm0, hm1, hval, _⟩ := hok
  rw [decide_eq_false (loc_ne_null_of_car _ hdc)]
  try wp_auto
  icases slots_metas σ v0 v1 Hok $$ Hslots with ⟨HM0, HM1, Hmback⟩
  rw [← Hm0, ← Hm1]
  have hc0 : dv.meta0'.locCar ≠ 0 := by rw [Hm0]; simpa [Loc.add] using hdc
  have hc1 : dv.meta1'.locCar ≠ 0 := by rw [Hm1]; simpa [Loc.add] using hdc
  wp_apply hinit «$r0_ptr» _ dbl dv.meta0' dv.meta1' (DFrac.own 1) (DFrac.own halfQ)
    (DFrac.own halfQ) v0 v1 hc0 hc1 hval $$ [«$r0» meta0 meta1 HM0 HM1]
    as %ml %ibl %pm %bm %nm ⟨%Hvm, Ht, Hml, Hibl, Hmaps, meta0, meta1, HM0, HM1⟩
  · iframe
  try wp_auto
  try simp only
  -- the freelist's entries have their two lists of one length
  isimp only [ownFL] at Hfl
  icases Hfl with ⟨#Hhdl, Hsh, Hown⟩
  icases ownShared_wf _ _ _ $$ Hsh with ⟨Hsh, %Hwf⟩
  ihave Hfl : ownFL I fls σ.fl $$ [Hsh Hown]
  · simp only [ownFL]; iframe; iframe #
  rw [Hfl']
  simp only [FLImpl.iface, interface.mkOk]
  try wp_auto
  wp_apply hRel fls σ.fl $$ [Hfl] as %fl' ⟨%Heq, Hfl⟩
  · iframe
  try wp_auto
  wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmetalock $Hmlocked]
  · iframe; inext; itrivial
  try wp_auto
  -- the new state: the freelist released, the writer added
  have hl : ∀ t pd, σ.fl.pending !! t = some pd → pd.ids.length = pd.alloctx.length :=
    Hwf.2.2.2.2
  have hok1 := dbOK_release σ v0 v1 Hok hw hrng hl fl' Heq
  icases typedPointsto_not_null_dup _ _ _ $$ Ht with ⟨Ht, %Htxl⟩
  rw [flfQ_null]
  icases (pointsto_split _ _ halfQ halfQ).1 $$ Hflf with ⟨Hflf, Hflw⟩
  have hok2 := dbOK_addWriter { σ with fl := fl' } v0 v1 hok1 hw «$r0_ptr» Htxl
  ihave Hslots := Hmback $$ HM0 HM1
  icases begin_carve { σ with fl := fl' } v0 v1 hok1 0 dbl $$ [Hslots Hdata Hps]
    with ⟨Hslots, Hdata, Hps, Hpages, Hdq, Hpsq⟩
  · simp only; iframe
  iapply HΦ
  iright
  isplitr
  · ipureintro; rfl
  iexists fl', (newReader { σ with fl := fl' } v0 v1 (beginQ { σ with fl := fl' })), v0, v1
  isplitr
  · ipureintro; exact Heq
  isplitr [Ht Hml Hibl Hmaps Hdq Hpsq Hpages Hflw]
  · iexists { dv with rwtx' := «$r0_ptr» }, fls, v0, v1, dl
    isplitr
    · ipureintro
      exact ⟨Hdata', Hps', Hdsz, Hm0, Hm1, Hopen, Hfile', Hfl', rfl, Hdbl⟩
    isplitr
    · ipureintro; exact hok2
    ihave Hplain : dbPlain dbl (DFrac.own 1) { dv with rwtx' := «$r0_ptr» } $$ [StrictMode NoSync NoFreelistSync FreelistType NoGrowSync PreLoadFreelist MmapFlags MaxBatchSize MaxBatchDelay AllocSize MaxSize Mlock path openFile file dataref datasz meta0 meta1 opened rwtx stats batch ops readOnly]
    · simp only [dbPlain]
      try simp only
      rw [Hopen, hro]
      iframe
    simp only [DBState.addWriter.proj_rwtx, decide_eq_false Htxl, Bool.false_eq_true, ↓reduceIte]
    simp only [DBState.addWriter.proj_data, DBState.addWriter.proj_ps, DBState.addWriter.proj_sz,
      DBState.addWriter.proj_file, DBState.addWriter.proj_fd, DBState.addWriter.proj_bs,
      DBState.addWriter.proj_readers, DBState.addWriter.proj_fl]
    simp only [flfQ, Htxl, ↓reduceIte]
    rw [Hfl']
    simp only [FLImpl.iface, interface.mkOk]
    iframe
    iframe #
    try (ipureintro; exact Hlog)
  · isplitr [Hflw]
    rotate_left
    · iframe
    simp only [wtxInit]
    iexists ml, ibl, pm, bm, nm
    have hq : ∀ (σ' : DBState) (q : Qp), (newReader σ' v0 v1 q).q = q := fun _ _ => rfl
    simp only [hq, show (zero_val Tx).managed' = false from rfl, show (zero_val Tx).db' = null from rfl,
      show (zero_val Tx).meta' = null from rfl, show (zero_val Tx).root' = zeroValDef from rfl,
      show (zero_val Tx).pages' = null from rfl, show (zero_val Tx).stats' = zeroValDef from rfl,
      show (zero_val Tx).commitHandlers' = slice.nil from rfl, show (zero_val Tx).WriteFlag' = 0 from rfl]
    simp only [↓reduceIte] at *
    try simp only [FLImpl.iface, interface.mkOk]
    iframe

end proof

end bbolt
end EtcdGrove
end Perennial
