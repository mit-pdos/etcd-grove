module
public import Spec.go_etcd_io.bbolt.DB__beginTx
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Txid

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

theorem DB.beginTx.wp_proof (hinit : Tx.init.spec (GF := GF) (hG := hG))
    (hTxid : Meta.Txid.spec (GF := GF) (hG := hG)) :
    DB.beginTx.spec (GF := GF) (hG := hG) := by
  intro I dbl γ σ hAdd hsize
  wp_start as Hdb
  simp only [ownDB]
  iNamed Hdb
  have hok := Hok
  -- one of `mmaplock`'s read handles
  have Hrep : Int.toNat sync.rwmutex.actualMaxReaders - σ.readers.size =
      (Int.toNat sync.rwmutex.actualMaxReaders - (σ.readers.size + 1)) + 1 := by omega
  rw [Hrep, List.replicate_succ]
  icases BigSepL.bigSepL_cons.1 $$ Hmmaph with ⟨Hh, Hmmaph⟩
  wp_auto
  wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hmetalock] as ⟨Hlocked, -⟩
  wp_apply sync.RWMutex.wp_RLock _ _ $$ [$Hh] as ⟨Hrl, Htok⟩
  -- the new reader's key
  have Hk := freshKey_none σ.readers
  imod ghost_map_insert (freshKey σ.readers) (newReader σ v0 v1 (beginQ σ)) Hk $$ Hrauth
    with ⟨Hrauth, Hkey⟩
  obtain ⟨Hdata', Hps', Hdsz, Hm0, Hm1, Hopen, Hfile', Hfl', Hrw, Hdbl⟩ := Hdv
  isimp only [dbPlain] at Hplain
  iNamed Hplain
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
  wp_apply hinit «$r0_ptr» (zero_val Tx) dbl dv.meta0' dv.meta1' (DFrac.own 1) (DFrac.own halfQ)
    (DFrac.own halfQ) v0 v1 hc0 hc1 hval $$ [«$r0» meta0 meta1 HM0 HM1]
    as %ml %ibl %pm %bm %nm ⟨%Hvm, Ht, Hml, Hibl, Hmaps, meta0, meta1, HM0, HM1⟩
  · iframe
  icases Hmaps with %Hmaps
  obtain ⟨rfl, rfl, rfl⟩ := Hmaps
  try wp_auto
  try simp only
  rw [Hfl']
  simp only [FLImpl.iface, interface.mkOk]
  try wp_auto
  try simp only [txInitOf.proj_meta']
  wp_apply hTxid ml _ (DFrac.own 1) $$ [Hml] as Hml
  · iframe
  try wp_auto
  wp_apply hAdd fls σ.fl _ $$ [Hfl] as Hfl
  · iframe
  try wp_auto
  wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmetalock $Hlocked]
  · iframe; inext; itrivial
  try wp_auto
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
    wp_apply sync.RWMutex.wp_Unlock _ _ $$ [$Hsl] as Hstath
    · iframe; simp only [statsInv]; inext; itrivial
    try wp_auto
    ihave Hstats : (⌜dv.stats' = null⌝ ∨ ∃ (sv : Stats), dv.stats' ↦ sv : IProp GF) $$ [Hsv]
    · iright; iexists _; iframe
  all_goals
    ihave Hslots := Hmback $$ HM0 HM1
    icases begin_carve σ v0 v1 Hok (freshKey σ.readers) dbl $$ [Hslots Hdata Hps]
      with ⟨Hslots, Hdata, Hps, Hpages, Hdq, Hpsq⟩
    · iframe
    iapply HΦ
    iexists (freshKey σ.readers), (newReader σ v0 v1 (beginQ σ))
    isplitr
    · ipureintro; exact Hk
    isplitr [Ht Hml Hibl Hdq Hpsq Hpages Hrl Hkey]
    · iexists dv
      iexists fls
      iexists v0
      iexists v1
      iexists dl
      have Hsz' := GMap.map_size_insert_None σ.readers (freshKey σ.readers)
        (newReader σ v0 v1 (beginQ σ)) Hk
      simp only [DBState.addReader.proj_data, DBState.addReader.proj_ps, DBState.addReader.proj_sz,
        DBState.addReader.proj_file, DBState.addReader.proj_fd, DBState.addReader.proj_bs,
        DBState.addReader.proj_readers, nslots_addReader, Hsz']
      isplitr
      · ipureintro; exact ⟨Hdata', Hps', Hdsz, Hm0, Hm1, Hopen, Hfile', Hfl', Hrw, Hdbl⟩
      isplitr
      · ipureintro; exact dbOK_addReader σ v0 v1 Hok hsize
      ihave Hplain : dbPlain dbl (DFrac.own 1) dv $$ [StrictMode NoSync NoFreelistSync FreelistType NoGrowSync PreLoadFreelist MmapFlags MaxBatchSize MaxBatchDelay AllocSize MaxSize Mlock logger path openFile file dataref datasz meta0 meta1 opened rwtx stats freelist batch ops readOnly]
      · simp only [dbPlain]
        rw [Hopen, Hfl']
        simp only [FLImpl.iface, interface.mkOk]
        iframe
      iframe
      ihave Htoks := (show (mmapTok (GF := GF) γ.mmap sync.rfrac ∗
          [∗map] _r ∈ σ.readers, mmapTok (GF := GF) γ.mmap sync.rfrac) ⊢
          [∗map] _r ∈ <[freshKey σ.readers := newReader σ v0 v1 (beginQ σ)]> σ.readers,
            mmapTok (GF := GF) γ.mmap sync.rfrac from
        (BigSepM.bigSepM_insert (M := GMap Nat)
          (Φ := fun (_ : Nat) (_ : Reader) => mmapTok (GF := GF) γ.mmap sync.rfrac)
          (x := newReader σ v0 v1 (beginQ σ))
          (show Std.get? σ.readers (freshKey σ.readers) = none from Hk)).2) $$ [Htok Htoks]
      · iframe
      iframe
      iframe #
      try (ipureintro; exact Hlog)
      done
    · simp only [ownReadTx]
      iexists (txInitOf (zero_val Tx) «$r0_ptr» dbl ml ibl map.nil map.nil map.nil)
      iexists (if metaPick v0 v1 then v1 else v0)
      simp only [txInitOf.proj_meta', txInitOf.proj_root', txMetaOf, Bool.false_eq_true, ↓reduceIte]
      iframe
      ipureintro
      simp [txInitOf, newBucketOf, newReader]
      exact ⟨rfl, rfl⟩

end proof

end bbolt
end EtcdGrove
end Perennial
