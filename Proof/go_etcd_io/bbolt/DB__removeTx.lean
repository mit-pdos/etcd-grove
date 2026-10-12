module
public import Spec.go_etcd_io.bbolt.DB__removeTx
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Txid
public import Spec.go_etcd_io.bbolt.TxStats__add
public import Proof.go_etcd_io.bbolt.StructSplit

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

theorem DB.removeTx.wp_proof (hTxid : Meta.Txid.spec (GF := GF) (hG := hG))
    (hadd : TxStats.add.spec (GF := GF) (hG := hG)) :
    DB.removeTx.spec (GF := GF) (hG := hG) := by
  intro I dbl γ σ txl k r m hRem
  wp_start as ⟨Hdb, Htx⟩
  simp only [ownDB]
  iNamed Hdb
  simp only [ownReadTx]
  iNamed Htx
  obtain ⟨Hdata', Hps', Hdsz, Hm0, Hm1, Hopen, Hfile', Hfl', Hrw, Hdbl⟩ := Hdv
  obtain ⟨Htdb, Htw, Htp, _, _, _, _, _, _, Hmtx, _⟩ := Ht
  ihave %Hk := ghost_map_lookup $$ Hrauth Hkey
  imod ghost_map_delete $$ Hrauth Hkey with Hrauth
  -- the reader's token
  icases (BigSepM.bigSepM_delete (M := GMap Nat)
    (Φ := fun (_ : Nat) (_ : Reader) => mmapTok (GF := GF) γ.mmap sync.rfrac)
    (show Std.get? σ.readers k = some r from Hk)).1 $$ Htoks with ⟨Htok, Htoks⟩
  isimp only [dbPlain] at Hplain
  iNamed Hplain
  wp_auto
  wp_apply sync.RWMutex.wp_RUnlock _ _ $$ [$Hrl $Htok] as Hh
  wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hmetalock] as ⟨Hlocked, -⟩
  try wp_auto
  try simp only
  rw [Hfl']
  simp only [FLImpl.iface, interface.mkOk]
  try wp_auto
  wp_apply hTxid t.meta' mv (DFrac.own 1) $$ [Hmeta] as Hmeta
  · iframe
  wp_apply hRem fls σ.fl _ $$ [Hfl] as %ro ⟨%Hro, Hfl⟩
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
    try simp only
    icases (Stats_split_TxStats _ _ _).1 $$ Hsv with ⟨HsT, Hsr⟩
    icases (Tx_split_stats _ _ _).1 $$ Htx with ⟨Hts, Htr⟩
    wp_apply hadd _ _ _ _ (DFrac.own 1) $$ [HsT Hts] as %v' ⟨%Hv', HsT, Hts⟩
    · iframe
    ihave Htx := (Tx_split_stats _ _ _).2 $$ [Hts Htr]
    · iframe
    ihave Hsv := (Stats_split_TxStats _ _ { sv with OpenTxN' := sv.OpenTxN' - W64 1, TxStats' := v' }).2
      $$ [HsT Hsr]
    · iframe; simp only [Stats_rest_TxStats]; iframe
    try wp_auto
    wp_apply sync.RWMutex.wp_Unlock _ _ $$ [$Hsl] as Hstath
    · iframe; simp only [statsInv]; inext; itrivial
    try wp_auto
    ihave Hstats : (⌜dv.stats' = null⌝ ∨ ∃ (sv : Stats), dv.stats' ↦ sv : IProp GF) $$ [Hsv]
    · iright; iexists _; iframe
  all_goals
    icases end_give σ v0 v1 Hok k r Hk ro dbl $$ [Hslots Hdata Hpages Hrdata]
      with ⟨Hslots, Hdata⟩
    · iframe
    iapply HΦ
    iexists ro, t
    isplitr
    · ipureintro; exact Hk
    isplitr [Htx]
    · iexists dv
      iexists fls
      iexists v0
      iexists v1
      iexists dl
      have Hsz' := GMap.map_size_delete_Some σ.readers k r Hk
      have Hpos : 0 < σ.readers.size := by
        have := GMap.map_size_ne_0_lookup_2 σ.readers Hk; omega
      have Hrep : Int.toNat sync.rwmutex.actualMaxReaders - (σ.readers.size - 1) =
          (Int.toNat sync.rwmutex.actualMaxReaders - σ.readers.size) + 1 := by
        have hok' := Hok
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hrs⟩ := hok'
        omega
      simp only [DBState.removeReader.proj_data, DBState.removeReader.proj_ps,
        DBState.removeReader.proj_sz, DBState.removeReader.proj_file, DBState.removeReader.proj_fd,
        DBState.removeReader.proj_bs, DBState.removeReader.proj_readers, Hsz', Hrep,
        List.replicate_succ]
      isplitr
      · ipureintro; exact ⟨Hdata', Hps', Hdsz, Hm0, Hm1, Hopen, Hfile', Hfl', Hrw, Hdbl⟩
      isplitr
      · ipureintro; exact dbOK_removeReader σ v0 v1 Hok k r Hk ro (Hmtx ▸ Hro)
      isplitr
      · ipureintro; exact Hdr
      isplitr
      · ipureintro; exact Hops
      ihave Hplain : dbPlain dbl (DFrac.own 1) dv $$ [StrictMode NoSync NoFreelistSync FreelistType NoGrowSync PreLoadFreelist MmapFlags MaxBatchSize MaxBatchDelay AllocSize MaxSize path openFile file dataref datasz meta0 meta1 opened rwtx stats batch ops readOnly]
      · simp only [dbPlain]
        rw [Hopen]
        iframe
      simp only [DBState.removeReader.proj_rwtx]
      rw [Hfl']
      simp only [FLImpl.iface, interface.mkOk]
      ihave Hmmaph := (BigSepL.bigSepL_cons (Φ := fun (_ : Nat) (_ : Unit) =>
          sync.ownRWMutex (structFieldRef DB go!"mmaplock" dbl) (mmapTok (GF := GF) γ.mmap))
          (x := ()) (xs := List.replicate (Int.toNat sync.rwmutex.actualMaxReaders - σ.readers.size) ())).2
        $$ [Hh Hmmaph]
      · iframe
      have Hns : (σ.removeReader k r ro).nslots = σ.nslots := rfl
      rw [Hns]
      iframe
      iframe #
      try (ipureintro; exact Hlog)
    · iframe
      ipureintro; exact ⟨Htdb, Htw⟩

end proof

end bbolt
end EtcdGrove
end Perennial
