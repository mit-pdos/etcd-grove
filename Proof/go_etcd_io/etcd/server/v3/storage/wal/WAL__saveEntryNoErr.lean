/-
The proof of `Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__saveEntryNoErr.lean`:
`WAL__saveEntry.lean`'s proof over the record's encode with no error (`encoder.encode.specTailNoErr`), the
room covering the record's frame (`frame_walRecEnc_tight`); the error arm gone. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__saveEntryNoErr
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.encoder__encodeTailNoErr
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.SaveNext
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.StreamBound

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs WalEnc WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]
variable {Sio : IoSet} [FsStepSat (NoIoErr Sio)]

/-- See the file header. -/
theorem go_etcd_io.etcd.server.v3.storage.wal.WAL.saveEntry.wp_proofNoErr (P : WalPbIn GF)
    (Mr : WalMarshal)
    (wp_encode : go_etcd_io.etcd.server.v3.storage.wal.encoder.encode.specTailNoErr (Sio := Sio) (W := W) Mr)
    (wp_marshal : WalPbIn.MarshalEntLaw P Mr) (wp_getIndex : WalPbIn.GetIndexLaw P) :
    go_etcd_io.etcd.server.v3.storage.wal.WAL.saveEntry.specNoErr (Sio := Sio) (W := W) P Mr := by
  intro hS0 R jr r w dir h l e hrest hei hlen hlast hx hroom
  wp_start as ⟨#Harea, Hh, #Hel⟩
  iunfold walHandleIn at Hh
  icases Hh with ⟨%lg, %df, %sp, %en, %fp, %lt, %f, %mds, %locks, %lfs, %fd, %dfd, %name, %dnm, %j,
    %rc, Hlg, #Hzap, Hdir, Hdf, Hdff, Hmd, #Hmds, Hsp, #Hst, Hdec, Hrc, Hns, #Hmu, Henti, Hsnapi,
    He, %Hen, Henc, Htw, Hdh, Hlocks, Hls, Hcap, %Hlt, Hlks, #Hltf, Hfp, Hpipe, #Henv, #Hcrc, #Hwpk, Hopen, %Hpure⟩
  obtain ⟨hsplit, hfd, hoff, hsz, hidx, hidx2⟩ := Hpure
  try wp_auto
  wp_apply (wp_marshal l e) $$ [] as %d ⟨Hd, Hdc, %Hdn⟩
  · iexact Hel
  imod ownSlice_persist $$ Hd with #Hd
  unfold go_etcd_io.etcd.server.v3.storage.wal.EntryType
  try wp_auto
  imod (typedPointsto_dfractional _ _).dfractional_persist (DFrac.own 1) $$ «$v0» with #Ht
  have hguard := WalHS.next_guard Mr h hsplit hrest entryType (Mr.encEntry e) hx
  have hrs : recSize (recOf ⟨entryType, hash.crc32.crc32c (h.crc Mr) (Mr.encEntry e),
      Mr.encEntry e⟩) < 2 ^ 47 := by
    have h1 := recSize_tight entryType (hash.crc32.crc32c (h.crc Mr) (Mr.encEntry e))
      (Mr.encEntry e) (by decide) (by omega)
    omega
  have hfr := frame_walRecEnc_tight entryType (hash.crc32.crc32c (h.crc Mr) (Mr.encEntry e))
    (Mr.encEntry e) (by decide) (by omega)
  have hroom' : h.o0 + (h.out ++ h.pend ++ frame (walRecEnc ⟨entryType,
      hash.crc32.crc32c (h.crc Mr) (Mr.encEntry e), Mr.encEntry e⟩)).length ≤ maxBytes := by
    simp only [List.length_append]; omega
  wp_apply (wp_encode hS0 R jr r en f fd name dir h.γ h.ino h.H h.md h.cuts h.o0 h.sz h.out h.pend
      (h.crc Mr) «$r0_ptr» entryType (Mr.encEntry e) hrs hguard hoff hsz hroom') $$ [Henc Htw «$r0»]
      as %err ⟨%pend', Henc, -, %out', %sz', %Hok, Htw⟩
  · iframe Harea Henv Henc Htw
    iunfold encRecIn
    iexists _
    iframe «$r0»
    have hd : (recOf ⟨entryType, 0#32, Mr.encEntry e⟩).data = some (Mr.encEntry e) := by
      simp [recOf, entryType, crcType]
    simp only [hd, recBytes]
    have hst : entryType = W64 2 := rfl
    rw [hst]
    isplitl
    · iexact Ht
    isplitr
    · isplitr
      · ipureintro; exact Hdn
      · iexact Hd
    · ipureintro; trivial
  obtain ⟨Herr, hsp, hoff', hsz'⟩ := Hok
  subst Herr
  try wp_auto
  wp_apply (wp_getIndex l e) $$ Hel
  try wp_auto
  iapply HΦ
  isplitr
  · ipureintro; rfl
  iexists out', pend', sz'
  have hlen' : out'.length + pend'.length ≤ h.out.length + h.pend.length + ((Mr.encEntry e).length + 64) := by
    have := congrArg List.length hsp
    simp only [List.length_append] at this
    omega
  obtain ⟨hsplit', hcrc'⟩ := WalHS.split_next Mr h
    { h with rest := h.rest - 1, out := out', pend := pend', enti := e.Index', sz := sz' } hsplit hrest
    entryType (Mr.encEntry e) hx rfl rfl rfl rfl rfl hsp
  isplitl
  · iunfold walHandleIn
    iexists lg, df, sp, en, fp, lt, f, mds, locks, lfs, fd, dfd, name, dnm, j, rc
    rw [hcrc']
    simp only
    iframe Hlg Hzap Hdir Hdf Hdff Hmd Hmds Hsp Hst Hdec Hrc Hns Hmu Henti Hsnapi He Henc Htw Hdh
      Hlocks Hls Hcap Hlks Hltf Hfp Hpipe Henv Hcrc Hwpk Hopen
    ipureintro
    refine ⟨Hen, Hlt, hsplit', hfd, hoff', hsz', ⟨fun h0 => hlast (by omega), hidx.2⟩, ?_⟩
    have := hidx2
    omega
  · ipureintro; exact hlen'

end proof

end EtcdGrove
end Perennial
