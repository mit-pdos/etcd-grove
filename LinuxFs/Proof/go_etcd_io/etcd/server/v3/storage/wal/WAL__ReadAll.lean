/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__ReadAll.lean` (W3/W5 of
`notes/wal-fsext-plan.md`; `sorry`: the plan's W3/W5 log says what is missing).
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__ReadAll
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.ReadAllCallees
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.decoder__Decode
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.decoder__LastCRC
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.decoder__UpdateCRC
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.decoder__LastOffset
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.walpb.Record__GetType
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.walpb.Record__GetCrc
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.walpb.Record__Validate
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.walpb.Snapshot__GetIndex
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__saveEntry
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__tail
public import LinuxFs.Spec.fmt.ErrorfErrs
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllLoop
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadState
public import Perennial.Proof.sync.Results
public import Perennial.Proof.bytes.Equal
import all LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadDefs

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
variable [os_sem : os.Assumptions] [bufio_sem : _root_.Perennial.bufio.Assumptions]

theorem go_etcd_io.etcd.server.v3.storage.wal.WAL.ReadAll.wp_proof [os.file.FieldAssumptions]
    [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]
    (P : WalPbIn GF) (Mr : WalMarshal) (U : WalUnmarshal) (hU : U.Ok Mr)
    (HsO : Loc → HardStateM → IProp GF) (hHs : WalHsOwn P U HsO)
    (wp_Decode : go_etcd_io.etcd.server.v3.storage.wal.decoder.Decode.spec (GF := GF) (hG := hG))
    (wp_LastCRC : go_etcd_io.etcd.server.v3.storage.wal.decoder.LastCRC.spec (GF := GF) (hG := hG))
    (wp_UpdateCRC : go_etcd_io.etcd.server.v3.storage.wal.decoder.UpdateCRC.spec (GF := GF) (hG := hG))
    (wp_LastOffset : go_etcd_io.etcd.server.v3.storage.wal.decoder.LastOffset.spec (GF := GF) (hG := hG))
    (wp_GetType : go_etcd_io.etcd.server.v3.storage.wal.walpb.Record.GetType.spec (GF := GF) (hG := hG))
    (wp_GetCrc : go_etcd_io.etcd.server.v3.storage.wal.walpb.Record.GetCrc.spec (GF := GF) (hG := hG))
    (wp_Validate : go_etcd_io.etcd.server.v3.storage.wal.walpb.Record.Validate.spec (GF := GF) (hG := hG))
    (wp_SnapIndex : go_etcd_io.etcd.server.v3.storage.wal.walpb.Snapshot.GetIndex.spec (GF := GF) (hG := hG))
    (wp_SnapTerm : go_etcd_io.etcd.server.v3.storage.wal.walpb.Snapshot.GetTerm.spec (GF := GF) (hG := hG))
    (wp_UnmarshalSnap : go_etcd_io.etcd.pkg.v3.pbutil.MustUnmarshalMessage.specWalSnap (GF := GF) (hG := hG) U)
    (wp_UnmarshalEnt : WalPbIn.UnmarshalEntLaw (GF := GF) (hG := hG) P U)
    (wp_EntIndex : WalPbIn.GetIndexLaw (GF := GF) (hG := hG) P)
    (wp_EntTerm : WalPbIn.GetTermLaw (GF := GF) (hG := hG) P)
    (wp_CloneHs : WalPbIn.CloneHsLaw (GF := GF) (hG := hG) P)
    (wp_tail : go_etcd_io.etcd.server.v3.storage.wal.WAL.tail.spec (GF := GF) (hG := hG))
    (wp_Errorf : fmt.ErrorfErrs.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.WAL.ReadAll.spec (W := W) P Mr := by
  intro R jr r dir nm w s qp qc Q hin hcl
  wp_start as ⟨#Harea, Hp, Hperm, Hop, Hau⟩
  unfold walOpeningF
  icases Hop with ⟨Hgh, Hrh, Hph, %df, %dfd, %jd, Hdff, Hdf, Hdfs⟩
  unfold walReadH walOpenIn walReadTie
  simp only [↓reduceIte]
  icases Hrh with ⟨⟨%lg, %sp, Hlg, #Hzap, Hdir, Hstart, #Hsp⟩, %dec, %IoE, %eof, %ueof, %fs, %locks,
    %lfs, %fp, %rc, %j, Hdecf, Hdec, #Hdenv, ⟨%X, %hj, %gs, %fls, Hn, Hout, ⟨Htf, Hnf⟩, #Hk, %Hgs,
    %Hfs, #Hlks⟩, Hlocks, Hls, Hcap, Hrc, Hfp, ⟨%hrc, Hpipe⟩, He, Hst, Hmd, Henti, Hsnapi, Hns,
    #Hmu, #Henv, #Hcrc⟩
  ihave #Henv0 := Henv
  iunfold encEnv at Henv0
  icases Henv0 with ⟨-, -, #Hsync, -, -⟩
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.Mutex.wp_Lock _ (BI.pure True : IProp GF) $$ [$Hmu $Hsync] as ⟨Hlocked, -⟩
  (try wp_auto)
  wp_apply (wp_Decode walCodec dec «$r0_ptr» IoE eof ueof fs 0 0#32 rfl) $$ [Hdec «$r0»] as %err0 Hpost
  · iframe Hdec Hdenv
    unfold ownRecAny
    iexists _
    iexact «$r0»
  (try wp_auto)
  sorry

end proof

end EtcdGrove
end Perennial
