/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/decoder__decodeRecord.lean`.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.decoder__decodeRecord
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.decoder__isTornEntry
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.readInt64
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.decodeFrameSize
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.walpb.Record__Reset
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.walpb.Record__GetType
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.walpb.Record__Validate
public import LinuxFs.Spec.google_golang_org.protobuf.proto.UnmarshalWalRecord
public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.FileBufReader__FileInfo
public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.FileBufReader__Err
public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.FileBufReader__Read
public import LinuxFs.Spec.go_etcd_io.etcd.pkg.v3.crc.digest__Sum32
public import Spec.io.ReadFull
public import Spec.encoding.binary.ReadInt64LE
public import LinuxFs.Spec.fmt.ErrorfErrs
public import LinuxFs.Spec.go_etcd_io.etcd.pkg.v3.crc.digest__Write

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open WalEnc WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [bufio_sem : _root_.Perennial.bufio.Assumptions]

theorem go_etcd_io.etcd.server.v3.storage.wal.decoder.decodeRecord.wp_proof
    (HUnm : ∀ C, proto.UnmarshalWalRecord.spec (GF := GF) (hG := hG) C)
    (HReset : go_etcd_io.etcd.server.v3.storage.wal.walpb.Record.Reset.spec (GF := GF) (hG := hG))
    (HGetType : go_etcd_io.etcd.server.v3.storage.wal.walpb.Record.GetType.spec (GF := GF) (hG := hG))
    (HValidate : go_etcd_io.etcd.server.v3.storage.wal.walpb.Record.Validate.spec (GF := GF) (hG := hG))
    (HErrorf : fmt.ErrorfErrs.spec (GF := GF) (hG := hG))
    (HTorn : go_etcd_io.etcd.server.v3.storage.wal.decoder.isTornEntry.spec (GF := GF) (hG := hG))
    (HRI : go_etcd_io.etcd.server.v3.storage.wal.readInt64.spec (GF := GF) (hG := hG))
    (HDFS : go_etcd_io.etcd.server.v3.storage.wal.decodeFrameSize.spec (GF := GF) (hG := hG))
    (HRF : io.ReadFull.spec (GF := GF) (hG := hG))
    (HFI : go_etcd_io.etcd.client.pkg.v3.fileutil.FileBufReader.FileInfo.spec (GF := GF) (hG := hG))
    (HErr : go_etcd_io.etcd.client.pkg.v3.fileutil.FileBufReader.Err.spec (GF := GF) (hG := hG))
    (HRead : go_etcd_io.etcd.client.pkg.v3.fileutil.FileBufReader.Read.spec (GF := GF) (hG := hG))
    (HWrite : go_etcd_io.etcd.pkg.v3.crc.digest.Write.spec (GF := GF) (hG := hG))
    (HSum : go_etcd_io.etcd.pkg.v3.crc.digest.Sum32.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.decoder.decodeRecord.spec (GF := GF) (hG := hG) := by
  intro C d rp IoE eof ueof fs off c hC
  sorry

end proof

end EtcdGrove
end Perennial
