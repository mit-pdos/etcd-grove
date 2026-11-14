/-
`(*WAL).renameWAL` over `fsExt`: the proof (W4 of `notes/wal-fsext-plan.md`, twelfth session; spec
`LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__renameWAL.lean`). **Not started** (`sorry`):
the callees' specs it will use are its hypotheses (`os.RemoveAll.specAbsentN`, `os.Rename.specDirSnc`,
`newFilePipeline.spec`, `fileutil.OpenDir.spec`, `renameWALUnlock`'s, itself a hypothesis); `errors.As`
of the rename's error (an `*os.LinkError`, or any error: both branches are covered by the post) still
needs a spec. Lean-first.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__renameWAL
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__renameWALUnlock
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.CreateCallees
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.newFilePipeline
public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.OpenDir

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Fs WalEnc WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [fu_sem : go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]

theorem go_etcd_io.etcd.server.v3.storage.wal.WAL.renameWAL.wp_proof (P : WalPbIn GF)
    (Mr : WalMarshal)
    (wp_RmAbsN : os.RemoveAll.specAbsentN (GF := GF) (hG := hG))
    (wp_Rename : os.Rename.specDirSnc (GF := GF) (hG := hG))
    (wp_nfp : go_etcd_io.etcd.server.v3.storage.wal.newFilePipeline.spec (GF := GF) (hG := hG))
    (wp_OpenDir : go_etcd_io.etcd.client.pkg.v3.fileutil.OpenDir.spec (GF := GF) (hG := hG))
    (wp_unlock : go_etcd_io.etcd.server.v3.storage.wal.WAL.renameWALUnlock.spec (W := W) P Mr) :
    go_etcd_io.etcd.server.v3.storage.wal.WAL.renameWAL.spec (W := W) P Mr := by
  sorry

end proof

end EtcdGrove
end Perennial
