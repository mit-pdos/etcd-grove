/-
`wal.Create` over `fsExt`: the proof (W4 of `notes/wal-fsext-plan.md`; spec
`LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/Create.lean`). The callees' specs not yet proved
over `fsExt` are hypotheses (`CreateCallees.lean`; the W4 log lists them). **Unfinished**: the body is
proved up to the frontier `sorry` (the W4 log, eleventh session, says where). Lean-first.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.Create
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.CreateCallees
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.syncDir
public import LinuxFs.Spec.path.filepath.Clean
public import LinuxFs.Spec.path.filepath.Join
public import LinuxFs.Spec.go_uber_org.zap.String
public import LinuxFs.Spec.go_uber_org.zap.Error
public import LinuxFs.Spec.go_uber_org.zap.Logger__Warn
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateTmp
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateArea
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateAbsent

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Fs WalEnc WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [fu_sem : go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]
variable [os_sem : os.Assumptions] [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions]

theorem wal.Create.wp_proof (C : WalCodec) (Mr : WalMarshal)
    (wp_Exist : wal.Exist.specCreate (GF := GF) C Mr)
    (wp_FExist : go_etcd_io.etcd.client.pkg.v3.fileutil.Exist.spec (GF := GF) (hG := hG))
    (wp_Clean : filepath.Clean.spec (GF := GF) (hG := hG))
    (wp_RmAbs : os.RemoveAll.specAbsentS (GF := GF) (hG := hG))
    (wp_RmDir : os.RemoveAll.specDirS (GF := GF) (hG := hG))
    (wp_CDA : fileutil.CreateDirAll.specTmp (GF := GF) (hG := hG))
    (wp_String : zap.String.spec (GF := GF) (hG := hG))
    (wp_Error : zap.Error.spec (GF := GF) (hG := hG))
    (wp_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG)) :
    wal.Create.spec (GF := GF) C Mr := by
  intro lg R jr r dir nm mp md qp Q hin hr hmp
  wp_start as ⟨#Hinit, #Hzap, #Hmd, #Hok, #Hdd, Hp, Hres, Hperm, Hu, Hau⟩
  try wp_auto
  sorry

end proof

end EtcdGrove
end Perennial
