/-
`snap_recSize` and `walLastHS_snap`, out of `WAL__SaveSnapshot.lean`'s proof so that
`WAL__SaveSnapshotNoErr.lean` imports them without the proof (import tiers, 2026-11-18).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__SaveSnapshot
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__sync
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.encoder__encodeTail
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.walpb.Snapshot__GetIndex
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.walpb.ValidateSnapshotForWrite
public import Spec.go_etcd_io.etcd.pkg.v3.pbutil.MustMarshalMessageWalSnap
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.HandleAppend
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.HandleLaws
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.SnapPure
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.StreamBound
public import Perennial.Proof.sync.Results
public import Proof.ReceiptTactics

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

/-- The snapshot record's size, from its encoding's bound. -/
theorem snap_recSize (c : w32) (d : List w8) (hd : d.length < 2 ^ 40) :
    recSize (recOf ⟨snapshotType, hash.crc32.crc32c c d, d⟩) < 2 ^ 47 := by
  have := recSize_le snapshotType (hash.crc32.crc32c c d) d (by decide)
  omega

theorem walLastHS_snap (H : WalHist) (md : SnapshotMetadataM) :
    walLastHS (H ++ [WalOpG.snap md]) = walLastHS H := by
  simp [walLastHS, List.foldl_append]

end proof

end EtcdGrove
end Perennial
