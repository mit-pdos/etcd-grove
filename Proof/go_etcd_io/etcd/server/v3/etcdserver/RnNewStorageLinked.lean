/-
**`NewStorage`'s contract, linked** (wal-item3, 2026-11-21; the linking module of `RnNewStorage.lean`, "Import
tiers"): the storage methods' specs at every open WAL `h` (`walStorSpecs_holds`: each storage method's proof
over the WAL's linked result at the server's message model `walSrvP`/`walSrvMr` and `h`'s file-system instances,
the instance's laws from `walSrvPb_laws` and `walSrvP_marshalHs`, the latter over `proto.MarshalPb`'s trust
boundary at the registered `raftpb.HardState`, `RaftModel/PbHardState.lean`), and from them and `NewStorage`'s
proof the law `rnNewStorageOk.law` (`rnNewStorageOk_law_holds`). Both take `os`'s `fileStat`/`file` field
assumptions, as the WAL `Link`'s results do, which the server's package assumptions do not include (goose emits
no field steps for `os`'s trusted layouts): so the server `Link`'s `bootstrappedRaft.wp_newRaftNode`, which passes
the law to `newRaftNode`'s proof, takes them, and so does every result reaching it (`etc/gen-link.py`'s
`SEM_PREMISES`), up to the closed theorems (wal-nostorageok, 2026-11-21: until then `rnNewStorageOk` was
`newRaftNode`'s spec's premise, and every closed theorem's). (Until Perennial `04b42a139`, 2026-11-21, they also took the semantic hypothesis
`UntypedRuneSemantics`, for `filepath.join` and `filepathlite.Base`/`FromSlash`: `string(Separator)`,
`Separator == '/'`; Perennial's semantics now steps the one and goose folds the other.) The server's `Link`
imports this module, so the trust-base report sees these results.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.RnNewStorage
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.Link
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.RaftModel.LawsHsMarshal
public import Proof.go_etcd_io.etcd.server.v3.storage.NewStorage
public import Proof.go_etcd_io.etcd.server.v3.storage.storage__Save
public import Proof.go_etcd_io.etcd.server.v3.storage.storage__SaveSnap
public import Proof.go_etcd_io.etcd.server.v3.storage.storage__Sync
public import Proof.go_etcd_io.etcd.server.v3.storage.storage__Close
public import Proof.go_etcd_io.etcd.server.v3.storage.storage__Release
public import Proof.google_golang_org.protobuf.proto.MarshalPb
public import Proof.google_golang_org.protobuf.proto.SizePb
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Snapshotter__ReleaseSnapDBs
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetIndex

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section linked
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [os.fileStat.FieldAssumptions] [os.file.FieldAssumptions]

/-- **The storage methods' specs at every open WAL** (see the file header). -/
theorem walStorSpecs_holds
    (wpGI : raftpb.SnapshotMetadata.GetIndex.spec (GF := GF) (hG := hG)) (h : WalH GF) :
    walStorSpecs h := by
  letI := h.ext; letI := h.semOk; letI := h.has; letI := h.W; letI := h.inj; haveI := h.sat
  haveI := h.satL
  have L := walSrvPb_laws (GF := GF) (hG := hG)
  have Lhs := walSrvP_marshalHs (GF := GF) (hG := hG) proto.MarshalPb.wp_proof
  exact
    ⟨storage.storage.Save.wp_proof walSrvP walSrvMr
        (walfs.go_etcd_io.etcd.server.v3.storage.wal.WAL.wp_Save walSrvP walSrvMr L.getIndex L.isEmpty
          L.marshalEnt Lhs L.mustSync L.size L.zero),
      storage.storage.SaveSnap.wp_proof walSrvP walSrvMr
        (walfs.go_etcd_io.etcd.server.v3.storage.wal.WAL.wp_SaveSnapshot walSrvP walSrvMr L.isEmpty Lhs),
      storage.storage.Sync.wp_proof walSrvP walSrvMr
        (walfs.go_etcd_io.etcd.server.v3.storage.wal.WAL.wp_Sync walSrvP walSrvMr),
      storage.storage.Close.wp_proof walSrvP walSrvMr
        (walfs.go_etcd_io.etcd.server.v3.storage.wal.WAL.wp_Close walSrvP walSrvMr),
      storage.storage.Release.wp_proof walSrvP walSrvMr wpGI
        (walfs.go_etcd_io.etcd.server.v3.storage.wal.WAL.wp_ReleaseLockTo walSrvP walSrvMr)
        snap.Snapshotter.ReleaseSnapDBs.wp_proof⟩

/-- **`NewStorage`'s contract** (`rnNewStorageOk.law`, see the file header). -/
theorem rnNewStorageOk_law_holds
    (wpGI : raftpb.SnapshotMetadata.GetIndex.spec (GF := GF) (hG := hG)) :
    rnNewStorageOk.law (GF := GF) (hG := hG) :=
  rnNewStorageOk_holds storage.NewStorage.wp_proof (walStorSpecs_holds wpGI)

end linked

end EtcdGrove
end Perennial
