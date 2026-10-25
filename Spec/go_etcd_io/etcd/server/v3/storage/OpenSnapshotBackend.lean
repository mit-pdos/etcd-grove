/-
`storage.OpenSnapshotBackend(cfg, ss, snapshot, hooks)` (`server/storage/backend.go`): the
database snapshot of `snapshot`'s index, which the transport saved in the snapshotter's
directory, renamed onto the backend's path (`cfg.BackendPath()`) and opened (`OpenBackend`). D22
S-f, 2026-10-19 (translated with its body; `notes/decisions.md`, "D22 S-f carried out").
Lean-first (no Rocq counterpart); `applySnapshot`'s callee (D22 S-j).

The pre: the snapshotter (`isSnapshotter`), the snapshot's `Metadata` field and its metadata
`md` (read, given back), the file at `snapDBPath ss md.Index` holding `D` (`fileHolds`, D22 S-i's
snapshot directory gives it, with `D`'s certificate `dbImage`), the backend's path the program's
(`pathOwn`, from the server's start) and `openPre` (`InvOpen.lean`) for the hooks `hooks` as a
`backend.Hooks`. The post: on success the backend over `D` (`newPost`, and its no-compaction token
if `D` records none, as `OpenBackend`'s; D22 S-g) and the
snapshot's entry the program's; on an error (the file not found, the rename failed), with `nil`
for the backend, the file and the path back.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.InvOpen
public import Proof.go_etcd_io.raft.v3.InvPb
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Image

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI backend storage go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.Assumptions]

/-- `OpenSnapshotBackend(cfg, ss, snapshot, hooks)`: the snapshot's database file renamed onto the
backend's path and opened, or an error with nothing moved. (D22 receiver epochs, S8a, 2026-10-24:
the creator's `K` for the fresh backend's payment rights, `OpenBackend`'s.) -/
abbrev storage.OpenSnapshotBackend.spec : Prop :=
  ∀ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (ss sn mp hk : Loc) (dq dq' : DFrac)
    (md : SnapshotMetadataM) (P : BParams) (D : Data) (W Pk K : BNames → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ∗ snap.isSnapshotter ss ∗
      sn.[raftpb.Snapshot, go!"Metadata"] ↦{dq} mp ∗ smOpt mp dq' md ∗
      fileHolds (snap.snapDBPath ss md.Index') D ∗ pathOwn (config.backendPathOf cfg.DataDir') ∗
      openPre cfg (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.BackendHooks.ty) #hk)
        P D W Pk K }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.OpenSnapshotBackend)) (Val #cfg))
      (Val #ss)) (Val #sn)) (Val #hk))
  {{ (be err : GoInterface), RET (PairV #be #err);
      sn.[raftpb.Snapshot, go!"Metadata"] ↦{dq} mp ∗ smOpt mp dq' md ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (b : Loc) (γ : BNames),
          ⌜be = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #b⌝ ∗
          newPostK γ P W Pk K b D ∗ (⌜mvcc.noCmpData D⌝ -∗ mvcc.bkNoCmp γ) ∗
          pathOwn (snap.snapDBPath ss md.Index')) ∨
       (⌜err ≠ GoInterface.nil ∧ be = GoInterface.nil⌝ ∗
          fileHolds (snap.snapDBPath ss md.Index') D ∗ pathOwn (config.backendPathOf cfg.DataDir'))) }}

end spec

end EtcdGrove
end Perennial
