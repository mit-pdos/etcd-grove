/-
`storage.OpenSnapshotBackend(cfg, ss, snapshot, hooks)` (`server/storage/backend.go`), as
changed by etcd PR #22046 (branch `pr-verify/etcd-22046`): rename the received snapshot
database `<index>.snap.db` onto the backend file `db`, then drop the index's pending-apply mark
(`ss.ReleaseDBSnapshot(index)`, new in the PR), and open the backend. Lean-first (no Rocq
counterpart); the vocabulary is etcd PR #22518's (`storage/InvSnapshotBackend.lean`) and the
snapshotter's (`etcdserver/api/snap/Defs.lean`).

What the PR adds is the mark's release: the file `ReleaseSnapDBs` was told to keep until it
is applied has been consumed (renamed away), so the mark goes; on the error paths the mark
stays (the caller, `applySnapshot`, panics).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.InvSnapshotBackend
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.Assumptions]

/-- `OpenSnapshotBackend(cfg, ss, snapshot, hooks)`, for a snapshot message `snapshot` (not
`nil`) of index `idx`, and the snapshotter `ss` (`isSnapshotter ss γ dir`): logically atomic on the
snapshotter's pending set `M`. It returns `(be, nil)` (`ok = true`) only after renaming the
snapshot's database file onto the backend file (`fs.renamePending (snapDBPath ss idx)
(cfgBackendPath cfg.DataDir)`), and then, at its linearization point (`ReleaseDBSnapshot`),
removes `idx` from the pending set; otherwise (`ok = false`) it returns `(nil, err)` with an
error whose `Error()` returns a string, leaving the set as it was. The snapshot is left as it
was. -/
abbrev storage.OpenSnapshotBackend.spec : Prop :=
  ∀ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (ss snapshot hooks : Loc)
    (dq : DFrac) (s : SnapshotM) (γ : GName) (dir : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ∗
      isSnapshotter ss γ dir ∗ ownSnapM snapshot dq s }}
  <<{ ∀∀ M, snapPending γ M }>>
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.OpenSnapshotBackend))
      (Val #cfg)) (Val #ss)) (Val #snapshot)) (Val #hooks)) @@ ∅
  <<{ ∃∃ (ok : Bool), snapPending γ (if ok then GMap.delete s.Metadata'.Index' M else M) }>>
  {{ (be err : GoInterface), RET (PairV #be #err);
      ownSnapM snapshot dq s ∗
      (if ok then ⌜err = interface.nil⌝ ∗
          fs.renamePending (snapDBPath ss s.Metadata'.Index') (cfgBackendPath cfg.DataDir')
       else ⌜be = interface.nil⌝ ∗ ∃ e : GoInterfaceOk, ⌜err = interface.ok e⌝ ∗
          fmt.stringMethodSpec e go!"Error") }}

end spec

end EtcdGrove
end Perennial
