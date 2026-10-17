/-
`storage.OpenSnapshotBackend(cfg, ss, snapshot, hooks)` (`server/storage/backend.go`), as
changed by etcd PR #22518 (branch `pr-verify/etcd-22518`): rename the received snapshot
database `<index>.snap.db` onto the backend file `db`, sync the snap directory, open the
backend. Lean-first (no Rocq counterpart); see
`Proof/go_etcd_io/etcd/server/v3/storage/InvSnapshotBackend.lean`.

What the PR adds is the durability of the rename before the function reports success: the
caller (`EtcdServer.applySnapshot`) then points the consistent index at the new backend and
closes the old one, whose last commit writes the snapshot's index into the old file; if the
rename were lost in a crash after that commit, the member would restart on the old database
with the new index (etcd-io/etcd#22498).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.InvSnapshotBackend

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
`nil`): it returns `(be, nil)` only once the backend file's directory entry is durable
(`fs.entryDurable (cfgBackendPath cfg.DataDir)`: the rename onto it was followed by a
successful sync of its directory); otherwise `(nil, err)` with an error whose `Error()` returns
a string. The snapshot is left as it was. -/
abbrev storage.OpenSnapshotBackend.spec : Prop :=
  ∀ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (ss snapshot hooks : Loc)
    (dq : DFrac) (s : SnapshotM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ∗
      ownSnapM snapshot dq s }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.OpenSnapshotBackend))
      (Val #cfg)) (Val #ss)) (Val #snapshot)) (Val #hooks))
  {{ (be err : GoInterface), RET (PairV #be #err);
      ownSnapM snapshot dq s ∗
      ((⌜err = interface.nil⌝ ∗ fs.entryDurable (cfgBackendPath cfg.DataDir')) ∨
       (⌜be = interface.nil⌝ ∗ ∃ e : GoInterfaceOk, ⌜err = interface.ok e⌝ ∗
          fmt.stringMethodSpec e go!"Error")) }}

end spec

end EtcdGrove
end Perennial
