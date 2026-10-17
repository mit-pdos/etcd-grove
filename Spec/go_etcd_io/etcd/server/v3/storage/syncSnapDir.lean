/-
`storage.syncSnapDir(dir)` (`server/storage/backend.go`), new in etcd PR #22518 (branch
`pr-verify/etcd-22518`): open the directory, `fsync` it, close it. Lean-first (no Rocq
counterpart); see `Proof/go_etcd_io/etcd/server/v3/storage/InvSnapshotBackend.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.InvSnapshotBackend

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.Assumptions]

/-- `syncSnapDir(dir)`, with a rename of `src` onto `dst` in `dir` pending: on success
(`nil`) the rename's directory entry is durable; on failure the error's `Error()` returns a
string (and nothing is known of the rename: it is still pending if the directory could not be
opened, unknown if the sync failed). -/
abbrev storage.syncSnapDir.spec : Prop :=
  ∀ (dir src dst : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ∗
      fs.renamePending src dst ∗ ⌜fs.dirOf dst = dir⌝ }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.syncSnapDir)) (Val #dir))
  {{ (err : GoInterface), RET #err; fsResult err (fs.entryDurable src dst) iprop(True) }}

end spec

end EtcdGrove
end Perennial
