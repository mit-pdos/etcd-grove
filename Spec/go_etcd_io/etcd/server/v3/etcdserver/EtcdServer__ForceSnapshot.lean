/-
`s.ForceSnapshot()` (`server.go`), as etcd#21574 rewrites it: `s.Backend().ForceCommit()`. Lean-first
(no Rocq counterpart; 2026-10-17).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplyAll

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `s.ForceSnapshot()` (etcd#21574), with a reader slot of `s.bemu` (given back): it commits the
current backend (`ForceCommit`, under the backend's contract `srvBackendCommits`, `s.bemu`'s
invariant) and returns. It no longer touches the apply loop's snapshot state: before the PR it set
`s.forceDiskSnapshot`, which made the next `snapshotIfNeededAndCompactRaftLog` take a disk snapshot. -/
abbrev EtcdServer.ForceSnapshot.spec : Prop :=
  ∀ (s : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ srvBemuReader s }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"ForceSnapshot")) (Val #()))
  {{ RET #(); srvBemuReader s }}

end spec

end EtcdGrove
end Perennial
