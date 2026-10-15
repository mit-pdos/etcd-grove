/-
`s.compactRaftLog(snapi)` (`server.go`): the trust boundary (names-only). Lean-first (no Rocq
counterpart); the request path's unit 4b (2026-10-13).
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

/-- `s.compactRaftLog(snapi)` (the contract of a names-only callee: it compacts the
`MemoryStorage`'s log below `snapi`, keeping `SnapshotCatchUpEntries`, unless a snapshot is in
flight) returns, with the logger's reader slot given back. -/
abbrev EtcdServer.compactRaftLog.spec : Prop :=
  ∀ (s : Loc) (snapi : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ srvLgReader s }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"compactRaftLog")) (Val #snapi))
  {{ RET #(); srvLgReader s }}

end spec

end EtcdGrove
end Perennial
