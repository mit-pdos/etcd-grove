/-
`(*EtcdServer).raftStatus()` (`server.go`): raft's status, `s.r.Node.Status()` (srvloops2, 2026-11-21,
with `ensureLeadership`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LeadCheck

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `s.raftStatus()`, any goroutine, with the leadership check's view of the server
(`srvLeadCheckOk`: the wrapper's node, whose `Status()` returns): some status. -/
abbrev EtcdServer.raftStatus.spec : Prop :=
  ∀ (s : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ srvLeadCheckOk s }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"raftStatus")) (Val #()))
  {{ (st : go_etcd_io.raft.v3.Status), RET #st; True }}

end spec

end EtcdGrove
end Perennial
