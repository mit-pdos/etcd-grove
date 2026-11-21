/-
`(*v2stats.ServerStats).becomeLeader()` (`server.go`; `BecomeLeader` and `SendAppendReq` call it
under the stats' mutex). Lean-first (prove-ps2-v2stats, 2026-11-21).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.Defs

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

/-- `ss.becomeLeader()` with the stats' fields (the mutex's, held by the caller) returns them,
the rate queues unchanged: if not leader already, the state, the leader's name (`ss.ID`) and
start time (`time.Now()`) set. -/
abbrev v2stats.ServerStats.becomeLeader.spec : Prop :=
  ∀ (ss : Loc) (v : go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.serverStats),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats ∗
      v2stats.ssInnerAddr ss ↦ v }}
    (App (Val (ss @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.ServerStats.ty @!! go!"becomeLeader")) (Val #()))
  {{ RET #(); ∃ v' : go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.serverStats,
      v2stats.ssInnerAddr ss ↦ v' ∗
      ⌜v'.sendRateQueue' = v.sendRateQueue' ∧ v'.recvRateQueue' = v.recvRateQueue'⌝ }}

end spec

end EtcdGrove
end Perennial
