/-
`(*v2stats.FollowerStats).Fail()` (`leader.go`; prove-ps2, 2026-11-21: translated with its body; until
then the trust boundary). `Fail` increments a counter under the stats' own lock (as `Succ` keeps its
latencies: `FollowerStats__Succ.lean`). rafthttp's pipeline calls it after a failed `MsgApp`. A
no-op spec, as `Succ`'s (D38). Lean-first.
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
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- `fs.Fail()` of follower stats `LeaderStats.Follower` made (`v2stats.isFollowerStats`: their mutex,
guarding the failure count) returns: it counts the failure under the mutex. (prove-ps2, 2026-11-21:
until then a trust-boundary axiom whose premise was `fs ≠ null` alone, true of Go by its type
safety but giving the proof no ownership of the mutex: `notes/specs-only/ledger.md`.) -/
abbrev v2stats.FollowerStats.Fail.spec : Prop :=
  ∀ (fs : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats ∗
      v2stats.isFollowerStats fs }}
    (App (Val (fs @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.FollowerStats.ty @!! go!"Fail")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
