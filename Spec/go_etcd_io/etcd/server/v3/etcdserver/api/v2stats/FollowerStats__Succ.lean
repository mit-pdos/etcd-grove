/-
`(*v2stats.FollowerStats).Succ(d)` (`leader.go`; prove-ps2-succ, 2026-11-22: translated with its body;
until then the trust boundary). `Succ` counts a successful send and updates the latency statistics
(float64 running averages and `math.Sqrt` of their variance) under the stats' own lock.
rafthttp's msgappv2 encoder and pipeline call it after each frame. A no-op spec, as the metrics'
(D38). Lean-first.
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

/-- `fs.Succ(d)` of follower stats `LeaderStats.Follower` made (`v2stats.isFollowerStats`: their
mutex, guarding the counts and latencies) returns: it updates them under the mutex. (prove-ps2-succ,
2026-11-22: until then a trust-boundary axiom whose premise was `fs ≠ null` alone, true of Go by
its type safety but giving the proof no ownership of the mutex: `notes/specs-only/ledger.md`.) -/
abbrev v2stats.FollowerStats.Succ.spec : Prop :=
  ∀ (fs : Loc) (d : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats ∗
      v2stats.isFollowerStats fs }}
    (App (Val (fs @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.FollowerStats.ty @!! go!"Succ")) (Val #d))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
