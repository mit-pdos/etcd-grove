/-
**The raft node's slots in the boot hub** (2026-11-03; the slot convention the user approved,
`notes/spec-first-plan.md`, "The slot convention"; the final whole-`bootOk` review's S2). Lean-first.

The raft node (`etcdserver/raft.go`'s `raftNode`, built by `newRaftNode`) asks one thing of the
server's configuration: its clock. `newRaftNode` starts `time.NewTicker(heartbeat)` with the
heartbeat Go computes from the configuration, `TickMs` milliseconds as a `time.Duration`
(`cfg.TickMs * 10^6`, wrapping): `NewTicker` panics for a negative duration, and a zero one
(`&time.Ticker{}`, which never fires) is not covered, a scope restriction. `NewServer.spec` names
it only through `raftNode.bootCfg`, sealed (`etc/import-all.txt`): a later condition of the raft
node on the configuration changes its body and laws, not the hub's text. No `raftNode.bootRes` or
`raftNode.bootOk` (the node takes no program-start resource, and `bootstrap` gives it nothing
beyond `bootOk`'s raft clauses, not yet a slot).
-/
module

public import GeneratedProof.go_etcd_io.etcd.server.v3.config

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

section slots
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]

/-- **The raft node's conditions on the configuration** (sealed): the heartbeat Go computes
(`TickMs` milliseconds, wrapping) positive. -/
@[no_expose] def raftNode.bootCfg (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) : Prop :=
  0 < sint.Z (cfg.TickMs' * W64 1000000)

/-- `raftNode.bootCfg` at the examples' clock (`TickMs = 100`, `examples/lib/etcdstart/etcdstart.go`). -/
theorem raftNode.bootCfg_of (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig)
    (htk : cfg.TickMs' = W64 100) : raftNode.bootCfg cfg := by
  unfold raftNode.bootCfg; rw [htk]; decide

/-- **What `newRaftNode` takes from `raftNode.bootCfg`**: the heartbeat it hands `time.NewTicker`
positive (its spec's pure premise, at the heartbeat `bootOk`'s `Hraft` states). -/
theorem raftNode.bootCfg_heartbeat (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig)
    (h : raftNode.bootCfg cfg) : 0 < sint.Z (cfg.TickMs' * W64 1000000) := h

end slots

end EtcdGrove
end Perennial
