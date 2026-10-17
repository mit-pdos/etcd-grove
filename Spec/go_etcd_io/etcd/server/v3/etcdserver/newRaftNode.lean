/-
`newRaftNode(cfg)` (`raft.go:123`): the raft wrapper's construction (stage R8b-C of the raft
v3.7 retarget, 2026-10-16; D12). Lean-first (no Rocq counterpart); see `InvNodeStart.lean`.

With `cfg.lg` non-nil (etcd always passes a logger: the `else` branch, `NewRaftLogger` of the
default zap config and `log.Fatalf`, is dead) and `cfg.heartbeat` non-zero (etcd's `TickMs > 0`:
the `heartbeat == 0` branch's `&time.Ticker{}` is dead), it sets raft's logger
(`NewRaftLoggerZap`, `raft.SetLogger`: contracts), allocates `tickMu`, takes `time.Now()`, the
timeout detector (`contention.NewTimeoutDetector(2 * heartbeat)`: a contract), the channels
(`readStateC` of capacity 1, `msgSnapC` of capacity `maxInFlightMsgSnap`, `applyc`, `stopped` and
`done` unbuffered) and the ticker (`time.NewTicker(heartbeat)`: a contract, D10's tick credits),
and returns the struct `r` as `rnBuilt` describes it: its fields read-only but `transport`
(`cfg`'s, nil, which `NewServer` sets), the channels' and the mutex's predicates, both halves of
`applyc`'s SPSC channel and the right to close `done`. The wrapper's names `γ` are the caller's
(`node`, `id`, `nl`, `pre`, `ms`, `γs`, `reg`: raft's node, this node's id and pointer, the start
log, the `MemoryStorage` with its names and registry) but the three `newRaftNode` allocates
(`ap`, `cum`, `done`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvNodeStart

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- See the file header. -/
abbrev newRaftNode.spec : Prop :=
  ∀ (E : RNEnv GF) (node : NodeNames) (id : w64) (nl : Loc) (pre : List EntryModel)
    (ms : Loc) (γs : MemStorNames) (reg : GName) (cv : raftNodeConfig),
  cv.lg' ≠ null →
  cv.heartbeat' ≠ W64 0 →
  -- (etcd-io/etcd#22223) asynchronous storage writes off: the wrapper's proofs cover the
  -- `Ready`/`Advance` path only
  cv.asyncStorageWrites' = false →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      -- (etcd-io/etcd#22223) `context.WithCancel`'s premise
      context.isClosedchanInit ∗
      -- the contracts (`InvNodeStart.lean`)
      rnLoggerZapOk ∗ rnSetLoggerOk ∗ rnTimeoutDetectorOk ∗ rnTickerOk E }}
    (App (Val (@! newRaftNode)) (Val #cv))
  {{ (r : Loc), RET #r;
      ∃ γ : RNNames,
        ⌜γ.node = node ∧ γ.id = id ∧ γ.nl = nl ∧ γ.pre = pre ∧ γ.ms = ms ∧ γ.γs = γs ∧
          γ.reg = reg⌝ ∗
        rnBuilt E γ r cv }}

end spec

end EtcdGrove
end Perennial
