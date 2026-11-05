/-
`newRaftNode(cfg)` (`raft.go:123`): the raft wrapper's construction (stage R8b-C of the raft
v3.7 retarget, 2026-10-16; D12). Lean-first (no Rocq counterpart); see `InvNodeStart.lean`.

With `cfg.lg` non-nil (etcd always passes a logger: the `else` branch, `NewRaftLogger` of the
default zap config and `log.Fatalf`, is dead) and `cfg.heartbeat` positive (a scope restriction,
2026-11-03, the final whole-`bootOk` review's S2, `notes/decisions.md`: Go's `heartbeat == 0` branch,
`&time.Ticker{}`, a ticker that never fires, is not covered; a negative one makes `NewTicker` panic), it sets raft's logger
(`NewRaftLoggerZap`, `raft.SetLogger`: contracts), allocates `tickMu`, takes `time.Now()`, the
timeout detector (`contention.NewTimeoutDetector(2 * heartbeat)`: a contract), the channels
(`readStateC` of capacity 1, `msgSnapC` of capacity `maxInFlightMsgSnap`, `applyc`, `stopped` and
`done` unbuffered) and the ticker (`time.NewTicker(heartbeat)`: since 2026-11-03 a callee of the
proof, Perennial's proved spec; until then a contract, `rnTickerOk`, in the precondition; its ticks
carry nothing, `isRNTicker`'s bag, since 2026-11-05 with no premise on `E.T`),
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- See the file header. -/
abbrev newRaftNode.spec : Prop :=
  ∀ (E : RNEnv GF) (node : SrvRaft) (id : w64) (nl : Loc) (pre : List EntryModel)
    (ms : Loc) (γs : MemStorNames) (key : GName) (wal : WalNames) (cv : raftNodeConfig),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      -- the contracts (`InvNodeStart.lean`; 2026-11-03: `rnTickerOk E` gone, the ticker proved)
      rnLoggerZapOk ∗ rnSetLoggerOk ∗ rnTimeoutDetectorOk ∗
      -- (2026-11-03: until then the implication `cv.lg' ≠ null →`) a logger; (S2: until then the
      -- implication `heartbeat ≠ 0`) a positive heartbeat (2026-11-03 to 2026-11-05, the user's
      -- S1: also `⌜E.T = iprop(True)⌝`, ticks carrying nothing, which `isRNTicker` now says)
      ⌜cv.lg' ≠ null⌝ ∗ ⌜0 < sint.Z cv.heartbeat'⌝ }}
    (App (Val (@! newRaftNode)) (Val #cv))
  {{ (r : Loc), RET #r;
      ∃ γ : RNNames,
        ⌜γ.node = node ∧ γ.id = id ∧ γ.nl = nl ∧ γ.pre = pre ∧ γ.ms = ms ∧ γ.γs = γs ∧
          γ.key = key ∧ γ.wal = wal⌝ ∗
        rnBuilt E γ r cv }}

end spec

end EtcdGrove
end Perennial
