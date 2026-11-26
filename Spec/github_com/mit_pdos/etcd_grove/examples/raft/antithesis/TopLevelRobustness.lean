/- Lean-first (no Rocq counterpart).

# `raft/antithesis`: the top-level robustness result, stated

`raft_antithesis_robust_msgs`: the Antithesis harness's top-level result for parity batch B1's
scope (messages and N servers: the **Scope** paragraph below; the plain name is kept for the
theorem over Antithesis's whole model, mit-pdos/etcd-grove#33), an instance of the generic robustness statement
(`Robustness/Statement.lean`, `Robust crashing stable g threads bound`: in every execution of the
machines that may crash and restart and of those that never crash, each a fresh Go process, of
fewer than `bound` steps along which every machine keeps fewer than `threads` threads, no thread is
stuck and none has an unrecovered panic). This file only states it (to audit); the proof is in
`Proof/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/TopLevelRobustness.lean`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.TopLevelDefs
public import Robustness.Statement

@[expose] public section

noncomputable section

set_option pp.fullNames true

set_option linter.unusedSectionVars false

namespace Perennial

namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section closed

attribute [local instance] trivialExts trivialExtsSemantics trivialExtsInterp trivialExts_hasExt

variable [go_gctx : GoGlobalContext]

/-- **The Antithesis harness never fails** (`Robustness.Robust`, `Robustness/Statement.lean`):
`antithesisProgram` (`examples/raft/antithesis`: the package's initialization, then `Main()`) alone on
one machine that never crashes, a fresh Go process (`Robust`'s premise): in every execution of fewer
than `antStepBound` (`2 ^ 61 - 3`) steps along which fewer than `antThreadBound` (`2 ^ 31`) threads
are live at once, no thread is stuck and none has an unrecovered panic.

**What it says.** `Main` draws a run's mode within its scope (`DrawMode(MainScope())`) and runs a
cluster of verified raft `RawNode`s in it (`RunCluster`): each node's goroutine starts the node from
its disk, then takes one input at a time (a message, a tick, a proposal, a campaign, a read index, a
leadership transfer, an unreachable report) and drains raft's `Ready`s, reporting each step to one
recorder; the network delivers every message from a goroutine of its own, zero to
`MaxDeliveries` times, in any order (a message delivered no time is reported to its sender as
unreachable); a proposer, a campaigner, a reader and a transferer call the client API on random
nodes until the run stops; after `Settle` the run stops. `Main` then runs `check.Run`, a Go
transcription of Antithesis's trace binding `EtcdBinding.tla` (`third_party/etcd-raft-formalized`),
on the recorded stream at the run's constants (`c.CheckConfig()`: `Server`, `InitVoters`,
`Bootstrapped`), and panics unless it answers `ACCEPTED`. No panic therefore means every stream the
harness can record is accepted by `check`. That an accepted stream is a behaviour of `EtcdRaft.tla`
rests on `check` being a faithful transcription of `EtcdBinding.tla` (evidence: the differential
tests against TLC, `notes/antithesis-check-design.md` §7) and on Antithesis's own claim that each
binding step is a sequence of `EtcdRaft` steps (§1).

**Scope.** Batch B1 of `notes/antithesis-parity-design.md` (`driver.go`'s scope constants): 3 or 5
servers, all voters or (non-voters) 5 servers of which 3 are the initial voters; empty or
bootstrapped logs; PreVote and CheckQuorum drawn per run; read indexes and leadership transfers;
the network may lose or duplicate a message; `MaxInflightMsgs` and `MaxSizePerMsg` drawn from the
simulator's values. Synchronous storage (`MemoryStorage`, written within the node's `Ready`); no
restarts, snapshots or membership changes. The network drops every forwarded proposal
(`Cluster.send`: a follower's `MsgProp` to its leader; mit-pdos/etcd-grove#44), so the theorem
does not cover forwarding.

**Premises.** None but the package assumptions of the translations (`antithesis.Assumptions`, which
includes `antithesis.check.Assumptions`) and `log.NewModel` (the model of `log.New`, which raft's
package initializer calls), both trusted.

**Extensions.** `trivialExts` (`[idIssueExt]`, the request ids' issue record, whose one operation
the program never runs), in any initial state: the program touches no file and no network.

**Bounds.** `antStepBound` is the most the proof allows: the run's time receipts bound the indices
raft hands its storage (raft's `readyFits`) and the stream's numbers (`check`'s `numBound`, `2 ^ 61`).
`antThreadBound` is a real limit of the program: the network's goroutines are counted in a
`sync.WaitGroup`, whose `int32` counter panics past `2 ^ 31`.

**Trust.** The Goose translations of the harness, `check`, raft and the standard library; the
package assumptions above; the axioms the proof reaches (`etc/tcb-collections/antithesis.txt`):
protobuf-go's `proto` boundary under raft (`proto.ClonePb` and the others' `.wp_proof`) and the
raftpb codec registrations `pbEntryC_reg`, `pbMessageC_reg`. -/
def raft_antithesis_robust_msgs.spec : Prop :=
  ∀ [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
    [hLog : log.NewModel] (σ : state) (g : GlobalState),
    Robustness.Robust [] [(antithesisProgram, σ)] g (threads := antThreadBound)
      (bound := antStepBound)

end closed
end EtcdGrove
end Perennial

end
