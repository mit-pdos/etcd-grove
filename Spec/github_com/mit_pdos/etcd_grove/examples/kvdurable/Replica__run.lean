/- Lean-first (no Rocq counterpart).

`r.run(send, snapIndex, hs, rafted)` (kv.go): the incarnation's loop, handling the node's `Ready`s
until `stopc` is closed (or a `Ready` would take the log past `maxIndex`, which does not happen), or
its write fails (the incarnation crashed), then handing `run`'s half of `nodeRunning` back on
`runDone`. It starts from `runStart` (the node as `RestartNode` left it, the replicated state at
the stored snapshot's prefix `ap`), `snapIndex` the stored snapshot's index, `hs` the storage's hard
state, `rafted` raft's applied index at start.

Per `Ready` (`readyGot`): its storage changes under `dmu`, which records its batch's *enter*
(`readyEnter`, `KdPhase.waiting`), or applies it at once for a commit-only batch (it moves only the
durable state's commit index, which the file may lag); a batch raft needs durable is written
(`persist`, whose `durable.Write` fires the *enter* in its atomic update, with `run`'s share of
`nodeRunning`) before its messages are sent (`readyMsgs`), except at role leader
(`readyLeaderMsgs`), applied, or advanced. Nothing is promised of its end: the loop's results are the
store invariant's.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KdStor GF]

attribute [local instance] kdStorageModel

/-- See the file header. -/
abbrev Replica.run.spec : Prop :=
  ∀ (γ : KdNames) (vs : List w64) (dir : GoString) (id : w64) (r n st sts sq : Loc)
    (ρ : KdRepNames) (f : GoFunc) (l ap : List LogEntry) (hs : HardStateM) (hsp : Loc)
    (S : RaftState) (m : Membership) (snapIndex rafted : w64),
  uint.nat rafted = l.length → ap.length ≤ uint.nat snapIndex ∨ snapIndex = W64 ap.length →
  {{ isReplicaR γ vs dir id r n st sts sq ρ ∗ runStart γ id r n st ρ l hs S ap m ∗
      hsOpt hsp hs ∗ sendSpec γ id f }}
    (App (App (App (App (Val (r @!! go.GoType.PointerType kReplicaTy @!! go!"run")) (Val #f)) (Val #snapIndex)) (Val #hsp))
      (Val #rafted))
  {{ RET #(); True }}

end spec

end kvdurable
end EtcdGrove
end Perennial
