/- Lean-first (no Rocq counterpart).

## `node.run()` (node.go:343)

The node's goroutine, forked by `RestartNode`: it owns the `RawNode` (`ownRawNode`, idle:
no `Ready` outstanding), `run`'s half of `dlv` at the committed log handed out so far,
the whole of `rof` (no `Ready` handed out), and the budget's bound on its term; (2026-10-29,
stage U9a) the closing side of `done` (`ownBroadcastChan … .Pending`) and its half of `live`
(`nodeLiveRaw γ 1`). It returns when it receives the client's half on `stop`: it closes `done`
with the node stopped (`nodeStoppedRaw`). (2026-11-01, durability stage I-2/I-3) With its share of
the generation of its id's slot (in `nodeLiveRaw`), its halves of `dur`/`bw` and the generation's
free queue, from which it cuts each `Ready`'s batch (`readyCut`); (2026-11-01, stage II (n), the stop's
option (c)) at the stop it answers on `stop` with its share of the generation and its protocol state
(`stopAns`), from which `Stop` gives the id's slot back itself (`raftIdSlot`, the API's `nodeVacant`,
`raft_stop`).
-/
module

public import Proof.go_etcd_io.raft.v3.InvNodeChan
public import Proof.go_etcd_io.raft.v3.TraceFits
public import Proof.go_etcd_io.raft.v3.InvRawnodeReady
public import Proof.go_etcd_io.raft.v3.InvApplyConf
public import Spec.go_etcd_io.raft.v3.RawNode__ProposeConfChange

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- What `run` starts with (see the file header). -/
def runPre (γ : NodeNames) (id : w64) (n : Loc) : IProp GF :=
  iprop(∃ (nv : node) (rs : RNState) (x : List EntryM × List EntryM ×
      List EntryM × HardStateM × Option SnapLoan),
    n ↦□ nv ∗ ownRawNode γ.raft nv.rn' id rs ∗
    ⌜rs.steps = [] ∧ rs.unpersisted = [] ∧ rs.storage = γ.stor⌝ ∗
    dghostVar γ.dlv (DFrac.own (1 : Qp).half) (rs.delivered, rs.phs) ∗
    dghostVar γ.rof (DFrac.own (1 : Qp).half) x ∗ dghostVar γ.rof (DFrac.own (1 : Qp).half) x ∗
    -- (2026-10-17; until then at the term) the term ceiling within the budget
    termLB γ.bud rs.tc ∗
    -- (2026-10-15, stage N) `run`'s side of the configuration shared with the driver
    runCfg γ rs ∗
    -- (2026-10-29, stage U9a) `run` closes `done` when stopped, and holds its half of `live`
    -- ((2026-11-01, durability stage I-3) with its share of the generation)
    ownBroadcastChan nv.done' γ.done (nodeStoppedRaw γ) .Pending ∗ nodeLiveRaw γ 1 ∗
    -- (2026-11-01, durability stage I-3/I-8) its half of the durable state and role the driver
    -- recorded, both halves of the last batch's maps (no `Ready` out), the generation's queue free
    dghostVar γ.dur (DFrac.own (1 : Qp).half) (rs.dur, rs.role) ∗
    (∃ W : DurMaps × (RaftState × StateType), dghostVar γ.bw (DFrac.own 1) W) ∗
    slotFree γ.raft id γ.gen)

/-- **What the gated `node.run` needs of a traced node** beyond `runPre` (pure; `StartNode`'s traced
proof discharges it): the node is dynamic (`confcP`'s static arm, `CCShrink`, has no traced callee: every
node of the node API is dynamic, `StartNode`'s `HdynOk`), the receipts fit the trace's bound past the
bootstrap log (`traceReadyFits`: the cluster's `readyFits` at its `RaftNames`, for the traced triples'
premise and `ownStepGhost_traceBound`), and the term ceiling's successor is below the trace's bound
(`receiptBound GF + 2 ≤ traceNumBound`: the ceiling `rs.tc` is at most `receiptBound GF` by `termLB` and
`budgetInv`, so `rs.tc + 1 < traceNumBound`, the traced triples' `Htcb`). The harness has the last two
from `tcRunFits` (`receiptBound GF + 3 ≤ 2^61`, three voters' bootstrap entries). -/
def RunTracedOk (GF : BundledGFunctors) [ReceiptGS GF] (γ : NodeNames) : Prop :=
  γ.mode.isDyn = true ∧ traceReadyFits GF γ.raft ∧ receiptBound GF + 2 ≤ traceNumBound

/-- See the file header. (2026-11-12, trace-check step 5: step 4's `node.run.gatedSpec`, replacing this statement in place) Both modes: the premise `γ.raft.reTrace = none` replaced by the gated `RunTracedOk`, and the precondition's gated half of the token escrow's pending deposit (`rtkRun γ.esc none`, `True` untraced). -/
abbrev node.run.spec : Prop :=
  ∀ (γ : NodeNames) (id : w64) (n : Loc),
  (γ.raft.reTrace ≠ none → RunTracedOk GF γ) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNodeChan γ id n ∗
      runPre γ id n ∗ gateTr γ.raft.reTrace (rtkRun γ.esc none) }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"run")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
