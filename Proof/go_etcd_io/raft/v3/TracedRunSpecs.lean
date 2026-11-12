/-
Lean-first (no Rocq counterpart). **Step 4 of the trace-check design (2026-11-12): the three statements
the gated `node.run` is proved from** (`notes/trace-check-design.md`, "Step 4 (2026-11-12): the
statements"; `notes/decisions.md`, "Step 4: the traced Advance, applyConfChange and run statements").
Raft-internal (not on `etc/api/raft.txt`). Statements only: nothing here is proved but the two
instances that show a statement generalizes today's (`node.run.spec_of_gatedSpec`,
`RawNode.Advance.spec_of_tracedSpec`).

- `node.run.gatedSpec`: `node.run.spec` for both modes. Today's premise `γ.raft.reTrace = none` is
  replaced by the gated pure premise `RunTracedOk` (a traced node is dynamic, the receipts fit the
  trace's bound, the term ceiling's arithmetic), and the precondition gains `run`'s half of the token
  escrow's pending deposit (`rtkRun γ.esc none`, gated: `True` untraced), which `runPre` does not hold.
- `RawNode.Advance.tracedSpec`: `RawNode.Advance.spec` for both modes (one statement, as
  `RawNode.acceptReady.spec` since slice 28n): today's premise `γ.reTrace = none` is replaced by the
  gated bounds of `acceptReady`'s and the absence of a lent snapshot. Every other traced content (the
  capability, the clauses, `TrNoSnap`, the self-addressed responses' tokens) is inside `ownRawNode`
  (`rnTrace`, `pendingRel`'s `selfTok`), on both sides of the triple.
- `raft.applyConfChange.tracedSpec`: `raft.applyConfChange.spec` for both modes: today's premise
  `s.gh.tr = none` is replaced by the gated premises of a follower whose change keeps its
  configuration (the leader excluded at the `confc` arm by clause 1(c), lemma (ii) and G3 (a)), and the
  capability (`trCapB`, `emp` untraced) is threaded booted from `s` to the end state.

**The intended theorem** (step 4's, `notes/trace-check-design.md` §9; to be proved in
`Proof/go_etcd_io/raft/v3/node__run.lean` or a sibling, not stated here):

    theorem node.run.gated_of
        (wp_RawNode_HasReady : RawNode.HasReady.spec) (wp_RawNode_readyWithoutAccept : …)
        (wp_RawNode_acceptReady : RawNode.acceptReady.spec)
        (hAdv : RawNode.Advance.tracedSpec)
        (wp_RawNode_Tick : RawNode.Tick.spec) (wp_raft_Step : raft.Step.spec)
        (hb : stepBundle_traced.statement)
        (wp_raft_hasLeader …) (wp_IsResponseMsg …) (wp_IsLocalMsgTarget …)
        (hCC : raft.applyConfChange.tracedSpec)
        (wp_GetType …) (wp_GetFrom …) (wp_getStatus …) :
        node.run.gatedSpec

with `node.run.spec` its instance (`node.run.spec_of_gatedSpec`) and today's `node.run.wp_proof`'s
`RawNode.Advance.spec`/`raft.applyConfChange.spec` arguments replaced by the two hypotheses.
-/
module

public import Spec.go_etcd_io.raft.v3.node__run
public import Spec.go_etcd_io.raft.v3.RawNode__Advance
public import Spec.go_etcd_io.raft.v3.raft__applyConfChange
public import Proof.go_etcd_io.raft.v3.TraceFits
public import Proof.go_etcd_io.raft.v3.TracedCap
public import Proof.go_etcd_io.raft.v3.InvRtk

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

/-! ## `node.run`, gated -/

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

/-- **`node.run()` in both modes** (step 4; design §3.2): `node.run.spec` with its premise
`γ.raft.reTrace = none` dropped, the traced content inside the invariants and predicates it opens
(`isNodeChan`'s gates and escrow, `ownRawNode`'s `rnTrace`). It takes the gated premise `RunTracedOk`
and, gated (`True` untraced), `run`'s half of the escrow's pending deposit at `none`
(`rtkRun γ.esc none`, `InvRtk.lean`; allocated with the escrow, `rtk_alloc`, at a traced node's start):
`run` lends it at every `advancec` rendezvous (`advDep`/`advRet`) and needs it at the `readyc` commit
(`esc_send_prep`), and `runPre` does not hold it (today's untraced proof makes it by `gateTr_none`).
Today's statement is its instance (`node.run.spec_of_gatedSpec`). -/
abbrev node.run.gatedSpec : Prop :=
  ∀ (γ : NodeNames) (id : w64) (n : Loc),
  (γ.raft.reTrace ≠ none → RunTracedOk GF γ) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNodeChan γ id n ∗
      runPre γ id n ∗ gateTr γ.raft.reTrace (rtkRun γ.esc none) }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"run")) (Val #()))
  {{ RET #(); True }}

open Iris.ProofMode in
/-- **`node.run.spec` is `node.run.gatedSpec`'s instance**: untraced, `RunTracedOk`'s premise is
vacuous and the escrow's half is `True` (`gateTr_none`). -/
theorem node.run.spec_of_gatedSpec (h : node.run.gatedSpec (GF := GF) (hG := hG)) :
    node.run.spec (GF := GF) (hG := hG) := by
  intro γ id n HtrG
  iintro %Φ ⟨#Hpkg, #Hnc, Hpre⟩ HΦ
  iapply (h γ id n (fun hne => absurd HtrG hne)) $$ [Hpre] [HΦ]
  · ihave Hg := gateTr_none (GF := GF) γ.raft.reTrace (rtkRun γ.esc none) HtrG
    iframe Hpkg Hnc Hpre Hg
  · iexact HΦ

/-! ## `RawNode.Advance`, both modes -/

/-- **`rn.Advance(rd)` in both modes** (step 4's `hAdv`; design §3.2's `advancec` row, §3.4 item 3):
`RawNode.Advance.spec` with its premise `γ.reTrace = none` replaced by, at a traced node, the bounds
`RawNode.acceptReady.spec` takes (the term ceiling's successor below the trace's bound, the receipts'
fit: each self-addressed response and acknowledgement it steps is a traced `raft.Step` whose numbers
are within the trace's bound) and no snapshot lent (`rs.slent = none`: no `MsgSnap` is stepped at a
traced node, so no `Ready` hands one out; `run` reads it off `TrNoSnap` and `LoanOk`, the lemma
`ownRawNode_trNoLoan` to write). The rest of the traced content is inside `ownRawNode` on both sides:
the capability and the clauses (`rnTrace`: 1(b)'s `TrScope` for the self `MsgAppResp`'s `lt` premise,
1(d)'s `c.autoLeave = false` for the apply acknowledgement's automatic leave, `TrNoSnap`), the
self-addressed responses' tokens (`pendingRel`'s `selfTok`), and at the end state the clauses
re-established (1(a) by the bundle's monotone flag, `delivered` unchanged without a loan). Lemma (ii)'s
`applied ≤ capplied` after is `ownStepGhost_applied_capplied` (implementation step 3's J2), with the
post's `ca = max rs.capplied rs.delivered.length` (N2) as today. Untraced it is today's statement
(`RawNode.Advance.spec_of_tracedSpec`). -/
abbrev RawNode.Advance.tracedSpec : Prop :=
  ∀ (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (rd : Ready),
  (rs.slent = none → rs.unpersisted = []) →
  rs.unst = false →
  -- (step 4) in place of `γ.reTrace = none`: at a traced node, `acceptReady`'s bounds and no loan
  (γ.reTrace ≠ none → uint.Z rs.tc + 1 < traceNumBound ∧ traceReadyFits GF γ ∧ rs.slent = none) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hrn" ∷ ownRawNode γ rn id rs ∗
      "Hret" ∷ loanRet rs ∗
      "#HA1" ∷ □ (⌜rs.slent = none⌝ -∗ undecFree γ rs.mode rs.delivered rs.capplied rs.delivered.length) ∗
      "#Hbw" ∷ durFrags γ id rs.bw }}
    (App (Val (rn @!! go.GoType.PointerType RawNode.ty @!! go!"Advance")) (Val #rd))
  {{ (t : w64) (ca : Nat), RET #();
      ownRawNode γ rn id (advRS rs t ca) ∗
      ⌜uint.Z rs.term ≤ uint.Z t ∧ uint.Z t ≤ uint.Z rs.term + 1⌝ ∗
      ⌜uint.Z t ≤ uint.Z rs.tc⌝ ∗
      ⌜(rs.slent = none → rs.capplied ≤ ca ∧ ca ≤ max rs.capplied rs.delivered.length) ∧
        (∀ l, rs.slent = some l → rs.mode.isDyn = true → ca = l.dlv.length) ∧
        (rs.mode = .static → ca = rs.capplied)⌝ ∗
      ⌜rs.slent = none → rs.mode.isDyn = true → ca = max rs.capplied rs.delivered.length⌝ }}

/-- **`RawNode.Advance.spec` is `RawNode.Advance.tracedSpec`'s instance**: untraced, the gated premise
is vacuous. -/
theorem RawNode.Advance.spec_of_tracedSpec (h : RawNode.Advance.tracedSpec (GF := GF) (hG := hG)) :
    RawNode.Advance.spec (GF := GF) (hG := hG) :=
  fun γ rn id rs rd Hunp Hunst HtrG => h γ rn id rs rd Hunp Hunst (fun hne => absurd HtrG hne)

/-! ## `raft.applyConfChange`, both modes -/

/-- **`r.applyConfChange(cc)` in both modes** (step 4's `hCC`; design §3.2's `confc` row, §3.4):
`raft.applyConfChange.spec` with its premise `s.gh.tr = none` replaced by, at a traced node:

- a follower (`s.role = .follower`): at the `confc` arm, from clause 1(c) (`role ≠ follower → |boot| ≤
  applied`), lemma (ii) (`applied ≤ capplied`, `ownStepGhost_applied_capplied`), `DynCCPreOp`'s
  `capplied ≤ k` and G3 (a) on the committed log handed out (`k < |boot|`); so `switchToConfig` neither
  commits nor sends and its one trace line is `traceConfChangeEvent`'s (`trCapB_hookGate_applyCC`);
- the change keeps the configuration (`c'.cfg = c`): the specification's `ApplySimpleConfChange`
  reapplies the log's configuration (`accSrv` at the voters, `toC_accSrv`), so raft must stay at it;
  the result is then simple, with no learner and `autoLeave = false` (clause 1(d) kept); **its source at
  the arm is missing** (the change applied is the client's recorded decision, not the entry's content:
  `notes/trace-check-design.md`, "Step 4", the `confc` table);
- the line's numbers: the bootstrap log committed (`ownStepGhost_bootCommit`), the commit index within
  the log (`ownRaftGhost_logOk`), the term, commit and last indices below the trace's bound
  (`ownStepGhost_traceBound`, the ceiling): `trCapB_hookGate_applyCC`'s `hboot`, `hcl`, `hbnd`;

and the capability, booted, idle at `s` (`trCapB`, `emp` untraced; clause 1(a) at the arm: the entry is
in the delivered log, so it is not empty) in, idle at the end state out (a follower's `ApplyCCOkC` keeps
`toPState`, `simIdle_congr`), at the configuration after. Untraced it is today's statement with `emp`
on both sides. -/
abbrev raft.applyConfChange.tracedSpec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (cc : Loc) (ccm : ConfChangeV2M) (dq : DFrac)
    (c' : CCState) (γ : RaftNames),
  ccApplyM ccm.transition ccm.changes (cfgStateC c) = some c' →
  (GMap.size c'.cfg.ids : Int) ≤ 2 ^ 62 →
  (s.role = .leader → s.term ≠ W64 0) →
  (s.role = .candidate ∨ s.role = .preCandidate → id ∈ c'.cfg.voters) →
  (s.gh.ns = true → s.role = .leader →
    2 ≤ plogLastIndexZ s.logst.prev (s.logst.sents ++ s.logst.uents)) →
  -- (step 4) in place of `s.gh.tr = none`: at a traced node, a follower whose change keeps its
  -- configuration, with the `ApplyConfChange` line's numbers
  (s.gh.tr ≠ none →
    s.role = .follower ∧ c'.cfg = c ∧
    (γ.reBoot.length : Int) ≤ uint.Z s.logst.committed ∧
    uint.Z s.logst.committed ≤ uint.Z (plastIndex (toPState s)) ∧
    uint.nat s.term < traceNumBound ∧ uint.nat s.logst.committed < traceNumBound ∧
    uint.nat (plastIndex (toPState s)) < traceNumBound) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
      "Hcc" ∷ ownConfChangeV2 cc dq ccm ∗
      "Hcap" ∷ trCapB s.gh.tr γ r id c true (fun C => SimIdle C s) }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"applyConfChange")) (Val #cc))
  {{ (cs : Loc) (xs os ls lns : List w64) (s' : NState), RET #cs;
      ownRaftPhysCV c'.cfg c'.cfg.voters r id s' ∗
      ownConfChangeV2 cc dq ccm ∗
      csPts cs (DFrac.own 1) (ConfStateM.mk xs ls os lns c'.cfg.autoLeave) true ∗
      ⌜xs ≡ₚ elements c'.cfg.incoming ∧ os ≡ₚ elements c'.cfg.outgoing ∧
        ls ≡ₚ elements c'.cfg.learners ∧ lns ≡ₚ elements c'.cfg.learnersNext⌝ ∗
      ⌜ApplyCCOkC c'.cfg id s s'⌝ ∗
      trCapB s.gh.tr γ r id c'.cfg true (fun C => SimIdle C s') }}

end spec

end EtcdGrove
end Perennial
