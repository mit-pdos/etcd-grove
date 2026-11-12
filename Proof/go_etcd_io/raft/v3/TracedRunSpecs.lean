/-
Lean-first (no Rocq counterpart). **Step 4 of the trace-check design (2026-11-12): the traced statements
the gated `node.run` was proved from** (`notes/trace-check-design.md`, "Step 4 (2026-11-12): the
statements"; `notes/decisions.md`, "Step 4: the traced Advance, applyConfChange and run statements").
Raft-internal (not on `etc/api/raft.txt`).

(2026-11-12, step 5) `node.run.gatedSpec` (with `RunTracedOk`) and `RawNode.Advance.tracedSpec` replaced
`node.run.spec` and `RawNode.Advance.spec` in their `Spec/` files in place, so one statement and one proof
each. What is left:

- `raft.applyConfChange.tracedSpec`: step 4's `hCC`, the capability form at a booted follower keeping its
  configuration: what `run`'s `confc` arm calls (`TracedNodeRun.lean`). Since step 5 an instance of the
  gate form `raft.applyConfChange.spec` (`raft.applyConfChange.tracedSpec_of_spec`,
  `TracedApplyConfChange.lean`).
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
