/-
Lean-first (no Rocq counterpart). Trace-check's S5, Draft (2026-11-09): the simulation's capability
on raft's hook paths, the global step's laws, and the hooks' traced statements
(`notes/trace-validation-sim.md`, "S5 Draft: the capability"; the plan's Q8; reviews
`notes/trace-validation-reviews/s5-r{1,2,3}.md`).

- `TraceFire tr tl E Q` (`TraceFireOpt`, `TraceFireN`; `traceFire_mono`): what a hook's caller gives
  the event builder, by the cluster's trace mode (`NGhost.tr`): untraced, a nil logger and `Q`;
  traced, the logger's contract and the atomic update appending any event `e` with `E e`, giving `Q`.
- The events: `NodeEvOf`, `SendEvOf`/`MsgEvOf`, `CCEvOf` (with their ASCII lemmas), the gates.
- `trCapB tr γ r id c b Φ Λ` (`trCap`: any `b`): the node's share in phase `Φ`, its `booted` flag `b`
  and last event (`Λ` of it), the logger's contract, the simulation's invariant (`simInv`, its
  specification state's facts `simFx`).
- A line's effect `LineEffect` (the pure lemmas `lineEffect_*`, `TraceSimMatch.lean`), the phase
  steps `PhaseStep`/`PhaseStepB`/`PhaseStepR`/`PhaseStepReady`/`PhaseStepBF`, the facts each line
  keeps `FxPres*` (the caller's, from its node's ghost).
- The laws (proved in `TracedHooksGlobal.lean`): `trCap_fire_any` (a line consuming no message;
  `trCap_fire`, `trCap_fire_booted` its two cases), `trCap_fire_recv`, `trCap_fire_ready`,
  `trCap_fire_boot`, `trCap_fire_bf`; `trCapB_cfg` re-keys the configuration.
- The traced hook statements (`X.tracedSpec`) and the first callers' (`raft.send`, `traceCommit`,
  `raft.maybeCommit`).

(Q13, 2026-11-09: the traced statements on the capability, `traceCommit`, `raft.maybeCommit` and
`raft.send`, take, traced, `TraceEv.Ok` of the events their line may log, the laws' amended premise;
`TracedCap.lean`'s header. `raft.maybeCommit.tracedSpec`'s last-event premise moved to the state at
the outcome, where Go logs the line, and its postcondition gives the outcome `maybeCommitOut`.)

(Q8 stage 1, 2026-11-09: everything above but the traced statements moved, verbatim, to
`TracedCap.lean`, which this file imports, so that the hook-path specs can state their traced case.)

(Amendment A1, 2026-11-09, the rest of Q13's re-freeze: `MsgEvOf` pins the traced message's
`rejectHint`, so `raft.send.tracedSpec`'s premise is dischargeable, `sendEvOf_ok`; the capability's
configuration is the voters' during a node's bootstrap, apart from raft's, `trCapB`'s docstring and
`trCapB_hookGate_bf`. No statement in this file changed.)

(Review round 1's "vacuous until Q8's logger clause lands" is resolved: `ownRaftPhys` carries
`TraceLoggerOkS s.gh.tr tl`, `InvRaftPhys.lean`, nil only untraced.)

Each `X.tracedSpec` is `X.spec` with the capability added (one spec per function: the untraced
instance, `s.gh.tr = none`, is `X.spec`'s, `trCap none … = emp`). **As `TracedApiDraft`:** a traced
statement replaces its `X.spec` only once proved; until then these are definitions, reviewed with
the rest of the Draft, and the existing specs stay as they are.
-/
module

public import Proof.go_etcd_io.raft.v3.TracedCap
public import Spec.go_etcd_io.raft.v3.raft__maybeCommit
public import Spec.go_etcd_io.raft.v3.traceCommit
public import Spec.go_etcd_io.raft.v3.traceNodeEvent
public import Spec.go_etcd_io.raft.v3.traceSendMessage
public import Spec.go_etcd_io.raft.v3.traceReceiveMessage
public import Spec.go_etcd_io.raft.v3.traceBecomeFollower
public import Spec.go_etcd_io.raft.v3.traceBecomeCandidate
public import Spec.go_etcd_io.raft.v3.traceBecomeLeader
public import Spec.go_etcd_io.raft.v3.traceReady
public import Spec.go_etcd_io.raft.v3.traceReplicate
public import Spec.go_etcd_io.raft.v3.raft__send

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3 TraceSim

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-! ## The `Commit` path, traced -/

/-- **`traceNodeEvent(evt, r)`, traced** (`traceNodeEvent.spec` with the gate): reads the logger;
nil, it returns, giving `Q`; otherwise it reads `r`'s state (`ownRaftPhysCV`, given back) to build
the event, a `NodeEvOf` one, and fires the caller's update with it. -/
abbrev traceNodeEvent.tracedSpec : Prop :=
  ∀ (evt : w64) (c : CfgM) (r : Loc) (id : w64) (s : NState) (tl : GoInterface) (Q : IProp GF),
  -- `evt.String()` panics past the event names (review round 1's F1)
  uint.nat evt < evtNames.length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ r.[raft, go!"traceLogger"] ↦□ tl ∗
      ownRaftPhysCV c c.voters r id s ∗ TraceFire s.gh.tr tl (NodeEvOf evt id s c) Q }}
    (App (App (Val #(functions traceNodeEvent [])) (Val #evt)) (Val #r))
  {{ RET #(); ownRaftPhysCV c c.voters r id s ∗ Q }}

/-- **`traceCommit(r)`, traced**: the `Commit` line, logged at the end of `maybeCommit` (its
`defer`), with raft's commit index already moved. The caller's phase: the node's server `a` is a
leader whose `AdvanceCommitIndex` commits exactly to `n`, and the server so committed is idle-related
to `s` (`SimIdle`): the line's step. After it, the share is idle-related to `s`. -/
abbrev traceCommit.tracedSpec : Prop :=
  ∀ (c : CfgM) (γ : RaftNames) (r : Loc) (id : w64) (s : NState) (b : Bool) (Λ Λ' : Option TraceEv → Prop),
  -- (review round 3's C2) the capability with its `booted` flag and last event, as the laws keep them
  (∀ e, NodeEvOf rsmCommit id s c e → Λ' (some e)) →
  -- (Q13) the line's event as the laws take it (traced: from the time receipts, `nodeEvOf_ok`)
  (s.gh.tr.isSome → ∀ e, NodeEvOf rsmCommit id s c e → TraceEv.Ok (elements c.incoming).length e) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhysCV c c.voters r id s ∗
      trCapB s.gh.tr γ r id c b (fun C cs P => ∃ (a : Etcdraft.Server) (n : Int),
        toC (confAbs C) a = cs ∧ a.state = Etcdraft.leader ∧ AdvancesTo a n ∧
        SimIdle C s (toC (confAbs C) { a with commitIndex := max a.commitIndex n }) P) Λ ∗
      -- (review round 2's A4) the facts the line keeps, the caller's (from its node's ghost)
      FxPresT s.gh.tr γ id (NodeEvOf rsmCommit id s c)
        (fun C cs P => ∃ (a : Etcdraft.Server) (n : Int),
          toC (confAbs C) a = cs ∧ a.state = Etcdraft.leader ∧ AdvancesTo a n ∧
          SimIdle C s (toC (confAbs C) { a with commitIndex := max a.commitIndex n }) P)
        (fun C => SimIdle C s) }}
    (App (Val #(functions traceCommit [])) (Val #r))
  {{ RET #(); ownRaftPhysCV c c.voters r id s ∗ trCapB s.gh.tr γ r id c true (fun C => SimIdle C s) Λ' }}

/-- **`r.maybeCommit()`, traced** (`raft.maybeCommit.spec` with the capability): at a leader whose
share is idle-related to its state, it commits as `raft.maybeCommit.spec` says and logs `Commit`,
the specification's `AdvanceCommitIndex` (exact: `Committed()`'s quorum index is `maxAgree`), after
which the share is idle-related to the new state. **Blocked** (review round 2's A4, round 3's C4):
the `Commit` line's `FxPres` needs `QuorumLogInv` at the leader's raised commit, which waits on the
acknowledgement-history copy of the vote table (`QuorumLogF` is a `simFx` clause until then). -/
abbrev raft.maybeCommit.tracedSpec : Prop :=
  ∀ (c : CfgM) (γ : RaftNames) (r : Loc) (id : w64) (s : NState) (b0 : Bool) (Λ Λ' : Option TraceEv → Prop),
  s.role = .leader →
  -- (Q13 review round 3's B) the line's event is of the state at the outcome (`defer traceCommit`,
  -- after the commit), as `raft.maybeCommit.traced` states it; until Q13 this was at `s`
  (∀ b N, maybeCommitOut c s b N → ∀ e, NodeEvOf rsmCommit id
    (if b then { s with logst := { s.logst with committed := N } } else s) c e → Λ' (some e)) →
  -- (Q13) the line's event as the laws take it
  (s.gh.tr.isSome → ∀ b N, maybeCommitOut c s b N → ∀ e, NodeEvOf rsmCommit id
    (if b then { s with logst := { s.logst with committed := N } } else s) c e →
      TraceEv.Ok (elements c.incoming).length e) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗ trCapB s.gh.tr γ r id c b0 (fun C => SimIdle C s) Λ }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"maybeCommit")) (Val #()))
  {{ (b : Bool) (N : w64), RET #b;
      -- (Q13 review round 4's N1) the outcome the premises quantify over
      ⌜maybeCommitOut c s b N⌝ ∗
      ownRaftPhysCV c c.voters r id
        (if b then { s with logst := { s.logst with committed := N } } else s) ∗
      ⌜b = true → CommitOkC c (toPState s) N⌝ ∗
      trCapB s.gh.tr γ r id c true (fun C =>
        SimIdle C (if b then { s with logst := { s.logst with committed := N } } else s)) Λ' }}

/-! ## The other hooks, traced -/

/-- **`traceSendMessage(r, m)`, traced**: reads the logger; for a traced type (`sendEvt`), reads
`r`'s state and the message (both given back) and fires the caller's update with a `SendEvOf`
event of the message as sent (`absMsg`: `send` has stamped `From` and `Term`); for another type
nothing. A snapshot is never traced in a traced cluster (P2). -/
abbrev traceSendMessage.tracedSpec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (ml : Loc) (dq : DFrac) (ms : MsgSt)
    (tl : GoInterface) (Q : IProp GF),
  (s.gh.tr.isSome → mtypeOf ms.msg.Type' ≠ some .snap) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ r.[raft, go!"traceLogger"] ↦□ tl ∗
      ownRaftPhysCV c c.voters r id s ∗ msgOwn ml dq ms ∗
      TraceFireOpt s.gh.tr tl (sendGate id s c ms) Q }}
    (App (App (Val #(functions traceSendMessage [])) (Val #r)) (Val #ml))
  {{ RET #(); ownRaftPhysCV c c.voters r id s ∗ msgOwn ml dq ms ∗ Q }}

/-- **`traceReceiveMessage(r, m)`, traced**: at `raft.Step`'s entry, before any handling: the
receipt's event (`recvEvt`), with `r`'s state as it is. -/
abbrev traceReceiveMessage.tracedSpec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (ml : Loc) (dq : DFrac) (ms : MsgSt)
    (tl : GoInterface) (Q : IProp GF),
  (s.gh.tr.isSome → mtypeOf ms.msg.Type' ≠ some .snap) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ r.[raft, go!"traceLogger"] ↦□ tl ∗
      ownRaftPhysCV c c.voters r id s ∗ msgOwn ml dq ms ∗
      TraceFireOpt s.gh.tr tl (recvGate id s c ms) Q }}
    (App (App (Val #(functions traceReceiveMessage [])) (Val #r)) (Val #ml))
  {{ RET #(); ownRaftPhysCV c c.voters r id s ∗ msgOwn ml dq ms ∗ Q }}

/-- **`traceBecomeFollower(r)`, traced**: a `BecomeFollower` node event of `r`'s state. -/
abbrev traceBecomeFollower.tracedSpec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (tl : GoInterface) (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ r.[raft, go!"traceLogger"] ↦□ tl ∗
      ownRaftPhysCV c c.voters r id s ∗ TraceFire s.gh.tr tl (NodeEvOf (W64 2) id s c) Q }}
    (App (Val #(functions traceBecomeFollower [])) (Val #r))
  {{ RET #(); ownRaftPhysCV c c.voters r id s ∗ Q }}

/-- **`traceBecomeCandidate(r)`, traced**. -/
abbrev traceBecomeCandidate.tracedSpec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (tl : GoInterface) (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ r.[raft, go!"traceLogger"] ↦□ tl ∗
      ownRaftPhysCV c c.voters r id s ∗ TraceFire s.gh.tr tl (NodeEvOf (W64 1) id s c) Q }}
    (App (Val #(functions traceBecomeCandidate [])) (Val #r))
  {{ RET #(); ownRaftPhysCV c c.voters r id s ∗ Q }}

/-- **`traceBecomeLeader(r)`, traced**. -/
abbrev traceBecomeLeader.tracedSpec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (tl : GoInterface) (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ r.[raft, go!"traceLogger"] ↦□ tl ∗
      ownRaftPhysCV c c.voters r id s ∗ TraceFire s.gh.tr tl (NodeEvOf (W64 3) id s c) Q }}
    (App (Val #(functions traceBecomeLeader [])) (Val #r))
  {{ RET #(); ownRaftPhysCV c c.voters r id s ∗ Q }}

/-- **`traceInitState(r)`, traced** (review round 3's B5): an `InitState` node event of `r`'s state.
Draft: `newRaft` calls it before raft's predicate holds (the struct built, its configuration empty,
before `confchange.Restore`), so its caller must assemble `ownRaftPhysCV` at the empty configuration
there (round 1's S5, open). The caller's gate comes from `trCap_fire_boot` at the capability's
configuration, the voters' (amendment A1), the event at raft's empty one (`nodeEvOf_okBoot` at the
voters' count). -/
abbrev traceInitState.tracedSpec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (tl : GoInterface) (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ r.[raft, go!"traceLogger"] ↦□ tl ∗
      ownRaftPhysCV c c.voters r id s ∗ TraceFire s.gh.tr tl (NodeEvOf (W64 0) id s c) Q }}
    (App (Val #(functions traceInitState [])) (Val #r))
  {{ RET #(); ownRaftPhysCV c c.voters r id s ∗ Q }}

/-- **`traceConfChangeEvent(cfg, r)`, traced** (review round 3's B5): at `switchToConfig`'s entry,
before `r.trk` is overwritten, an `ApplyConfChange` event of `r`'s state at its old configuration `c`,
with the new configuration `cn`'s voters (`cfg`'s, read through `ownConfigC`, given back). Draft:
`switchToConfig`'s callers hold the struct open (`Htrkf`, `Hback`); its traced statement must take
`ownRaftPhysCV c` closed at entry instead. -/
abbrev traceConfChangeEvent.tracedSpec : Prop :=
  ∀ (c cn : CfgM) (r : Loc) (id : w64) (s : NState) (cfgv : tracker.Config) (prsm : Loc)
    (prs : GMap w64 Loc) (pvs : GMap w64 Progress) (tl : GoInterface) (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ r.[raft, go!"traceLogger"] ↦□ tl ∗
      ownRaftPhysCV c c.voters r id s ∗ ownConfigC cn cfgv prsm prs pvs ∗
      TraceFire s.gh.tr tl (CCEvOf id s c cn) Q }}
    (App (App (Val #(functions traceConfChangeEvent [])) (Val #cfgv)) (Val #r))
  {{ RET #(); ownRaftPhysCV c c.voters r id s ∗ ownConfigC cn cfgv prsm prs pvs ∗ Q }}

/-- **`traceReady(r)`, traced**. -/
abbrev traceReady.tracedSpec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (tl : GoInterface) (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ r.[raft, go!"traceLogger"] ↦□ tl ∗
      ownRaftPhysCV c c.voters r id s ∗ TraceFire s.gh.tr tl (NodeEvOf (W64 8) id s c) Q }}
    (App (Val #(functions traceReady [])) (Val #r))
  {{ RET #(); ownRaftPhysCV c c.voters r id s ∗ Q }}

/-- **`traceReplicate(r, es...)`, traced**: one `Replicate` node event per normal entry of the batch,
of `r`'s state before the append (`appendEntry` traces first). -/
abbrev traceReplicate.tracedSpec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (es : GoSlice) (dq : DFrac) (ents : List EntryM)
    (tl : GoInterface) (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ entsPts es dq ents ∗
      r.[raft, go!"traceLogger"] ↦□ tl ∗ ownRaftPhysCV c c.voters r id s ∗
      TraceFireN s.gh.tr tl (NodeEvOf (W64 5) id s c) (normalCount ents) Q }}
    (App (App (Val #(functions traceReplicate [])) (Val #r)) (Val #es))
  {{ RET #(); entsPts es dq ents ∗ ownRaftPhysCV c c.voters r id s ∗ Q }}

/-! ## `send`, traced -/

/-- **`r.send(m)`, traced** (`raft.send.spec` with the capability): the message queued as
`raft.send.spec` says, then `traceSendMessage`: for a traced type, a line whose local effect takes the
caller's phase `Φ` to `Φ'` (`PhaseStep`, the message as sent, `out`'s); otherwise `Φ` kept. -/
abbrev raft.send.tracedSpec : Prop :=
  ∀ (c : CfgM) (γ : RaftNames) (r : Loc) (id : w64) (s : NState) (ml : Loc) (m : MessageM)
    (ents : List EntryM) (sn : Option SnapshotM) (ctx : List w8) (rs : List Loc)
    (out : List Msg) (Φ Φ' : List w64 → ServerC → List Etcdraft.Msg → Prop) (b : Bool)
    (Λ Λ' : Option TraceEv → Prop),
  (m.From' = W64 0 ∨ m.From' = id ∨ m.Type' = MsgReadIndex ∨ m.Type' = MsgTransferLeader) →
  SendOk id s m ents ctx out →
  SnapOut id s m sn out →
  (m.Type' = MsgApp → AppShape ⟨m, ents, sn, ctx, rs⟩) →
  rs = [] →
  (s.gh.tr.isSome → mtypeOf m.Type' ≠ some .snap) →
  (match (mtypeOf m.Type').bind sendEvt with
   | some evt => ∀ mm ∈ out, PhaseStep id c (SendEvOf evt id s c mm) Φ Φ'
   | none => ∀ C cs P, Φ C cs P → Φ' C cs P) →
  -- (review round 3's C2) a logged line's event is the capability's new last event
  (∀ evt, (mtypeOf m.Type').bind sendEvt = some evt → ∀ mm ∈ out, ∀ e, SendEvOf evt id s c mm e → Λ' (some e)) →
  -- (Q13) a logged line's event as the laws take it
  (s.gh.tr.isSome → ∀ evt, (mtypeOf m.Type').bind sendEvt = some evt → ∀ mm ∈ out, ∀ e,
    SendEvOf evt id s c mm e → TraceEv.Ok (elements c.incoming).length e) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
      "Hm" ∷ msgOwn ml (DFrac.own 1) ⟨m, ents, sn, ctx, rs⟩ ∗
      "#Hsrc" ∷ tsSrc s.gh.sn m.Type' sn ∗
      trCapB s.gh.tr γ r id c b Φ Λ ∗
      -- (review round 2's A4) the facts the send line keeps, the caller's
      (match (mtypeOf m.Type').bind sendEvt with
       | some evt => [∗list] mm ∈ out, FxPresT s.gh.tr γ id (SendEvOf evt id s c mm) Φ Φ'
       | none => iprop(True)) }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"send")) (Val #ml))
  {{ RET #(); ownRaftPhysCV c c.voters r id (sendMsgs s out) ∗
      -- a line logged: the node booted, its last event the line's; none: both unchanged
      (if ((mtypeOf m.Type').bind sendEvt).isSome && !out.isEmpty
       then trCapB s.gh.tr γ r id c true Φ' Λ' else trCapB s.gh.tr γ r id c b Φ' Λ) }}

end ghost

end EtcdGrove
end Perennial
