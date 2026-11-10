/-
Lean-first (no Rocq counterpart). **`raft.Step` on the capability: the statement** (2026-11-10, trace-check
Q8 stage 1 slice 13, `notes/decisions.md`, "Q8 stage 1 (slice 13)"). Not proved: a definition, the target
of piece 2 of the plan.

`raft.Step.spec` is one spec for both modes: the caller's resources `R` through the gates of the path
(`stepGates`) and the closing wand (`stepClose`), which since slice 13 learns the code's end state on the
types a traced node steps (`StepEnd`). An untraced caller supplies them from the struct's nil logger
(`stepBundle_none`, `TracedUntracedRaftStep.lean`). A traced caller supplies them from the capability
(`trCapB`) in the idle phase at the state the step starts in, and gets the capability back in the idle
phase at the state `Step` returns: that is **`stepBundle_traced.statement`** below, the traced
counterpart of `stepBundle_none`; with `raft.Step.spec` it gives `raft.Step`'s traced triple (the
capability in, `SimIdle C s`, and out, `SimIdle C s'`), as `raft.Step.untraced` follows from
`stepBundle_none`.

What only the node API can supply is premised: the received message's token (`recvTokOf`: its
specification message in flight, for a traced type), its numbers (`MsgTrOk`, from `isRaftMsg`), the
terms' bound (`termLB`'s, as a pure bound), the receipts' fit (`readyFits`', for
`ownRaftGhost_traceBound`); and the traced node's configuration (`TracedConfigOk`: pre-vote and
check-quorum off) and message types (`StepEndTy`).

**Slice 13's finding** (the broadcast paths not derivable while the gates' resources were not indexed
by the outbox) **is resolved by slice 14's indexing**; a traced caller's families are `trFam`
(`TracedFamilies.lean`). Proved path by path (`stepBundle_traced.on`, slice 15,
`TracedRaftStepPaths.lean`; the local paths that log lines, slice 18a, `TracedRaftStepLocal.lean`).
-/
module

public import Proof.go_etcd_io.raft.v3.TracedRecvGate
public import Proof.go_etcd_io.raft.v3.LemmasStepGates

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

section traced
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **The received message's token, traced** (the node API's, from the transport): for a message of a
traced type, its specification message (`msgAbs` at the cluster's voters) in flight under some token
`k` (`inFlight`, which the receive line consumes: `trCapB_hookGateRecv`); nothing for another type. -/
def recvTokOf (γd : GName) (m : MessageM) (ents : List EntryM) (ctx : List w8) : IProp GF :=
  iprop(∀ ty : MsgType, ⌜mtypeOf m.Type' = some ty ∧ ty.traced = true⌝ -∗
    ∃ (tn : TraceNames) (k : Nat) (ma : Etcdraft.Msg), traceDir γd tn ∗
      ⌜TraceSim.msgAbs tn.voters tn.voters.length (absMsg ty m ents ctx) = some ma⌝ ∗ inFlight tn k ma)

/-- (2026-11-10, slice 15) **The node's last event after `Step`**: the one before (`Λ`, no line logged) or
one of the step's lines. Until slice 15 the statement gave back `Λ` itself, which a path logging a line
cannot (the capability's `simBoot` records the line as the node's last event). -/
def stepLastEv (Λ : Option TraceEv → Prop) : Option TraceEv → Prop := fun o => Λ o ∨ o.isSome = true

/-- **`raft.Step`'s resources from the capability, on the paths `Path`** (the statement; see the
header): at a traced node (`s.gh.tr = some γd`) idle at `s`, on a message `m` whose path at `s` is
one of `Path`'s, the capability, the received message's token and the node's premises give, after an
update, resources `R` with `Step`'s gates for the message and the closing wand whose result is the
capability idle at the end state `s'` the wand is given. (2026-11-10, slice 15) Parameterized by the
paths so that the proofs come path by path (`stepBundle_traced.statement` is `Path := True`), and
three premises found needed (`notes/decisions.md`, "Q8 stage 1 (slice 15)"): a local message's term
is zero (a local message at a higher term steps the node down with no receive line before, a
`BecomeFollower` line the specification cannot take); `MsgHup` not at a leader (`hup`'s
`BecomeCandidate` gate, `hupGates`' `"Hgbc"`, is asked whatever the role, and a leader has no
`Timeout` step); the log never compacted (`TrNoSnap`, which `candidateGates`'/`leaderGates`'
`"#Hnosnap"` ask unguarded, from the Draft's P2); a traced message addressed to the node (the receive
line's event is the node's, `SendEvOf … m.dst`, and the specification delivers it to its
destination). And the node's last event after the step is `stepLastEv Λ`, not `Λ`. (2026-11-10, slice
18a, `notes/decisions.md`, "Q8 stage 1 (slice 18a)") No learners (`c.learners = ∅`) and the tracker's
peers within the configuration: a heartbeat's and an append's send line needs its destination a voter.
The log terms' bound the append and vote-request lines need (`blt`) is not a premise: raft's ghost state,
which the gates hand the caller's families, gives it (`ownRaftGhost_terms_le`). -/
abbrev stepBundle_traced.on (Path : NState → MessageM → Prop) : Prop :=
  ∀ (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64) (s : NState) (m : MessageM)
    (ents : List EntryM) (sn : Option SnapshotM) (ctx : List w8) (rs : List Loc) (γd : GName)
    (Λ : Option TraceEv → Prop),
  Path s m →
  s.gh.tr = some γd →
  -- a traced node's configuration (`TracedConfigOk`) and message types
  s.prevote = false → s.cq = false → StepEndTy m.Type' → NStateWf s →
  -- (slice 15) a local message (`tickElection`'s, `tickHeartbeat`'s, `Propose`'s) at term zero, and
  -- `MsgHup` stepped by a node that is not leading (`tickElection` is a non-leader's tick)
  (m.Type' = MsgHup ∨ m.Type' = MsgBeat ∨ m.Type' = MsgProp → m.Term' = W64 0) →
  (m.Type' = MsgHup → s.role ≠ .leader) →
  -- (slice 15) a traced message is the node's (rafthttp delivers a message to its `To`)
  (∀ ty, mtypeOf m.Type' = some ty → ty.traced = true → m.To' = id) →
  -- the numbers the lines read (`TraceEv.Ok`): the terms (`termLB`'s bound at the node API), the
  -- message's (`isRaftMsg`'s `MsgTrOk`), the receipts' fit (`readyFits`)
  uint.Z s.term + 1 < traceNumBound → uint.Z m.Term' < traceNumBound →
  (∀ ty, mtypeOf m.Type' = some ty → MsgTrOk γ (absMsg ty m ents ctx)) →
  receiptBound GF + γ.reBoot.length ≤ traceNumBound →
  -- (slice 18a) no learners at a traced node (the Draft's P3: a traced cluster's voters only), and the
  -- tracker's peers the configuration's (`ownRaftPhysC`'s, read off before the call): a heartbeat's
  -- or an append's destination is then a voter, as its send line needs
  c.learners = ∅ → domSet s.progress ⊆ c.voters ∪ c.learners →
  -- (slice 15) the log never compacted (P2): `TrNoSnap`, persistent
  (trCapB s.gh.tr γ r id c true (fun C => SimIdle C s) Λ ∗ recvTokOf γd m ents ctx ∗
      TrNoSnap s.gh.tr s.logst : IProp GF) ⊢
    |={⊤}=> ∃ R : StepG GF, R.G ∗ stepGates c r id s m ents sn ctx rs (ghostIn γ md c id s R) ∗
      stepClose γ md c id m ents ctx s R
        (fun s' => trCapB s.gh.tr γ r id c true (fun C => SimIdle C s') (stepLastEv Λ))

/-- **`raft.Step`'s resources from the capability** on every path (see `stepBundle_traced.on`). -/
abbrev stepBundle_traced.statement : Prop := stepBundle_traced.on (GF := GF) (hG := hG) (fun _ _ => True)

end traced

end EtcdGrove
end Perennial
