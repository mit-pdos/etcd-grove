/-
Port of `election_proof/inv_rawnode.v` (at 857d09190), reworked on 2026-10-09.

**Raft v3.7 (2026-10-16, stage R5 of the retarget, `notes/decisions.md`, "The node layer over
pointer messages").** Ported from the old proof's file. What changed: `Pending.applyAck` and
`RNState`'s logs are over `EntryM` (the rename); the hard and soft state records (`HardSt`,
`hsAbs`, `nodeHardstate`, `hardstateVal`, ...) are `InvRaftPhys.lean`'s (stage R4); the two
local acknowledgements are message records (`appendAckM`, `applyAckM : MessageM`; the entries
of an apply acknowledgement are its `MsgSt.ents`); a pending step's message is a pointer
`stepsOnAdvance` holds, **owned** (`msgIn l □ st`, which `Advance` hands to `raft.Step`), with
`pendingRel γ id st p` the pure record (`pendSt`) plus, for a self-addressed response, its
`isMessage`; `pendingOwn` is gone (the apply acknowledgement's `Entries` capacity is inside
`msgIn`); `SelfMsgOk`/`isRaftMsg` are on the message's state; `prevHardSt` is a pointer to a
read-only hard state (`hsRO`, never `nil`); the message types `RawNode.Step` takes
(`netStepTypes`, `NetMsgOk`, now over the message's state), `DynNoSnap`, `DynCCPreOp`/`DynCCPre`
and the records `RawNode.Propose`/`confChangeToMsg` build (`propEntryM`, `propMsgM`,
`ccEntryM`) moved here from the old specs (`RawNode__Step`, `RawNode__ApplyConfChange`,
`RawNode__Propose`), so that `InvNode.lean` and the specs share them.

**The `RawNode`, as its client sees it (2026-10-09)**

`ownRawNode γ rn id rs` is the one predicate for a `RawNode` (`rawnode.go`), and it is
**protocol-free**: its index `rs : RNState` is what the application sees -- the committed
log handed out so far (`delivered`), the entries handed out that it must still append to
storage (`unpersisted`), the local messages `Advance` will step (`steps`, opaque) and the
term. Inside are the struct, the `raft` it points to at some physical state `s`
(`ownRaftPhys`), the node's ghost state at some protocol state `ps` (`ownRaftGhost`,
`NStateRel s ps`), and the facts that tie `rs` to `s`: `isCommitted γ rs.delivered` with
`delivered` as long as `applying`, `rs.unpersisted = s.logst.unpersisted`, `StepsOk` for
the queue, and the term. The scope facts the specs took as premises until then are
conjuncts: the node is a voter of `γ.reCfg`, the configuration `ownRaftPhys` is about; no
snapshot is pending (handing one out is phase 2); synchronous storage writes; and (since
2026-10-17, `RNPv`; from 2026-10-10 pre-vote off) pre-vote off in the dynamic mode only, and
the term ceiling `rs.tc` (`NGhost.tc`): every queued message is of a term at most the node's or
the ceiling (`OutTermOk`), which `readyWithoutAccept` reports of the messages it hands out, and a
pre-candidate's next term is within it; the client raises it (`ownRawNode_raise_tc`) with the
budget before a step that may need more.

Until 2026-10-08 the predicate was `ownRawNode cfg rn id s rs`, indexed by the node's
`NState` and an `RNState` of the previous `SoftState`/`HardState` and the queue, with
the ghost state beside it in every spec; the specs exposed the protocol state
(`NStateRel`, `Step`, `ps.role`, `s.logst.applying`, ...). The previous `SoftState` and
`HardState` are now owned and unconstrained (`prevSoftSt` points to some `SoftState`,
read-only): no spec states them.

With synchronous storage writes `Ready`'s `acceptReady` queues the self-addressed
responses of `msgsAfterAppend`, a `MsgStorageAppendResp` and a `MsgStorageApplyResp`
into `stepsOnAdvance`, and `Advance` steps them. Until 2026-10-10 `Advance` was proved
only for a queue without self-addressed responses (the flag `RNState.advanceable`, which
no client could establish); now `pendingRel` records of each self-addressed response
what `Step`'s spec asks of it, as `ownRaftPhys` keeps it for `msgsAfterAppend`
(`AAMsgOk`, `InvRaftPhys.lean`), and `StepsOk` its term.

**The acknowledgement across a truncation (2026-10-10).** The queued
`MsgStorageAppendResp` acknowledges the last entry `e` of the log of the `Ready`, which
the storage holds once the application appended (`LogState.stored`). Any `Step` may come
between `Ready` and `Advance`; a `MsgApp` may truncate the log below `e` (lowering
`offsetInProgress`), and a later one, from a leader of a higher term that has `e`, may put
`e` back. The acknowledgement then hits, and is right: the log and `stored` both have
`e`, both have records (`logRecs`: `ownRaftGhost` keeps the log's, `ownRawNode` keeps
`stored`'s, `Hstrecs`), so by Log Matching `stored` is the log up to `e`
(`stored_agree`, `stableOk_of_stored`). So `StepsOk` asks only that `e` be the last
entry of `stored` (`PendingOk`), which no network step changes (`NetFrame` keeps `prev`
and `stored`), and `RawNode.Step` takes a `MsgApp` with a `Ready` outstanding. Until then
`PendingOk` asked `e.index < offsetInProgress`, which only the first truncation already
breaks. The log-side notions
`Ready`/`Advance` are proved with -- the next unstable entries, the committed entries to
apply, `acceptUnstable`, `stableTo` -- are pure functions of `LogState` in
`InvReadylog.lean`.

Lean notes: the Rocq records `hardstate.t`, `softstate.t`, `rnstate.t` and the
inductive `pending.t` are `HardSt`, `SoftSt`, `RNState`, `Pending` (`HardSt`/`SoftSt`
after the Go fields `prevHardSt`/`prevSoftSt`: `SoftState` is the Goose type of
`go_etcd_io.raft.v3`, opened here; they are the proofs' now, no spec mentions them); the
constructors `pending.self`, `pending.append_ack`, `pending.apply_ack` are
`Pending.self`, `.appendAck`, `.applyAck`. `hs_abs`, `node_hardstate`,
`node_softstate`, `hardstate_val`, `softstate_val`, `append_ack_msg`, `apply_ack_msg`,
`pending_rel`, `pending_own`, `own_RawNode` are `hsAbs`, `nodeHardstate`,
`nodeSoftstate`, `hardstateVal`, `softstateVal`, `appendAckMsg`, `applyAckMsg`,
`pendingRel`, `pendingOwn`, `ownRawNode`; the `EqDecision` instances are `deriving
DecidableEq`. (`hs_empty_abs`'s port `hsEmptyAbs` had no user and is gone, 2026-10-17.)
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.InvReadylog
-- (2026-10-14, reconfiguration stage B7 part 2) the ghost modes
public import RaftWitness.Proof.go_etcd_io.raft.v3.StepGhostMode
public import RaftWitness.Proof.go_etcd_io.raft.v3.SnapConf
-- (2026-10-16, stage R5) `StepMsg`, `RestMsgOk` for `NetMsgOk`; `ccV2Of` for `DynCCPre`
public import RaftWitness.Spec.go_etcd_io.raft.v3.raft__Step
public import RaftWitness.Proof.go_etcd_io.raft.v3.CCApply

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-! ## The RawNode's state -/

-- (2026-10-16, stage R5) `HardSt`, `SoftSt` are `InvRaftPhys.lean`'s (stage R4)

/-- A local message `acceptReady` queued for `Advance` to step:

- `self pv t`: a self-addressed response from `msgsAfterAppend` (a candidate's own vote,
  a pre-candidate's own pre-vote -- `pv` -- or a leader's own `MsgAppResp`) of term `t`
  (2026-10-10; until then `self a`, with the message's abstraction `a`);
- `appendAck t last`: `MsgStorageAppendResp` at term `t` acknowledging the log up to
  `last` (queued when there were unstable entries);
- `applyAck ents`: `MsgStorageApplyResp` carrying the committed entries handed out for
  applying. -/
inductive Pending [FfiSyntax] where
  | self (pv : Bool) (t : w64)
  | appendAck (term : w64) (last : entryID)
  | applyAck (ents : List EntryM)

/-- The mode of a `RawNode`'s ghost state (2026-10-14, reconfiguration stage B7 part 2): static
(the voters fixed at `γ.reCfg`, conf-change entries data) or dynamic (the configuration changes
by applied conf entries: a decoder `dec` and an initial configuration `c0`; B5's
`ownRaftGhostR`). -/
inductive RNMode [FfiSyntax] where
  | static
  | dyn (dec : CCDec) (c0 : CCState) (h0 : CfgOk c0) (h1 : CCGood c0)

/-- What the application sees of a `RawNode` (2026-10-09). -/
structure RNState [FfiSyntax] where
  /-- The committed log handed out so far, from the start (as `isCommitted` takes it):
  every `Ready`'s `CommittedEntries`, in order, after the entries applied before the
  node was built. -/
  delivered : List EntryM
  /-- The entries `Ready` handed out (`Ready.Entries`) that the application must still
  append to the `Storage` (and give the receipt back: `ownRawNode_appended`). -/
  unpersisted : List EntryM
  /-- `rn.stepsOnAdvance`: what `Advance` will step. Opaque to clients, which only
  learn that it is empty (after `Advance`), as `Ready` requires. (Until 2026-10-10 a
  flag `advanceable` said whether `Advance` was proved for it: not for a queue with a
  self-addressed response, which no client could rule out.) -/
  steps : List Pending
  /-- The node's current term (2026-10-09). A client sees it (`Status`, `Ready`'s
  `HardState`); the specs need it because Go panics when a campaign wraps it
  (`Campaign`, `Tick`, `Advance`), and say how a step moves it. -/
  term : w64
  /-- The `Storage` the node reads (`Config.Storage`), constant (2026-10-10): the right
  to append `Ready` hands out (`appendRight`) and the receipt `ownRawNode_appended` takes
  back are for this storage. -/
  storage : Storage
  /-- Lower bounds for `node.go` (2026-10-10): at most this many messages are queued
  (`NGhost.outlb`), ... -/
  outlb : Nat := 0
  /-- ... some unstable entry is still to be handed out (`NGhost.unst`), ... -/
  unst : Bool := false
  /-- ... and the commit index is at least this. A step keeps all three; `acceptReady`
  resets the first two. `node.go`'s `run` raises them when it abandons a computed `Ready`
  (`ownRawNodeReady_abandon`), so that, should `HasReady` later report nothing new, the
  abandoned `Ready` is known to hold nothing (`ownRawNodeIdle`). -/
  clb : w64 := W64 0
  /-- (2026-10-17, pre-vote on) the term ceiling (`NGhost.tc`): every message the node queues,
  and its term, are at most this. The node's budget covers it (`termLB`); the client raises it
  (`ownRawNode_raise_tc`) before a step that may send at a later term. -/
  tc : w64 := W64 0
  /-- The ghost state's mode (2026-10-14, reconfiguration stage B7 part 2), constant. -/
  mode : RNMode := .static
  /-- In the dynamic mode, the configuration in use (with the learner flags; `confchange`'s
  state) and its *configuration index*: the configuration is that of the committed log's
  first `capplied` entries -- every conf entry below has been applied with `ApplyConfChange`.
  Only `ApplyConfChange` (to the entry it applies, plus one) and `Advance` (to at most the
  committed log handed out, `delivered`, past no conf entry: A1) move them. Unconstrained in
  the static mode. -/
  cfg : CCState := ⟨CfgM.simple ∅ ∅, ∅⟩
  capplied : Nat := 0
  /-- (D19i part 1) The floor is raised past `applied` (`ownRawNode_raise_floor`): `node.go`
  raises it to `applying` when the application's `Advance` is handed over, and `Advance`, which
  follows at once, moves `applied` up to it and clears the flag. While it is set the node is not
  to campaign (`Campaign`, `Tick`, `Step` take it clear: `hasUnappliedConfChanges` reads from
  `applied + 1`). -/
  flw : Bool := false

section defs
variable [FfiSyntax]

def RNMode.isDyn : RNMode → Bool
  | .static => false
  | .dyn .. => true

/-- The ghost mode `raft.Step` keeps for a `RawNode` in mode `md`, with the ghost part `g`. -/
def RNMode.toG : RNMode → RGh → GMode
  | .static, _ => .static
  | .dyn dec c0 h0 _, g => .dyn dec c0 h0 g

theorem RNMode.toG_isDyn (md : RNMode) (g : RGh) : (md.toG g).isDyn = md.isDyn := by
  cases md <;> rfl

/-- The voters the node's quorums are taken in, as the client sees them: `γ.reCfg` in the
static mode, the configuration in use in the dynamic one. -/
def RNState.vcfg (γ : RaftNames) (rs : RNState) : CfgM :=
  match rs.mode with
  | .static => CfgM.simple γ.reCfg ∅
  | .dyn .. => rs.cfg.cfg

/-- No conf entry in a range of a prefix is none in the longer log. -/
theorem NoConfIn_prefix {D F : List EntryM} {lo hi : Nat} (hp : D <+: F)
    (hhi : hi ≤ D.length) (h : NoConfIn D lo hi) : NoConfIn F lo hi := by
  intro k e hk1 hk2 he
  apply h k e hk1 hk2
  obtain ⟨t, rfl⟩ := hp
  rw [List.getElem?_append_left (by omega)] at he
  exact he

/-- A step in the mode of a `RawNode` (`RNMode.toG`), with the configuration index `ca`: the
mode afterwards is the node's at some `ca'`, moved only by a `MsgStorageApplyResp`, to at
most the new `applied` (`CidxMove`), and not at all in the static mode. -/
theorem RNMode.stepOut_ca {mode : RNMode} {ca : Nat} {cfg : CCState} {fp : List EntryM}
    {c : CfgM} {id : w64} {m : MessageM} {s s' : NState} {md' : GMode}
    (H : (mode.toG ⟨ca, cfg, fp⟩).StepOut c id m s s' md') (hs : m.Type' ≠ MsgSnap) :
    ∃ ca', md' = mode.toG ⟨ca', cfg, fp⟩ ∧ ca ≤ ca' ∧
      ca' ≤ max ca (uint.nat s'.logst.applied) ∧ (mode = .static → ca' = ca) ∧
      (m.Type' ≠ MsgStorageApplyResp → ca' = ca) := by
  cases mode with
  | static =>
    exact ⟨ca, H.1, Nat.le_refl _, Nat.le_max_left _ _, fun _ => rfl, fun _ => rfl⟩
  | dyn dec c0 h0 _ =>
    obtain ⟨g', Hcm, rfl, -⟩ := H
    rcases Hcm with h | h | ⟨hty, h⟩
    · exact absurd h hs
    · subst h
      exact ⟨ca, rfl, Nat.le_refl _, Nat.le_max_left _ _, fun h => (by cases h), fun _ => rfl⟩
    · subst h
      exact ⟨_, rfl, Nat.le_max_left _ _, Nat.le_refl _, fun h => (by cases h),
        fun hm => absurd hty hm⟩


-- (2026-10-16, stage R5) `hsAbs`, `nodeHardstate`, `nodeSoftstate`,
-- `hardstateVal`, `softstateVal` are `InvRaftPhys.lean`'s (stage R4)

/-- The two local messages, as `newStorageAppendRespMsg` and `newStorageApplyRespMsg`
build them (with synchronous writes and no pending snapshot). (2026-10-16, stage R5: the
message's scalars, `MessageM`; until then the Goose values `appendAckMsg`, `applyAckMsg sl`.
The apply acknowledgement's entries are its state's `ents`, `pendSt`.) -/
def appendAckM (id t : w64) (e : entryID) : MessageM :=
  MessageM.mk MsgStorageAppendResp id LocalAppendThread t e.term' e.index' (W64 0) (W64 0) false
    (W64 0)

def applyAckM (id : w64) : MessageM :=
  MessageM.mk MsgStorageApplyResp id LocalApplyThread (W64 0) (W64 0) (W64 0) (W64 0) (W64 0) false
    (W64 0)

/-- A self-addressed response as `Advance` steps it (2026-10-10): what `Step`'s spec asks
of a `MsgVoteResp`, `MsgPreVoteResp` or `MsgAppResp` to the node itself, beyond its
term's bound (`PendingOk`) -- from and to the node, a nonzero term, no entries and no
context (`nil`), and a `MsgAppResp` that does not reject. `AAMsgOk` (`InvRaftPhys.lean`)
of a self-addressed message of `msgsAfterAppend`, without the term bound. (2026-10-16, stage
R5: on the message's state; "no entries and no context" is `st.ents = []`, `st.ctx = []`.) -/
def SelfMsgOk (id : w64) (st : MsgSt) : Prop :=
  (st.msg.Type' = MsgAppResp ∨ st.msg.Type' = MsgVoteResp ∨ st.msg.Type' = MsgPreVoteResp) ∧
  st.msg.From' = id ∧ st.msg.To' = id ∧ st.msg.Term' ≠ W64 0 ∧ st.ents = [] ∧
  st.ctx = [] ∧ (st.msg.Type' = MsgAppResp → st.msg.Reject' = false)

/-- A self-addressed message of `msgsAfterAppend` is `SelfMsgOk` (2026-10-16, stage R5). -/
theorem AAMsgOk.selfMsgOk {id t : w64} {st : MsgSt} (H : AAMsgOk id t st)
    (Hto : st.msg.To' = id) : SelfMsgOk id st := by
  obtain ⟨Hty, Hfr, Hself⟩ := H
  obtain ⟨H1, H2, H3, H4, -⟩ := Hself Hto
  exact ⟨Hty, Hfr, Hto, H1, H2, H3, H4⟩

/-- The pending step `acceptReady` queues for a self-addressed message. -/
def selfPending (m : MessageM) : Pending :=
  .self (decide (m.Type' = MsgPreVoteResp)) m.Term'

/-- The message state of a pending step (2026-10-16, stage R5): `st` is the message
`acceptReady` queued for `p` -- a self-addressed response `SelfMsgOk` of the term and type
`p` records; or exactly the acknowledgement `newStorageAppendRespMsg`/`newStorageApplyRespMsg`
builds (no snapshot, context or responses; the apply acknowledgement's entries the committed
entries handed out). -/
def pendSt (id : w64) (st : MsgSt) : Pending → Prop
  | .self pv t => SelfMsgOk id st ∧ st.msg.Term' = t ∧ pv = decide (st.msg.Type' = MsgPreVoteResp)
  | .appendAck t e => st = ⟨appendAckM id t e, [], none, [], []⟩
  | .applyAck ce => st = ⟨applyAckM id, ce, none, [], []⟩

/-! ## The queue `Advance` is proved for

What `Advance` needs of the queue it steps, at the state `s` it is called in, stated so
that `Ready` establishes it and a `Propose`, `Step`, `Tick` or `Campaign` in between
keeps it (`stepsOk_mono_le`). -/

/-- A queued `MsgStorageApplyResp`: its entries end at or below `committed` (`Step`'s
premise, `appliedTo`'s guard) and at or below `applying` (so that its `appliedTo` does
not move `applying`, to which `RNState.delivered` is tied). -/
def ApplyAckOk (s : NState) (p : Pending) : Prop :=
  match p with
  | .applyAck ce => ∀ e, ce.getLast? = some e →
      uint.Z e.Index' ≤ uint.Z s.logst.committed ∧ uint.Z e.Index' ≤ uint.Z s.logst.applying
  | _ => False

/-- One queued message, steppable at `s`: a self-addressed response not from a later
term than `s`'s -- one later for a pre-vote response, which a pre-campaign sends at the
next term -- (2026-10-10; what else `Step` asks of it is `pendingRel`'s); a
`MsgStorageAppendResp` not from a later term that acknowledges the last entry of what
the storage holds (`stored`, 2026-10-10: the log of the `Ready` that queued it); or an
`ApplyAckOk` `MsgStorageApplyResp`. The acknowledgement's `StableOk` is not a fact of
`s` alone: with the records of `stored` (`ownRawNode`'s `Hstrecs`) and of the log
(`ownRaftGhost`), Log Matching gives it whenever the acknowledgement hits
(`stableOk_of_stored`). Until 2026-10-10 the second fact was `e.index < offsetInProgress`
(with nothing unpersisted and no snapshot pending, `StableOk` outright), which a
truncating `MsgApp` breaks, so `RawNode.Step` took a `MsgApp` only with an empty queue. -/
def PendingOk (s : NState) (p : Pending) : Prop :=
  match p with
  | .self pv t => uint.Z t ≤ uint.Z s.term + (if pv then 1 else 0) ∧
      -- (2026-10-17; 2026-10-10 to 2026-10-17: with pre-vote off, not a pre-vote response) a
      -- pre-vote response within the term ceiling (`OutTermOk`)
      (pv = true → uint.Z t ≤ uint.Z s.gh.tc)
  | .appendAck t e => uint.Z t ≤ uint.Z s.term ∧ plogLast s.logst.prev s.logst.stored = e
  | .applyAck _ => ApplyAckOk s p

/-- The queue, in `acceptReady`'s order: the self-addressed responses (2026-10-10), then
the `MsgStorageAppendResp`, if any, then `ApplyAckOk` ones. Until 2026-10-09
`AdvanceOk`, a premise of `Advance`'s spec; until 2026-10-10 without self-addressed
responses (`RNState.advanceable`). It is stated on `s`'s term, `committed`, `applying`,
`prev` and `stored` only (`stepsOk_mono_le`), so that any step keeps it -- since
2026-10-10 a truncating `MsgApp`'s too (`PendingOk`). -/
def StepsOk (s : NState) : List Pending → Prop
  | [] => True
  | .self pv t :: rest => PendingOk s (.self pv t) ∧ StepsOk s rest
  | .appendAck t e :: rest => PendingOk s (.appendAck t e) ∧ ∀ p ∈ rest, ApplyAckOk s p
  | .applyAck ce :: rest => ∀ p ∈ Pending.applyAck ce :: rest, ApplyAckOk s p

theorem applyAckOk_mono (s s' : NState) (p : Pending)
    (Hc : uint.Z s.logst.committed ≤ uint.Z s'.logst.committed)
    (Ha : s'.logst.applying = s.logst.applying) :
    ApplyAckOk s p → ApplyAckOk s' p := by
  cases p with
  | applyAck ce =>
    intro H e He
    have := H e He
    rw [Ha]
    omega
  | _ => intro H; exact H

/-- A queue of `MsgStorageApplyResp`s only. -/
theorem stepsOk_of_applyAcks (s : NState) (l : List Pending)
    (H : ∀ p ∈ l, ApplyAckOk s p) : StepsOk s l := by
  match l, H with
  | [], _ => trivial
  | .self _ _ :: _, H => exact (H _ List.mem_cons_self).elim
  | .appendAck _ _ :: _, H => exact (H _ List.mem_cons_self).elim
  | .applyAck _ :: _, H => exact H

/-- `StepsOk` survives a step that moves the term up (a campaign, a message of a higher
term: `TermStep`), keeps `applying`, `prev` and `stored` (`NetFrame`, `LocalFrame`) and
does not move `committed` back: a queued `MsgStorageAppendResp` of an older term is still
not from a later one, and a queued self-addressed response neither. (Until 2026-10-10 it
also asked that `offsetInProgress` not move back, which a truncating `MsgApp` does.) -/
theorem stepsOk_mono_le (s s' : NState) (steps : List Pending)
    (Ht : uint.Z s.term ≤ uint.Z s'.term)
    (Hst : s'.logst.prev = s.logst.prev ∧ s'.logst.stored = s.logst.stored)
    (Hc : uint.Z s.logst.committed ≤ uint.Z s'.logst.committed)
    (Ha : s'.logst.applying = s.logst.applying)
    (Htc : uint.Z s.gh.tc ≤ uint.Z s'.gh.tc) :
    StepsOk s steps → StepsOk s' steps := by
  have Hall : ∀ l : List Pending, (∀ p ∈ l, ApplyAckOk s p) → ∀ p ∈ l, ApplyAckOk s' p :=
    fun l H p Hp => applyAckOk_mono s s' p Hc Ha (H p Hp)
  induction steps with
  | nil => intro _; trivial
  | cons p rest IH =>
    cases p with
    | self pv t =>
      intro ⟨⟨H1, H1'⟩, H2⟩
      exact ⟨⟨by omega, fun h => Int.le_trans (H1' h) Htc⟩, IH H2⟩
    | appendAck t e =>
      intro ⟨⟨H1, H2⟩, Hr⟩
      refine ⟨⟨by omega, ?_⟩, Hall rest Hr⟩
      rw [Hst.1, Hst.2]; exact H2
    | applyAck ce =>
      intro H; exact Hall _ H

/-- `StepsOk` survives a step that keeps the term, `applying`, `prev` and `stored` and
does not move `committed` back -- a `Propose`'s (`LocalStepOk`, `Step.commit_mono`), or
the application's append (`ownRawNode_appended`). -/
theorem stepsOk_mono (s s' : NState) (steps : List Pending)
    (Ht : s'.term = s.term)
    (Hst : s'.logst.prev = s.logst.prev ∧ s'.logst.stored = s.logst.stored)
    (Hc : uint.Z s.logst.committed ≤ uint.Z s'.logst.committed)
    (Ha : s'.logst.applying = s.logst.applying)
    (Htc : uint.Z s.gh.tc ≤ uint.Z s'.gh.tc) :
    StepsOk s steps → StepsOk s' steps :=
  stepsOk_mono_le s s' steps (by rw [Ht]; exact Int.le_refl _) Hst Hc Ha Htc

/-- (2026-10-17) The term ceiling of a step that keeps the ghost state (`stepsOk_mono_le`). -/
theorem tc_le_of_gh {s s' : NState} (h : s'.gh = s.gh) : uint.Z s.gh.tc ≤ uint.Z s'.gh.tc := by
  simp [h]

/-- What the storage holds agrees with the log up to an entry both have (2026-10-10):
Log Matching between two logs with records (`RecsAgree`, `logRecs_agree`), one of
which -- `L`, the log of the last `Ready`, which the storage holds -- ends at `e`. This
is why an acknowledgement of `e` that hits (`StableHit`: the log has `e.term` at
`e.index`) moves stable only entries the storage has, even after `MsgApp`s truncated
the log below `e` and put `e` back. -/
theorem stored_agree (b : entryID) (L F : List EntryM) (e : entryID)
    (HL : PlogWf b L) (HF : PlogWf b F) (HRA : RecsAgree b L b F)
    (Hlast : plogLast b L = e) (Ht : plogTermAt b F e.index' = some e.term') :
    L = F.take (uint.Z e.index' - uint.Z b.index').toNat := by
  have Hli := plogLast_index b L HL
  rw [Hlast] at Hli
  unfold plogLastIndexZ at Hli
  have Hn : (uint.Z e.index' - uint.Z b.index').toNat = L.length := by omega
  rw [Hn]
  have HtL : plogTermAt b L e.index' = some e.term' := by
    cases Hl : L.getLast? with
    | none =>
      have HL0 : L = [] := List.getLast?_eq_none_iff.mp Hl
      subst HL0
      simp only [plogLast, List.getLast?_nil] at Hlast
      subst Hlast
      exact plogTermAt_base _ _
    | some x =>
      have Hk := getLast?_some_getElem? L x Hl
      have He : e = entId x := by rw [← Hlast]; simp [plogLast, Hl]
      subst He
      have Hx := HL _ _ Hk
      have Hpos : 0 < L.length := by
        cases L with
        | nil => simp at Hl
        | cons _ _ => simp
      exact plogTermAt_lookup b L _ _ x Hk (by simp only [entId]; push_cast at Hx ⊢; omega)
  have Hm := plog_match_down b L b F e.index' (PlogWf_wfR _ _ HL) (PlogWf_wfR _ _ HF) HRA
    (by rw [HtL]; rfl) (by rw [HtL, Ht])
  apply List.ext_getElem?
  intro k
  by_cases hk : k < L.length
  · obtain ⟨y, Hy⟩ : ∃ y, L[k]? = some y := ⟨_, List.getElem?_eq_getElem hk⟩
    have Hyi := HL k y Hy
    push_cast at Hyi
    have := uint_Z_lt e.index'
    have Hj := Hm y.Index' (by omega) (by omega) (by omega)
    rw [plogTermAt_lookup b L _ k y Hy (by push_cast; omega)] at Hj
    obtain ⟨z, Hz, Hzi, Hzt⟩ := plogTermAt_some_entry b F _ _ (PlogWf_wfR _ _ HF) Hj.symm
      (by omega)
    have Hkz : (uint.Z y.Index' - uint.Z b.index' - 1).toNat = k := by omega
    rw [Hkz] at Hz
    obtain ⟨Hyz, -⟩ := HRA k k y z Hy Hz (by omega) (by omega) Hzt.symm Hzi.symm
    rw [Hy, List.getElem?_take_of_lt hk, Hz, Hyz]
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]

/-- The head of a `StepsOk` queue is steppable now, and the rest is `StepsOk`. -/
theorem stepsOk_cons (s : NState) (p : Pending) (rest : List Pending) :
    StepsOk s (p :: rest) → PendingOk s p ∧ StepsOk s rest := by
  cases p with
  | self pv t => exact id
  | appendAck t e =>
    intro ⟨Hh, Hr⟩
    exact ⟨Hh, stepsOk_of_applyAcks s rest Hr⟩
  | applyAck ce =>
    intro H
    exact ⟨H _ List.mem_cons_self,
      stepsOk_of_applyAcks s rest (fun q Hq => H q (List.mem_cons_of_mem _ Hq))⟩

/-- After a storage acknowledgement, the queue holds no self-addressed response. -/
theorem stepsOk_ack_noself (s : NState) (p : Pending) (rest : List Pending)
    (Hp : ∀ pv t, p ≠ .self pv t) :
    StepsOk s (p :: rest) → ∀ pv t, Pending.self pv t ∉ rest := by
  cases p with
  | self pv t => exact absurd rfl (Hp pv t)
  | appendAck t e =>
    intro ⟨_, Hr⟩ pv t' Hm
    exact Hr _ Hm
  | applyAck ce =>
    intro H pv t' Hm
    exact H _ (List.mem_cons_of_mem _ Hm)


/-! ## The messages of the `RawNode`/`node` API (2026-10-16, stage R5)

Moved here from the old specs (`RawNode__Step.lean`, `RawNode__ApplyConfChange.lean`,
`RawNode__Propose.lean`, `node`'s): `InvNode.lean` and the specs share them. -/

/-- The message types `RawNode.Step` is specified for: replication, leader election,
(2026-10-13) read-index, leader transfer and the local reports. -/
def netStepTypes : List w32 :=
  [MsgApp, MsgAppResp, MsgVote, MsgVoteResp, MsgHeartbeat, MsgHeartbeatResp,
   MsgReadIndex, MsgReadIndexResp, MsgTimeoutNow, MsgTransferLeader, MsgForgetLeader,
   MsgUnreachable, MsgSnapStatus,
   -- (2026-10-17) pre-vote
   MsgPreVote, MsgPreVoteResp]

/-- (2026-10-13) The types of `netStepTypes` that come unstamped (`Term = 0`): a read-index
request (forwarded or local), `TransferLeadership`'s request, and the local reports. -/
def UnstampedType (t : w32) : Prop :=
  t = MsgReadIndex ∨ t = MsgTransferLeader ∨ t = MsgForgetLeader ∨ t = MsgUnreachable ∨
    t = MsgSnapStatus

/-- A message from the network, as the transport and the peers deliver it to node `id`
(see `RawNode__Step.lean`'s header): but for the unstamped types (`Term = 0`, 2026-10-13),
addressed to `id`, of a nonzero term, from a nonzero sender; a transfer request with no
entries and no context. (2026-10-16, stage R5: on the message's state, the last clause over its
entries and context, `st.ents = [] ∧ st.ctx = []`; until then over the Goose value, `Entries' =
slice.nil ∧ Context' = slice.nil`.) -/
def NetMsgOk (id : w64) (st : MsgSt) : Prop :=
  st.msg.Type' ∈ netStepTypes ∧
  (¬ UnstampedType st.msg.Type' → st.msg.To' = id ∧ st.msg.Term' ≠ W64 0 ∧ st.msg.From' ≠ W64 0) ∧
  (UnstampedType st.msg.Type' → st.msg.Term' = W64 0) ∧
  (st.msg.Type' = MsgApp ∨ st.msg.Type' = MsgHeartbeat ∨ st.msg.Type' = MsgHeartbeatResp ∨
     st.msg.Type' = MsgReadIndexResp → st.msg.From' ≠ id) ∧
  (st.msg.Type' = MsgAppResp → st.msg.Reject' = true → st.msg.From' ≠ id) ∧
  (st.msg.Type' = MsgTransferLeader → st.ents = [] ∧ st.ctx = []) ∧
  -- (2026-10-17) a pre-vote request from another node
  (st.msg.Type' = MsgPreVote → st.msg.From' ≠ id)

omit [FfiSyntax] in
theorem netStepTypes_nonneg {t : w32} (h : t ∈ netStepTypes) : 0 ≤ sint.Z t := by
  simp only [netStepTypes, List.mem_cons, List.not_mem_nil, _root_.or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> decide

omit [FfiSyntax] in
theorem netStepTypes_ne_prop {t : w32} (h : t ∈ netStepTypes) : t ≠ MsgProp := by
  intro he
  rw [he] at h
  simp [netStepTypes, MsgProp, MsgApp, MsgAppResp, MsgVote, MsgVoteResp, MsgHeartbeat,
    MsgHeartbeatResp, MsgReadIndex, MsgReadIndexResp, MsgTimeoutNow, MsgTransferLeader,
    MsgForgetLeader, MsgUnreachable, MsgSnapStatus, MsgPreVote, MsgPreVoteResp] at h

theorem netStepTypes_stepMsg {m : MessageM} (h : m.Type' ∈ netStepTypes) : StepMsg m := by
  simp only [StepMsg, stepMsgTypes]
  simp only [netStepTypes, List.mem_cons, List.not_mem_nil, _root_.or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> simp [h]


/-! ### What a sender in the no-snapshot mode promises the receiver (2026-10-19, D21 M2r)

A message a `Ready` hands out in the cluster's no-snapshot mode is `SentMsgOk` (`isRaftMsg`'s
clause, `InvRaftPhys.lean`): at the node it is addressed to, every clause of `NetMsgOk` but for a
forwarded proposal, which `node.Step` takes as `fwdP` (D21g (A)). -/

theorem SentMsgOk.ne_snap {st : MsgSt} (H : SentMsgOk st) : st.msg.Type' ≠ MsgSnap := by
  intro h; have := H.1; rw [h] at this
  simp [sentTypes, MsgSnap, MsgProp, MsgApp, MsgAppResp, MsgVote, MsgVoteResp, MsgHeartbeat,
    MsgHeartbeatResp, MsgReadIndex, MsgReadIndexResp, MsgPreVote, MsgPreVoteResp, MsgTimeoutNow,
    MsgTransferLeader] at this

theorem SentMsgOk.ne_timeoutNow {st : MsgSt} (H : SentMsgOk st) :
    st.msg.Type' ≠ MsgTimeoutNow := by
  intro h; have := H.1; rw [h] at this
  simp [sentTypes, MsgSnap, MsgProp, MsgApp, MsgAppResp, MsgVote, MsgVoteResp, MsgHeartbeat,
    MsgHeartbeatResp, MsgReadIndex, MsgReadIndexResp, MsgPreVote, MsgPreVoteResp, MsgTimeoutNow,
    MsgTransferLeader] at this

theorem SentMsgOk.ne_transferLeader {st : MsgSt} (H : SentMsgOk st) :
    st.msg.Type' ≠ MsgTransferLeader := by
  intro h; have := H.1; rw [h] at this
  simp [sentTypes, MsgSnap, MsgProp, MsgApp, MsgAppResp, MsgVote, MsgVoteResp, MsgHeartbeat,
    MsgHeartbeatResp, MsgReadIndex, MsgReadIndexResp, MsgPreVote, MsgPreVoteResp, MsgTimeoutNow,
    MsgTransferLeader] at this

/-- **`NetMsgOk` of a sent message at its destination** (D21g (A)): what `node.Step`'s `netP`
takes of a message from the network, from the sender's `SentMsgOk` and the transport's delivery to
the node it is addressed to; but for a forwarded proposal (`fwdP`). -/
theorem NetMsgOk.of_sent {dst : w64} {st : MsgSt} (H : SentMsgOk st) (Hto : st.msg.To' = dst)
    (Hnp : st.msg.Type' ≠ MsgProp) : NetMsgOk dst st := by
  obtain ⟨Hty, Hf0, Ht0, Ht1, Hft⟩ := H
  subst Hto
  unfold NetMsgOk UnstampedType
  simp only [sentTypes, List.mem_cons, List.not_mem_nil, _root_.or_false] at Hty
  rcases Hty with h | h | h | h | h | h | h | h | h | h | h <;> rw [h] at Ht0 Ht1 Hft Hnp ⊢ <;>
    simp only [netStepTypes, MsgProp, MsgApp, MsgAppResp, MsgVote, MsgVoteResp, MsgHeartbeat,
      MsgHeartbeatResp, MsgReadIndex, MsgReadIndexResp, MsgPreVote, MsgPreVoteResp, MsgTimeoutNow,
      MsgTransferLeader, MsgForgetLeader, MsgUnreachable, MsgSnapStatus] at Ht0 Ht1 Hft Hnp ⊢ <;>
    simp_all

/-- What `raft.Step` takes of the types it was extended to last (`RestMsgOk`), from
`NetMsgOk` and the bound on the terms of a `MsgTimeoutNow`. -/
theorem NetMsgOk.restMsgOk {id : w64} {s : NState} {st : MsgSt}
    (h : NetMsgOk id st)
    (ht : st.msg.Type' = MsgTimeoutNow →
      uint.Z s.term + 1 < 2 ^ 64 ∧ uint.Z st.msg.Term' + 1 < 2 ^ 64 ∧
      uint.Z s.logst.fl ≤ uint.Z s.logst.applied)
    -- (2026-10-19, D21 M2r) a transfer request only with leader transfer on
    (hx : st.msg.Type' = MsgTransferLeader → s.gh.xf = false) :
    RestMsgOk s st.msg st.ents st.ctx := by
  obtain ⟨-, -, Hun, -, -, Htl, -⟩ := h
  refine ⟨fun h' => Hun ?_, ht, fun h' => ⟨(Htl h').1, (Htl h').2, fun hz => ?_, hx h'⟩⟩
  · rcases h' with h' | h' | h'
    · exact .inr (.inr (.inl h'))
    · exact .inr (.inr (.inr (.inl h')))
    · exact .inr (.inr (.inr (.inr h')))
  · exact absurd (Hun (.inr (.inl h'))) hz

/-- (2026-10-14, stage B7 part 2) The dynamic mode takes no snapshot message (stage B8).
(2026-10-16, stage R5: on the message's scalars.) -/
def DynNoSnap (rs : RNState) (m : MessageM) : Prop :=
  rs.mode.isDyn = true → m.Type' ≠ MsgSnap

/-- `DynCCPre` (below) on its components (2026-10-15, stage N): the committed log handed out
`D`, the configuration index `ca` and configuration `cfg`, and the change as `AsV2` makes it
(`op`); what `node.go`'s `confc` arm checks against the run loop's `RawNode` from what the
driver knows. -/
def DynCCPreOp (dec : CCDec) (D : List EntryM) (ca : Nat) (cfg : CCState) (op : CCOp)
    (k : Nat) (e : EntryM) (cs' : CCState) : Prop :=
  ca ≤ k ∧ k < D.length ∧ D[k]? = some e ∧ IsConfEnt e ∧
  NoConfIn D ca k ∧ dec (D.take k) e = some op ∧
  ccStepB op cfg = some cs' ∧ cs'.cfg.autoLeave = false ∧
  -- (2026-10-20, witness support) **`NoWitReconf`**: at a configuration without a witness
  -- (`raft.applyConfChange`'s premise: `confchange`'s model has none of Go's witness changes yet)
  cfg.cfg.wit = W64 0

/-- The dynamic mode's premises of `ApplyConfChange` (2026-10-14, stage B7 part 2), at the change
`o` the application passes: it is the decoded change (`dec`, from the entry and the log before
it) of the next conf-change entry `e` of the committed log handed out, at position `k` (log index
`k + 1`), past every applied one (`capplied ≤ k`, none in between: in order, once); it applies to
the configuration in use (`ccStepB`: no `confchange` error, fewer than `2^62` tracked ids -- Go
panics otherwise); and its result is no auto-leave joint configuration (`appliedTo`'s auto-leave
proposal is out of `raft.Step`'s scope). -/
def DynCCPre (dec : CCDec) (rs : RNState) (o : CCMsg) (k : Nat) (e : EntryM)
    (cs' : CCState) : Prop :=
  DynCCPreOp dec rs.delivered rs.capplied rs.cfg (ccV2Of o) k e cs'

/-- The entry `Propose` builds, `&pb.Entry{Data: data}`, as the model reads it (2026-10-16,
stage R5; D6: the data is its bytes; until then `propEntry data_sl`, the Goose value). -/
def propEntryM (d : List w8) : EntryM := ⟨W64 0, W64 0, W32 0, d, W64 0⟩

/-- The scalars of the message `Propose`, `confChangeToMsg` and `node.Propose` build,
`pb.Message{Type: MsgProp, ...}` (2026-10-16, stage R5; until then `propMsg esl`, the Goose
value with its entries' slice). `Propose`/`node.run` set `From` to the node's id. -/
def propMsgM : MessageM := { (zero_val MessageM) with Type' := MsgProp }

/-- The entry `confChangeToMsg` builds for the conf change `o` marshalled as `bs`:
`pb.Entry{Type: typ, Data: data}` (2026-10-16, stage R5; R4 dropped the value builder
`ccEntry`). -/
def ccEntryM (o : Option CCMsg) (bs : List w8) : EntryM := ⟨W64 0, W64 0, ccEntryType o, bs, W64 0⟩

end defs

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

-- (2026-10-16, stage R5) `pendingOwn` (the capacity of a `MsgStorageApplyResp`'s `Entries`)
-- is gone: a pending step's message is owned (`msgIn`, `ownRawNode`'s `Hpend`), capacity
-- included.

/-- The log's last index leaves room for a batch of `2^61` entries (2026-10-14, stage B7 part
2), as `raft__appendEntry.lean`'s `ownRaftLog_facts`: the stable part is below `isStorage`'s
bound `2^61`, the unstable part a Go slice. -/
theorem ownRaftLog_last_bound (l : Loc) (ls : LogState) :
    ⊢ ownRaftLog (GF := GF) l ls -∗
      ⌜uint.Z ls.prev.index' + ((ls.sents ++ ls.uents).length : Int) < 2^61 + 2^63⌝ ∗
      ownRaftLog l ls := by
  iintro H0
  iNamed H0
  ihave #Hsto : isStorage (GF := GF) lv.storage' $$ []
  · iexact HisStorage
  iunfold isStorage at Hsto
  iunfold isStorageWith at Hsto
  icases Hsto with ⟨%isv, #Hs⟩
  iNamed Hs
  icases Hbounded $$ %σ HStorage with ⟨%Hstb, HStorage⟩
  ihave %Hul := entsPts_len _ _ _ $$ Huents
  have Hsb : uint.Z ls.prev.index' + (ls.sents.length : Int) < 2^61 := by
    unfold LogStoreOk at Hstore
    split at Hstore
    · obtain ⟨Hsp, Hstored, -⟩ := Hstore
      have := Hstored.length_le
      rw [Hsp] at Hstb
      omega
    · obtain ⟨rfl, Hs0, Hsid⟩ := Hstore
      rw [Hs0, List.length_nil]; omega
  isplitr
  · ipureintro
    have : (ls.uents.length : Int) < 2^63 := by
      rw [Hul.1]; have := word.signed_range lv.unstable'.entries'.len; word
    rw [List.length_append]; push_cast
    omega
  · iapply ownRaftLog_intro l lv lv.storage' σ _ _ ls rfl Hcm Hap Hidx Hnowrap Hstore Hoffset
      Happlied Hpapplied Hcommitted Hssnap Hapg Hip Hipb Hpersist Happlying
      Hpaused Hasz Hamx Hstor Hpend Hfl Hsksn rfl rfl rfl $$ Hl HisStorage HStorage Husnap Hpksn Huents
      Huents_cap Hl_logger Hu_logger

/-- ... read through the struct: room for a dropped proposal's indices (`GMode.Pre`). -/
theorem ownRaftPhysC_last_bound (c : CfgM) {V : GSet w64} (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhysCV (GF := GF) c V r id s -∗
      ⌜plogLastIndexZ (toPState s).base (toPState s).log + 2 ^ 61 < 2 ^ 64⌝ ∗
      ownRaftPhysCV c V r id s := by
  iintro H
  icases ownRaftPhysC_log_same c r id s $$ H with ⟨Hlog, Hback⟩
  icases ownRaftLog_last_bound _ _ $$ Hlog with ⟨%Hb, Hlog⟩
  ihave H := Hback $$ Hlog
  iframe H
  ipureintro
  simp only [plogLastIndexZ, toPState]
  omega

/-- The log's `applied ≤ applying ≤ committed`, read through the struct. -/
theorem ownRaftPhysC_logwf (c : CfgM) {V : GSet w64} (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhysCV (GF := GF) c V r id s -∗
      ⌜uint.Z s.logst.applied ≤ uint.Z s.logst.applying ∧
        uint.Z s.logst.applying ≤ uint.Z s.logst.committed⌝ ∗ ownRaftPhysCV c V r id s := by
  iintro H
  icases ownRaftPhysC_log_same c r id s $$ H with ⟨Hlog, Hback⟩
  icases ownRaftLog_ready_wf _ _ $$ Hlog with ⟨%Hw, Hlog⟩
  ihave H := Hback $$ Hlog
  iframe H
  ipureintro; exact Hw.2

/-- (D19i part 1) The floor and `applied` (`RNState.flw`): the floor is at most `applied` unless
raised; and `applied` lags `applying` only while an apply acknowledgement up to `applying` is
queued for `Advance` (so `Advance` leaves `applied` at least `applying`, at least the floor). -/
def RNFl (rs : RNState) (s : NState) : Prop :=
  (rs.flw = false → uint.Z s.logst.fl ≤ uint.Z s.logst.applied) ∧
  (uint.Z s.logst.applied < uint.Z s.logst.applying →
    ∃ ce e, Pending.applyAck ce ∈ rs.steps ∧ ce.getLast? = some e ∧
      uint.Z s.logst.applying ≤ uint.Z e.Index')

/-- `RNFl` across a step that keeps the floor, `applying`, the queue and the flag, and does not
move `applied` back. -/
theorem RNFl.keep {rs rs' : RNState} {s s' : NState} (h : RNFl rs s)
    (hfl : s'.logst.fl = s.logst.fl) (hap : uint.Z s.logst.applied ≤ uint.Z s'.logst.applied)
    (hag : s'.logst.applying = s.logst.applying)
    (hw : rs'.flw = rs.flw := by rfl) (hst : rs'.steps = rs.steps := by rfl) : RNFl rs' s' := by
  refine ⟨fun hf => ?_, fun hlt => ?_⟩
  · have := h.1 (hw ▸ hf); rw [hfl]; omega
  · rw [hag] at hlt ⊢; rw [hst]; exact h.2 (by omega)

/-- (2026-10-17) The pre-vote scope and the term ceiling, as `ownRawNode` keeps them: pre-vote off
in the dynamic mode (a pre-candidate there needs `StepR.campaign`'s guard kept: not yet proved);
the ceiling `rs.tc` the struct's (`NGhost.tc`), at least the term, and one past it at a
pre-candidate (a won pre-vote campaigns at `term + 1`: the pre-campaign's budget). -/
def RNPv (rs : RNState) (s : NState) : Prop :=
  (rs.mode.isDyn = true → s.prevote = false) ∧ rs.tc = s.gh.tc ∧
  uint.Z s.term ≤ uint.Z s.gh.tc ∧
  (s.role = .preCandidate → uint.Z s.term + 1 ≤ uint.Z s.gh.tc)

theorem RNPv.dyn {rs : RNState} {s : NState} (H : RNPv rs s) (g : RGh) :
    (rs.mode.toG g).isDyn = true → s.prevote = false :=
  fun h => H.1 (by rw [← RNMode.toG_isDyn rs.mode g]; exact h)

set_option hygiene false in
/-- A premise of `raft.Step` about a type a network message is not (`Hty`): vacuous. -/
local macro "not_net" : tactic => `(tactic| (intro h; first
  | (obtain h | h := h <;> (first | exact h.elim | (rw [h] at Hty; simp [netStepTypes,
  MsgApp, MsgAppResp, MsgVote, MsgVoteResp, MsgHeartbeat, MsgHeartbeatResp,MsgCheckQuorum, MsgHup,
  MsgPreVote, MsgPreVoteResp, MsgSnap, MsgBeat, MsgProp, MsgStorageAppendResp,
  MsgStorageApplyResp, MsgReadIndex, MsgReadIndexResp, MsgForgetLeader, MsgUnreachable, MsgSnapStatus, MsgTimeoutNow, MsgTransferLeader] at Hty)))
  | (first | exact h.elim | (rw [h] at Hty; simp [netStepTypes,
  MsgApp, MsgAppResp, MsgVote, MsgVoteResp, MsgHeartbeat, MsgHeartbeatResp,MsgCheckQuorum, MsgHup,
  MsgPreVote, MsgPreVoteResp, MsgSnap, MsgBeat, MsgProp, MsgStorageAppendResp,
  MsgStorageApplyResp, MsgReadIndex, MsgReadIndexResp, MsgForgetLeader, MsgUnreachable, MsgSnapStatus, MsgTimeoutNow, MsgTransferLeader] at Hty))))

/-- A stamped type is not one of the unstamped ones. -/
local macro "ty_ne" : tactic => `(tactic| (simp [UnstampedType, MsgApp, MsgAppResp, MsgVote,
  MsgVoteResp, MsgHeartbeat, MsgHeartbeatResp, MsgPreVote, MsgPreVoteResp, MsgReadIndex, MsgReadIndexResp,
  MsgForgetLeader, MsgUnreachable, MsgSnapStatus, MsgTimeoutNow, MsgTransferLeader]))

/-- **`raft.Step`'s premises of a message from the network** (`NetMsgOk`) at a `RawNode`'s
state (`RNPv rs s`, the term `rs.term = s.term`; the ceiling covering the message's term and a
transfer's campaign, a pre-vote request only past term `0`): every premise up to `RestMsgOk`,
vacuous at a type the network does not deliver. `k` is `raft.Step`'s spec at the message (what it
takes after `RestMsgOk` is left in `X`). Shared by `RawNode.Step` (`RawNode__Step.lean`) and
`run`'s step (`InvNodeRun.lean`, `wp_rn_raft_Step_net`). -/
theorem NetMsgOk.raftStep {id : w64} {rs : RNState} {s : NState} {c : CfgM} {m : MessageM}
    {ents : List EntryM} {sn : Option SnapshotM} {ctx : List w8} {rsp : List Loc} {X : Prop}
    (Hok : NetMsgOk id ⟨m, ents, sn, ctx, rsp⟩) (Hpv : RNPv rs s) (Htrm : rs.term = s.term)
    (Hmtc : uint.Z m.Term' ≤ uint.Z rs.tc)
    (Htn : m.Type' = MsgTimeoutNow → max (uint.Z rs.term) (uint.Z m.Term') + 1 ≤ uint.Z rs.tc)
    (Hb1 : m.Type' = MsgPreVote → 1 ≤ uint.Z s.term)
    -- (D19i part 1) the floor at most `applied` (a `MsgTimeoutNow` campaigns)
    (Hfla : uint.Z s.logst.fl ≤ uint.Z s.logst.applied)
    -- (2026-10-19, D21 M2r) a transfer request only with leader transfer on
    (Hxo : m.Type' = MsgTransferLeader → s.gh.xf = false)
    (k : StepMsg m →
      (m.Type' = MsgHup → m.Term' = W64 0 ∧ uint.Z s.term + 1 < 2 ^ 64 ∧
        (s.prevote = true → uint.Z s.term + 1 ≤ uint.Z s.gh.tc) ∧
        uint.Z s.logst.fl ≤ uint.Z s.logst.applied) →
      (m.Type' = MsgVote → m.To' = id ∧ m.Term' ≠ W64 0 ∧ m.From' ≠ W64 0) →
      (m.Type' = MsgVoteResp → m.To' = id ∧ m.Term' ≠ W64 0) →
      (m.Type' = MsgPreVote → m.To' = id ∧ m.Term' ≠ W64 0 ∧ m.From' ≠ W64 0 ∧ m.From' ≠ id ∧
        (s.term = W64 0 → plogUpToDate s.logst.prev (s.logst.sents ++ s.logst.uents)
          (entryID.mk m.LogTerm' m.Index') = true) ∧
        (uint.Z m.Term' ≤ uint.Z s.term ∨ uint.Z m.Term' ≤ uint.Z s.gh.tc)) →
      (m.Type' = MsgPreVoteResp → m.To' = id ∧ m.Term' ≠ W64 0 ∧ m.From' ≠ W64 0 ∧
        (s.role = .preCandidate → uint.Z s.term + 1 < 2 ^ 64)) →
      (m.Type' = MsgApp → m.To' = id ∧ m.Term' ≠ W64 0 ∧ m.From' ≠ W64 0 ∧ m.From' ≠ id) →
      (m.Type' = MsgHeartbeat → m.To' = id ∧ m.Term' ≠ W64 0 ∧ m.From' ≠ W64 0 ∧ m.From' ≠ id) →
      (m.Type' = MsgAppResp → m.To' = id ∧ m.Term' ≠ W64 0 ∧ m.From' ≠ W64 0 ∧
        (m.Reject' = true → m.From' ≠ id)) →
      (m.Type' = MsgHeartbeatResp → m.To' = id ∧ m.Term' ≠ W64 0 ∧ m.From' ≠ W64 0 ∧
        m.From' ≠ id) →
      (m.Type' = MsgSnap → m.To' = id ∧ m.Term' ≠ W64 0 ∧ m.From' ≠ W64 0 ∧ m.From' ≠ id) →
      (m.Type' = MsgBeat ∨ m.Type' = MsgCheckQuorum → m.Term' = W64 0) →
      (m.Type' = MsgProp → m.Term' = W64 0 ∧ (m.From' = W64 0 ∨ m.From' = id)) →
      (m.Type' = MsgStorageAppendResp → sn = none ∧ uint.Z m.Term' ≤ uint.Z s.term ∧
        (m.Term' = W64 0 ∨ m.Term' = s.term → m.Index' ≠ W64 0 →
          StableOk s.logst (entryID.mk m.LogTerm' m.Index')) ∧ s.gh.unst = false) →
      (m.Type' = MsgStorageApplyResp → m.Term' = W64 0) →
      (m.Type' = MsgReadIndex → m.Term' = W64 0) →
      (m.Type' = MsgStorageApplyResp → c.autoLeave = true → s.role ≠ .leader) →
      (m.Type' = MsgReadIndexResp → m.To' = id ∧ m.Term' ≠ W64 0 ∧ m.From' ≠ W64 0 ∧
        m.From' ≠ id) →
      RestMsgOk s m ents ctx → X) : X := by
  have Hok0 := Hok
  simp only [NetMsgOk] at Hok0
  obtain ⟨Hty, Hnri, Hri, Hself, Hrej, -, Hpvf⟩ := Hok0
  have Hnr : ∀ {t : w32}, m.Type' = t → ¬ UnstampedType t →
      m.To' = id ∧ m.Term' ≠ W64 0 ∧ m.From' ≠ W64 0 :=
    fun h ht => Hnri (h ▸ ht)
  have Htcb : uint.Z s.gh.tc < 2 ^ 64 := by word
  refine k (netStepTypes_stepMsg Hty) (by not_net) (fun h => Hnr h (by ty_ne))
    (fun h => ⟨(Hnr h (by ty_ne)).1, (Hnr h (by ty_ne)).2.1⟩)
    (fun h => ⟨(Hnr h (by ty_ne)).1, (Hnr h (by ty_ne)).2.1, (Hnr h (by ty_ne)).2.2, Hpvf h,
      fun hz => by exfalso; have := Hb1 h; rw [hz] at this; word,
      .inr (by rw [← Hpv.2.1]; exact Hmtc)⟩)
    (fun h => ⟨(Hnr h (by ty_ne)).1, (Hnr h (by ty_ne)).2.1, (Hnr h (by ty_ne)).2.2,
      fun hp => by have := Hpv.2.2.2 hp; omega⟩)
    (fun h => ⟨(Hnr h (by ty_ne)).1, (Hnr h (by ty_ne)).2.1, (Hnr h (by ty_ne)).2.2,
      Hself (.inl h)⟩)
    (fun h => ⟨(Hnr h (by ty_ne)).1, (Hnr h (by ty_ne)).2.1, (Hnr h (by ty_ne)).2.2,
      Hself (.inr (.inl h))⟩)
    (fun h => ⟨(Hnr h (by ty_ne)).1, (Hnr h (by ty_ne)).2.1, (Hnr h (by ty_ne)).2.2, Hrej h⟩)
    (fun h => ⟨(Hnr h (by ty_ne)).1, (Hnr h (by ty_ne)).2.1, (Hnr h (by ty_ne)).2.2,
      Hself (.inr (.inr (.inl h)))⟩)
    (by not_net) (by not_net) (by not_net) (by not_net) (by not_net) (fun h => Hri (.inl h))
    (by not_net)
    (fun h => ⟨(Hnr h (by ty_ne)).1, (Hnr h (by ty_ne)).2.1, (Hnr h (by ty_ne)).2.2,
      Hself (.inr (.inr (.inr h)))⟩)
    (Hok.restMsgOk (st := ⟨m, ents, sn, ctx, rsp⟩) (fun h => by
      have := Htn h; rw [Hpv.2.1, Htrm] at this
      have := Int.le_max_left (uint.Z s.term) (uint.Z m.Term')
      have := Int.le_max_right (uint.Z s.term) (uint.Z m.Term')
      simp only at h ⊢
      exact ⟨by omega, by omega, Hfla⟩) Hxo)

/-- `RNPv` after a step of `raft.Step` (`PreCandStep`): the setting and the ceiling kept, the term
within the ceiling, and a pre-campaign (`MsgHup`) only with the ceiling one past the term. -/
theorem RNPv.step {rs rs' : RNState} {s s' : NState} {m : MessageM} (H : RNPv rs s)
    (hmd : rs'.mode = rs.mode) (htc : rs'.tc = rs.tc) (hpv : s'.prevote = s.prevote)
    (hgh : s'.gh = s.gh) (ht : uint.Z s'.term ≤ uint.Z s.gh.tc) (hpc : PreCandStep m s s')
    (hhup : m.Type' = MsgHup → uint.Z s.term + 1 ≤ uint.Z s.gh.tc) : RNPv rs' s' := by
  obtain ⟨H1, H2, -, H4⟩ := H
  refine ⟨fun h => by rw [hpv]; exact H1 (hmd ▸ h), by rw [htc, hgh]; exact H2,
    by rw [hgh]; exact ht, fun h => ?_⟩
  obtain ⟨Ht, Hor⟩ := hpc h
  rw [hgh, Ht]
  rcases Hor with Hr | Hh
  · exact H4 Hr
  · exact hhup Hh

/-- `RNPv` across a step that keeps the term, the role, the setting and the ghost bounds. -/
theorem RNPv.keep {rs rs' : RNState} {s s' : NState} (H : RNPv rs s)
    (hmd : rs'.mode = rs.mode) (htc : rs'.tc = rs.tc) (hpv : s'.prevote = s.prevote)
    (hgh : s'.gh = s.gh) (ht : s'.term = s.term) (hr : s'.role = s.role) : RNPv rs' s' := by
  obtain ⟨H1, H2, H3, H4⟩ := H
  refine ⟨fun h => by rw [hpv]; exact H1 (hmd ▸ h), by rw [htc, hgh]; exact H2,
    by rw [hgh, ht]; exact H3, fun h => by rw [hgh, ht]; exact H4 (hr ▸ h)⟩

/-- What `GMode.Pre` needs of the node, for any message but a snapshot or a storage-apply
acknowledgement (2026-10-14, stage B7 part 2). -/
def PreFacts (dyn : Bool) (s : NState) : Prop :=
  (dyn = true → s.role ≠ .preCandidate) ∧
  plogLastIndexZ (toPState s).base (toPState s).log + 2 ^ 61 < 2 ^ 64

theorem GMode.Pre.of_facts {md : GMode} {m : MessageM} {ents : List EntryM}
    {s : NState} (h : PreFacts md.isDyn s) (h1 : m.Type' ≠ MsgSnap)
    (h3 : m.Type' ≠ MsgStorageApplyResp) :
    md.Pre m ents s := by
  cases md with
  | static => trivial
  | dyn dec c0 h0 g => exact ⟨h.1 rfl, fun h' => absurd h' h3, fun _ => h.2⟩

/-- ... read off the struct, at a node with pre-vote off in the dynamic mode (2026-10-17: until
then at a node with pre-vote off). -/
theorem ownRaftPhysC_preFacts (c : CfgM) {V : GSet w64} (r : Loc) (id : w64) (s : NState)
    {dyn : Bool} (Hpv : dyn = true → s.prevote = false) :
    ⊢ ownRaftPhysCV (GF := GF) c V r id s -∗ ⌜PreFacts dyn s⌝ ∗ ownRaftPhysCV c V r id s := by
  iintro H
  icases ownRaftPhysC_precand c r id s $$ H with ⟨%Hpc, H⟩
  icases ownRaftPhysC_last_bound c r id s $$ H with ⟨%Hb, H⟩
  iframe H
  ipureintro
  refine ⟨fun hd h => ?_, Hb⟩
  have := Hpc h; rw [Hpv hd] at this; cases this

/-- The dynamic mode's premises of a step of `raft.Step` (`GMode.Pre`) for a message that is
no snapshot and no storage-apply acknowledgement, at a node with pre-vote off (2026-10-14,
stage B7 part 2): no pre-candidate (`ownRaftPhysC_precand`), and for a proposal the log's
room (`ownRaftPhysC_last_bound`). -/
theorem ownRaftPhysC_pre (c : CfgM) {V : GSet w64} (r : Loc) (id : w64) (s : NState)
    (md : GMode) (m : MessageM) (ents : List EntryM) (Hpv : md.isDyn = true → s.prevote = false)
    (h1 : m.Type' ≠ MsgSnap) (h3 : m.Type' ≠ MsgStorageApplyResp) :
    ⊢ ownRaftPhysCV (GF := GF) c V r id s -∗ ⌜md.Pre m ents s⌝ ∗ ownRaftPhysCV c V r id s := by
  iintro H
  icases ownRaftPhysC_precand c r id s $$ H with ⟨%Hpc, H⟩
  icases ownRaftPhysC_last_bound c r id s $$ H with ⟨%Hb, H⟩
  iframe H
  ipureintro
  cases md with
  | static => trivial
  | dyn dec c0 h0 g =>
    refine ⟨fun h => ?_, fun h => absurd h h3, fun _ => Hb⟩
    have := Hpc h; rw [Hpv rfl] at this; cases this

end proof

section rawnode
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
-- `hlc := HasLC.hasLC`: the predicate holds the ghost state (`ownRaftGhost`), as in
-- `Spec/raft__Step.lean`
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The message queued for a pending step. A self-addressed response
(2026-10-10): `SelfMsgOk`, its term and type as `Pending.self` records them, and its
abstraction legitimately sent (`isMessage`, from the outbox `Ready` drained) -- what
`Step`'s spec asks of it besides the term bound (`PendingOk`); it has no entries and no
context, so the abstraction is at `[]`, `[]`. (Until 2026-10-10 `msgAbs m a ∗ ⌜m.To' = id⌝`,
which `Step`'s spec could not use.) (2026-10-16, stage R5: on the message's state `st`, whose
pointer `ownRawNode` holds (`msgIn`); the pure part is `pendSt`; the apply acknowledgement's
entries are `st.ents`, read through `msgIn`, rather than a slice `sl ↦*□ ents`.) -/
def pendingRel (γ : RaftNames) (id : w64) (st : MsgSt) (p : Pending) : IProp GF :=
  iprop(⌜pendSt id st p⌝ ∗
    match p with
    | .self _ _ => iprop(□ (∀ ty, ⌜mtypeOf st.msg.Type' = some ty⌝ -∗
        isMessage γ (absMsg ty st.msg [] [])))
    | _ => iprop(True))

instance pendingRel_pers (γ : RaftNames) (id : w64) (st : MsgSt) (p : Pending) :
    Persistent (pendingRel (GF := GF) γ id st p) := by
  cases p <;> unfold pendingRel <;> infer_instance

/-- A message `Ready` hands to the application to send: what it contributes to the
protocol's messages (`msgAbs`: nothing, for a type the protocol does not describe) was
legitimately sent (`isMessage`). (2026-10-16, stage R5: on the message's state; `msgAbs` is
pure.) (2026-10-19, D21 M3) In the cluster's no-snapshot mode no `MsgSnap`; (D21 M2r, D21g (A))
and what the receiver's `NetMsgOk` needs of it (`SentMsgOk`, `NetMsgOk.of_sent`): its type, a
nonzero sender other than its destination, its term stamped (no `MsgTimeoutNow`, no
`MsgTransferLeader`: leader transfer is off in the mode). -/
def isRaftMsg (γ : RaftNames) (st : MsgSt) : IProp GF :=
  iprop(⌜γ.reNoSnap = true → st.msg.Type' ≠ MsgSnap⌝ ∗ ⌜γ.reNoSnap = true → SentMsgOk st⌝ ∗
    ∃ a, ⌜msgAbs st a⌝ ∗ [∗list] x ∈ a.toList, isMessage γ x)

instance isRaftMsg_pers (γ : RaftNames) (st : MsgSt) :
    Persistent (isRaftMsg (GF := GF) γ st) := by
  unfold isRaftMsg; infer_instance

/-- (2026-10-19, D21 M2r) In the cluster's no-snapshot mode a message a `Ready` handed out is
`SentMsgOk`: at its destination `NetMsgOk.of_sent` (D21g (A)). -/
theorem isRaftMsg_sent (γ : RaftNames) (hns : γ.reNoSnap = true) (st : MsgSt) :
    isRaftMsg (GF := GF) γ st ⊢ ⌜SentMsgOk st⌝ := by
  iintro H
  unfold isRaftMsg
  icases H with ⟨-, %H, -⟩
  ipureintro; exact H hns

/-- The records of what the storage holds (2026-10-10): `L` (after `b`) is a log with
records (`logRecs`), as `ownLogGhost` keeps of the node's log; `ownRawNode` keeps it of
`stored`, which a `Ready` sets to the log (`ownRaftGhost_storedRecs`), so that a later
log with records can be matched against it (`stableOk_of_stored`). -/
def storedRecs (γ : RaftNames) (b : entryID) (L : List EntryM) : IProp GF :=
  iprop(⌜PlogWf b L⌝ ∗ logRecs γ b L)

instance storedRecs_pers (γ : RaftNames) (b : entryID) (L : List EntryM) :
    Persistent (storedRecs (GF := GF) γ b L) := by
  unfold storedRecs; infer_instance

/-- The node's own log has records. -/
theorem ownRaftGhost_storedRecs (γ : RaftNames) (id : w64) (ps : PState) {md : Bool} :
    ownRaftGhost (GF := GF) γ id ps md ⊢ storedRecs γ ps.base ps.log := by
  iintro H
  unfold ownRaftGhost
  icases H with ⟨%γv, %voted, %kl, H⟩
  iNamed H
  unfold ownLogGhost
  icases Hlg with ⟨%γm, %terms, %γa, %acks, %fp, %γc, %camps, %γl, %vlogs, %γw, %wins, Hlg⟩
  iNamed Hlg
  unfold storedRecs
  isplitr
  · ipureintro; exact Hfull.2.1
  iexact Hrecs

/-- ... read out without consuming the ghost state. -/
theorem ownRaftGhost_storedRecs_keep (γ : RaftNames) (id : w64) (ps : PState) {md : Bool} :
    ⊢ ownRaftGhost (GF := GF) γ id ps md -∗ ownRaftGhost γ id ps md ∗ storedRecs γ ps.base ps.log :=
  entails_wand (persistent_entails_left (ownRaftGhost_storedRecs γ id ps))

/-- A queued acknowledgement of the last entry `e` of what the storage holds is
`StableOk` (2026-10-10), once nothing is unpersisted and with no snapshot pending: if
it hits, the log has `e`'s term at `e`'s index, and Log Matching between the records of
`stored` and of the log (`stored_agree`) makes `stored` the log up to `e`. -/
theorem stableOk_of_stored (γ : RaftNames) (id : w64) (s : NState) {md : Bool}
    (e : entryID)
    (He : plogLast s.logst.prev s.logst.stored = e)
    (Hsn : s.logst.snap = none) (Hun : s.logst.unpersisted = []) :
    ⊢ storedRecs γ s.logst.prev s.logst.stored -∗ ownRaftGhost (GF := GF) γ id (toPState s) md -∗
      ⌜StableOk s.logst e⌝ ∗ ownRaftGhost γ id (toPState s) md := by
  iintro #Hst Hg
  icases ownRaftGhost_storedRecs_keep γ id (toPState s) $$ Hg with ⟨Hg, #Hlr⟩
  unfold storedRecs
  icases Hst with ⟨%HwL, #HrL⟩
  icases Hlr with ⟨%HwF, #HrF⟩
  icases logRecs_agree γ _ _ _ _ $$ HrL HrF with %HRA
  isplitr
  · ipureintro
    intro Hhit
    exact ⟨Hsn, Hun, stored_agree _ _ _ _ HwL HwF HRA He Hhit.2⟩
  iexact Hg

/-- Nothing stored has records. -/
theorem storedRecs_nil (γ : RaftNames) (b : entryID) : ⊢ storedRecs (GF := GF) γ b [] := by
  unfold storedRecs logRecs
  isplitr
  · ipureintro; intro k e h; simp at h
  · iapply (BigSepL.bigSepL_nil).2; iempintro

/-- The records of `stored`, at a state with the same `prev` and `stored`. -/
theorem storedRecs_eq (γ : RaftNames) (b b' : entryID) (L L' : List EntryM)
    (Hb : b' = b) (HL : L' = L) :
    ⊢ storedRecs (GF := GF) γ b L -∗ storedRecs γ b' L' := by
  subst Hb HL; iintro H; iexact H

/-! ## The `RawNode` struct, with `raft` shared (2026-10-10)

The `AccessStrict` instances for `rawNodeOwn` are scoped (`open RawNodeOwnAccess`): the
`AccessStrict` classes' last parameters are `outParam`s, so a global instance would be
tried for a field of a whole-struct points-to as well (`NewRawNode`'s) and win.

`rawNodeOwn l v` is `l ↦ v` with the field nobody writes after `NewRawNode` -- `raft`, the
pointer to the raft struct -- persistent: `node.go`'s `Tick` reads `n.rn.raft` while `run`
owns the node (`raftOwn`, `InvRaftPhys.lean`, for the raft struct's own fields). (2026-10-16,
stage R5: `prevHardSt` is a `*pb.HardState`, `stepsOnAdvance` a `[]*pb.Message`.) -/
def rawNodeOwn (l : Loc) (v : RawNode) : IProp GF :=
  iprop("#H_raft" ∷ l.[RawNode, go!"raft"] ↦□ v.raft' ∗
    "H_asyncStorageWrites" ∷ l.[RawNode, go!"asyncStorageWrites"] ↦ v.asyncStorageWrites' ∗
    "H_prevSoftSt" ∷ l.[RawNode, go!"prevSoftSt"] ↦ v.prevSoftSt' ∗
    "H_prevHardSt" ∷ l.[RawNode, go!"prevHardSt"] ↦ v.prevHardSt' ∗
    "H_stepsOnAdvance" ∷ l.[RawNode, go!"stepsOnAdvance"] ↦ v.stepsOnAdvance')

theorem rawNodeOwn_of_pts (l : Loc) (v : RawNode) :
    ⊢ (l ↦ v : IProp GF) ==∗ rawNodeOwn l v := by
  iintro Hl
  rw [typedPointsto_unseal_eq l v]
  icases Hl with ⟨Hf, -⟩
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hf
  ipersist raft
  imodintro
  unfold rawNodeOwn
  simp only [named]
  iframe
  try iframe #

theorem rawNodeOwn_raft (l : Loc) (v : RawNode) :
    ⊢ rawNodeOwn (GF := GF) l v -∗ l.[RawNode, go!"raft"] ↦□ v.raft' := by
  iintro H; unfold rawNodeOwn; iNamed H; iexact H_raft

local macro "rawNodeOwn_access " f:ident : tactic =>
  `(tactic| (constructor
             unfold rawNodeOwn
             iintro H
             iNamed H
             isplitl [$f:ident]
             · iexact $f:ident
             iintro $f:ident
             simp only [named]
             iframe
             try iframe #))

namespace RawNodeOwnAccess

scoped instance (priority := high) rawNodeOwn_access_load_raft (l : Loc) (v : RawNode) :
    AccessStrict (PROP := IProp GF) (l.[RawNode, go!"raft"] ↦□ v.raft')
      (l.[RawNode, go!"raft"] ↦□ v.raft') (rawNodeOwn l v) (rawNodeOwn l v) := by
  constructor
  unfold rawNodeOwn
  iintro H
  iNamed H
  iframe H_raft
  iintro -
  iframe
  try iframe #

scoped instance (priority := high) rawNodeOwn_access_load_asyncStorageWrites (l : Loc) (v : RawNode) :
    AccessStrict (PROP := IProp GF) (l.[RawNode, go!"asyncStorageWrites"] ↦ v.asyncStorageWrites') (l.[RawNode, go!"asyncStorageWrites"] ↦ v.asyncStorageWrites')
      (rawNodeOwn l v) (rawNodeOwn l v) := by
  rawNodeOwn_access H_asyncStorageWrites

scoped instance (priority := high) rawNodeOwn_access_store_asyncStorageWrites (l : Loc) (v : RawNode) (x : Bool) :
    AccessStrict (PROP := IProp GF) (l.[RawNode, go!"asyncStorageWrites"] ↦ v.asyncStorageWrites') (l.[RawNode, go!"asyncStorageWrites"] ↦ x)
      (rawNodeOwn l v) (rawNodeOwn l { v with asyncStorageWrites' := x }) := by
  rawNodeOwn_access H_asyncStorageWrites

scoped instance (priority := high) rawNodeOwn_access_load_prevSoftSt (l : Loc) (v : RawNode) :
    AccessStrict (PROP := IProp GF) (l.[RawNode, go!"prevSoftSt"] ↦ v.prevSoftSt') (l.[RawNode, go!"prevSoftSt"] ↦ v.prevSoftSt')
      (rawNodeOwn l v) (rawNodeOwn l v) := by
  rawNodeOwn_access H_prevSoftSt

scoped instance (priority := high) rawNodeOwn_access_store_prevSoftSt (l : Loc) (v : RawNode) (x : Loc) :
    AccessStrict (PROP := IProp GF) (l.[RawNode, go!"prevSoftSt"] ↦ v.prevSoftSt') (l.[RawNode, go!"prevSoftSt"] ↦ x)
      (rawNodeOwn l v) (rawNodeOwn l { v with prevSoftSt' := x }) := by
  rawNodeOwn_access H_prevSoftSt

scoped instance (priority := high) rawNodeOwn_access_load_prevHardSt (l : Loc) (v : RawNode) :
    AccessStrict (PROP := IProp GF) (l.[RawNode, go!"prevHardSt"] ↦ v.prevHardSt') (l.[RawNode, go!"prevHardSt"] ↦ v.prevHardSt')
      (rawNodeOwn l v) (rawNodeOwn l v) := by
  rawNodeOwn_access H_prevHardSt

scoped instance (priority := high) rawNodeOwn_access_store_prevHardSt (l : Loc) (v : RawNode) (x : Loc) :
    AccessStrict (PROP := IProp GF) (l.[RawNode, go!"prevHardSt"] ↦ v.prevHardSt') (l.[RawNode, go!"prevHardSt"] ↦ x)
      (rawNodeOwn l v) (rawNodeOwn l { v with prevHardSt' := x }) := by
  rawNodeOwn_access H_prevHardSt

scoped instance (priority := high) rawNodeOwn_access_load_stepsOnAdvance (l : Loc) (v : RawNode) :
    AccessStrict (PROP := IProp GF) (l.[RawNode, go!"stepsOnAdvance"] ↦ v.stepsOnAdvance') (l.[RawNode, go!"stepsOnAdvance"] ↦ v.stepsOnAdvance')
      (rawNodeOwn l v) (rawNodeOwn l v) := by
  rawNodeOwn_access H_stepsOnAdvance

scoped instance (priority := high) rawNodeOwn_access_store_stepsOnAdvance (l : Loc) (v : RawNode) (x : GoSlice) :
    AccessStrict (PROP := IProp GF) (l.[RawNode, go!"stepsOnAdvance"] ↦ v.stepsOnAdvance') (l.[RawNode, go!"stepsOnAdvance"] ↦ x)
      (rawNodeOwn l v) (rawNodeOwn l { v with stepsOnAdvance' := x }) := by
  rawNodeOwn_access H_stepsOnAdvance

end RawNodeOwnAccess

/-- The configuration the struct is at has the voters the client sees (`RNState.vcfg`;
2026-10-14, stage B7 part 2): `γ.reCfg` statically, the configuration in use dynamically. -/
theorem ownStepGhost_vcfg (γ : RaftNames) (rs : RNState) (fp : List EntryM) (c : CfgM)
    (id : w64) (s : NState) :
    ⊢ ownStepGhost (GF := GF) γ (rs.mode.toG ⟨rs.capplied, rs.cfg, fp⟩) c id s -∗
      ⌜c.incoming = (rs.vcfg γ).incoming ∧ c.outgoing = (rs.vcfg γ).outgoing⌝ ∗
      ownStepGhost γ (rs.mode.toG ⟨rs.capplied, rs.cfg, fp⟩) c id s := by
  iintro H
  unfold RNState.vcfg
  cases hm : rs.mode with
  | static =>
    simp only [RNMode.toG, ownStepGhost, ghostRest, ghostRestM]
    icases H with ⟨Hg, %Hnl, %Hps, %HC⟩
    iframe Hg
    ipureintro
    exact ⟨⟨HC.1.1, HC.1.2.1⟩, Hnl, Hps, HC⟩
  | dyn dec c0 h0 _ =>
    simp only [RNMode.toG, ownStepGhost, ghostRest, ghostRestM]
    icases H with ⟨Hg, %Hnl, %Hps, %HC, Hr⟩
    iframe Hg Hr
    isplitr
    · ipureintro
      have hc := HC.2.1
      exact ⟨by rw [← hc], by rw [← hc]⟩
    ipureintro
    exact ⟨Hnl, Hps, HC⟩

/-- A node's committed prefix, with records, is a prefix of the global committed log (persistent;
read off the ghost state's log ghost). -/
theorem ownRaftGhost_cmt (γ : RaftNames) (id : w64) (ps : PState) {md : Bool} :
    ownRaftGhost (GF := GF) γ id ps md ⊢
      ∃ fp, ⌜FullOk ps.base fp⌝ ∗ logRecs γ base0 fp ∗ isCommitted γ (cprefix fp ps) := by
  iintro Hg
  iunfold ownRaftGhost at Hg
  icases Hg with ⟨%γv, %voted, %kl, Hg⟩
  iNamed Hg
  iapply ownLogGhost_cmt γ id ps kl $$ Hlg

/-- In the dynamic mode, a committed log no longer than the node's commit index -- the committed
log a `RawNode` handed out, `delivered` -- is a prefix of the node's full log (2026-10-14,
stage B7 part 2): both are prefixes of the global committed log (`isCommitted_agree`), and the
node's full prefix is its ghost part's (`FullOk_unique`). -/
theorem ownStepGhost_deliv (γ : RaftNames) (dec : CCDec) (c0 : CCState) (h0 : CfgOk c0)
    (g : RGh) (c : CfgM) (id : w64) (s : NState) (D : List EntryM)
    (Hlen : (D.length : Int) ≤ uint.Z s.logst.committed) :
    ⊢ isCommitted γ D -∗ ownStepGhost (GF := GF) γ (.dyn dec c0 h0 g) c id s -∗
      ⌜D <+: (rOf s g).full⌝ ∗ ownStepGhost γ (.dyn dec c0 h0 g) c id s := by
  iintro #HD H
  iunfold ownStepGhost at H
  icases H with ⟨Hg, Hr⟩
  icases (entails_wand (persistent_entails_left (ownRaftGhost_cmt γ id (toPState s)))) $$ Hg
    with ⟨Hg, %fp', %Hf', #Hfr', #Hc⟩
  iunfold ghostRest at Hr
  iunfold ghostRestM at Hr
  icases Hr with ⟨%Hnl, %Hps, %HC, #Hfr, Hcamp⟩
  icases FullOk_unique γ (toPState s).base fp' g.fp Hf' HC.2.2.full $$ Hfr' Hfr with %He
  icases isCommitted_agree γ _ _ $$ HD Hc with %Hag
  isplitr
  · ipureintro
    unfold cprefix at Hag
    have Hfull : (rOf s g).full = fp' ++ (toPState s).log := by
      simp only [RState.full, rOf.proj_fp, rOf.proj_p]; rw [He]
    have Hfl := HC.2.2.full_length
    have Hcl := HC.2.2.commit_last
    rw [Hfull] at Hfl
    simp only [rOf.proj_p] at Hcl Hfl
    have hn : (uint.Z (toPState s).commit).toNat ≤ (fp' ++ (toPState s).log).length := by
      have := uint_Z_nonneg (toPState s).commit; omega
    have hPl : ((fp' ++ (toPState s).log).take (uint.Z (toPState s).commit).toNat).length =
        (uint.Z (toPState s).commit).toNat := by
      rw [List.length_take]; omega
    rw [Hfull]
    rcases Hag with h | h
    · exact h.trans (List.take_prefix _ _)
    · have hc' : D.length ≤ (uint.Z (toPState s).commit).toNat := by
        show D.length ≤ (uint.Z s.logst.committed).toNat; omega
      have heq := h.eq_of_length (by have := h.length_le; omega)
      rw [← heq]; exact List.take_prefix _ _
  iunfold ownStepGhost
  iframe Hg
  iunfold ghostRest
  iunfold ghostRestM
  isplitr
  · ipureintro; exact Hnl
  isplitr
  · ipureintro; exact Hps
  isplitr
  · ipureintro; exact HC
  isplitr
  · iexact Hfr
  iexact Hcamp

/-! ## The one predicate for a `RawNode` -/

/-- The persistent `stepDownOnRemoval` field (2026-10-14, stage B7 part 2): nobody writes it
after `newRaft`; in the dynamic mode it is on (`Config.StepDownOnRemoval`), so that a leader
an `ApplyConfChange` removes steps down (`StepR.stepDown`). -/
def sdrOk (r : Loc) (md : RNMode) : IProp GF :=
  iprop(∃ b : Bool, r.[raft, go!"stepDownOnRemoval"] ↦□ b ∗ ⌜md.isDyn = true → b = true⌝)

instance sdrOk_pers (r : Loc) (md : RNMode) : Persistent (sdrOk (GF := GF) r md) := by
  unfold sdrOk; infer_instance

/-- The pending queue's messages, owned, with their records (2026-10-16, stage R5): `ownRawNode`'s
`Hpend`. -/
abbrev pendList (γ : RaftNames) (id : w64) (steps : List Loc) (ps : List Pending) : IProp GF :=
  iprop([∗list] _k ↦ l;p ∈ steps;ps, ∃ st, msgIn l DFrac.discard st ∗ pendingRel γ id st p)

/-- The empty queue. -/
theorem pendList_nil (γ : RaftNames) (id : w64) :
    ⊢ pendList (GF := GF) γ id [] [] := by
  iapply (BigSepL2.bigSepL2_nil (Φ := fun _ l p => iprop(∃ st, msgIn (GF := GF) l DFrac.discard st ∗
    pendingRel γ id st p))).2
  iempintro

/-- See the file header. `s` is the node's physical state, `c` the configuration the struct is
at, `fp` the ghost full prefix (the dynamic mode's ghost part is `⟨rs.capplied, rs.cfg, fp⟩`);
`delivered` is the committed log up to `applying` (`isCommitted_agree` makes it the one such
list), `unpersisted` the log's. Since 2026-10-14 (reconfiguration stage B7 part 2) in either
mode (`rs.mode`): the struct at any configuration (`ownRaftPhysCV c`) and the ghost state as
`raft.Step` keeps it (`ownStepGhost`), with `NStateWf` for `NStateRel`. (2026-10-16, stage R5:
`prevHardSt` points to a read-only hard state `hprev` (`hsRO`; `NewRawNode` sets it to
`r.hardState()`, `acceptReady` to a `Ready`'s fresh one), existential like the soft state: no
spec states it; `stepsOnAdvance` holds pointers `steps`, each message owned (`msgIn`, its
entries read-only), with `pendingRel` of its state -- `Advance` hands each to `raft.Step`.) -/
def ownRawNode (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) : IProp GF :=
  iprop(∃ (s : NState) (cf : CfgM) (fp : List EntryM) (rnv : RawNode) (sv : SoftState)
      (hprev : HardStateM) (steps : List Loc),
  "Hrn" ∷ rawNodeOwn rn rnv ∗
  "Hphys" ∷ ownRaftPhysCV cf cf.voters rnv.raft' id s ∗
  "Hghost" ∷ ownStepGhost γ (rs.mode.toG ⟨rs.capplied, rs.cfg, fp⟩) cf id s ∗
  "#Hsdrf" ∷ sdrOk rnv.raft' rs.mode ∗
  "%Hwf" ∷ ⌜NStateWf s⌝ ∗
  -- scope (static mode): the node is a voter (`Step`'s premise for a snapshot; a shrinking
  -- `ApplyConfChange`'s); (2026-10-14) no auto-leave joint configuration
  -- (`appliedTo`'s auto-leave proposal is out of `raft.Step`'s scope)
  "%Hin" ∷ ⌜rs.mode = .static → id ∈ γ.reCfg⌝ ∗
  "%Hal" ∷ ⌜cf.autoLeave = false⌝ ∗
  -- scope: synchronous storage writes (`Config.AsyncStorageWrites` unset); `NewRawNode`
  -- copies the `Config` field
  "%Hasync" ∷ ⌜rnv.asyncStorageWrites' = false⌝ ∗
  -- `prevSoftSt`: a pointer to a `SoftState` nobody writes (it is either `NewRawNode`'s
  -- or a `Ready.SoftState`), held read-only; (2026-10-16, stage R5) `prevHardSt`: a pointer
  -- to a read-only hard state (`NewRawNode`'s `r.hardState()` or a `Ready.HardState`)
  "#Hsoft" ∷ rnv.prevSoftSt' ↦□ sv ∗
  "#Hhard" ∷ hsRO rnv.prevHardSt' hprev ∗
  "Hsteps" ∷ rnv.stepsOnAdvance' ↦* steps ∗
  "Hsteps_cap" ∷ ownSliceCap Loc rnv.stepsOnAdvance' (DFrac.own 1) ∗
  -- (2026-10-16, stage R5) each queued message owned, with its record (until then
  -- `pendingRel` of the Goose value, persistent, and `pendingOwn`)
  "Hpend" ∷ pendList γ id steps rs.steps ∗
  "#Hdeliv" ∷ isCommitted γ rs.delivered ∗
  -- the records of what the storage holds (2026-10-10), for the acknowledgement
  -- `Advance` steps (`PendingOk`, `stableOk_of_stored`)
  "#Hstrecs" ∷ storedRecs γ s.logst.prev s.logst.stored ∗
  "%Hdlen" ∷ ⌜rs.delivered.length = (uint.Z s.logst.applying).toNat⌝ ∗
  "%Hunp" ∷ ⌜rs.unpersisted = s.logst.unpersisted⌝ ∗
  -- scope: no snapshot pending (handing one out and `appliedSnap` are phase 2)
  "%Hsnap" ∷ ⌜s.logst.snap = none⌝ ∗
  -- the queue is steppable (since 2026-10-10 unconditionally: until then only for an
  -- `advanceable` one)
  "%Hstok" ∷ ⌜StepsOk s rs.steps⌝ ∗
  "%Htrm" ∷ ⌜rs.term = s.term⌝ ∗
  "%Hstor" ∷ ⌜rs.storage = s.logst.storage⌝ ∗
  -- (2026-10-17; until then pre-vote off, `s.prevote = false`, its scope) pre-vote off in the
  -- dynamic mode only, and the term ceiling (`RNPv`)
  "%Hpvoff" ∷ ⌜RNPv rs s⌝ ∗
  -- the lower bounds for `node.go` (2026-10-10, `RNState.outlb`)
  "%Hrs_out" ∷ ⌜rs.outlb = s.gh.outlb⌝ ∗
  "%Hrs_unst" ∷ ⌜rs.unst = s.gh.unst⌝ ∗
  "%Hrs_clb" ∷ ⌜uint.Z rs.clb ≤ uint.Z s.logst.committed⌝ ∗
  -- (D19i part 1) the floor and `applied`
  "%Hrnfl" ∷ ⌜RNFl rs s⌝)

/-- Closing the predicate; the pure premises are first, the resources in the order of
the definition. (2026-10-16, stage R5: the hard state `hprev` after the soft state; the
queue `pendList`, owned; no `pendingOwn`.) -/
theorem ownRawNode_intro (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState)
    (s : NState) (c : CfgM) (fp : List EntryM) (rnv : RawNode) (sv : SoftState)
    (hprev : HardStateM) (steps : List Loc)
    (Hwf : NStateWf s) (Hin : rs.mode = .static → id ∈ γ.reCfg) (Hal : c.autoLeave = false)
    (Hasync : rnv.asyncStorageWrites' = false)
    (Hdlen : rs.delivered.length = (uint.Z s.logst.applying).toNat)
    (Hunp : rs.unpersisted = s.logst.unpersisted) (Hsnap : s.logst.snap = none)
    (Hstok : StepsOk s rs.steps)
    (Htrm : rs.term = s.term) (Hstor : rs.storage = s.logst.storage)
    (Hpvoff : RNPv rs s) (Hrs_out : rs.outlb = s.gh.outlb)
    (Hrs_unst : rs.unst = s.gh.unst) (Hrs_clb : uint.Z rs.clb ≤ uint.Z s.logst.committed)
    (Hrnfl : RNFl rs s) :
    ⊢ rawNodeOwn rn rnv -∗ ownRaftPhysCV c c.voters rnv.raft' id s -∗
      ownStepGhost (GF := GF) γ (rs.mode.toG ⟨rs.capplied, rs.cfg, fp⟩) c id s -∗
      sdrOk rnv.raft' rs.mode -∗
      rnv.prevSoftSt' ↦□ sv -∗ hsRO rnv.prevHardSt' hprev -∗ rnv.stepsOnAdvance' ↦* steps -∗
      ownSliceCap Loc rnv.stepsOnAdvance' (DFrac.own 1) -∗
      pendList γ id steps rs.steps -∗
      isCommitted γ rs.delivered -∗
      storedRecs γ s.logst.prev s.logst.stored -∗
      ownRawNode γ rn id rs := by
  iintro Hrn Hphys Hghost #Hsdrf #Hsoft #Hhard Hsteps Hcap Hpend #Hdeliv #Hstrecs
  unfold ownRawNode
  iexists s, c, fp, rnv, sv, hprev, steps
  simp only [named]
  iframe Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hcap Hpend Hdeliv Hstrecs
  ipureintro
  exact ⟨Hwf, Hin, Hal, Hasync, Hdlen, Hunp, Hsnap, Hstok, Htrm, Hstor, Hpvoff, Hrs_out,
    Hrs_unst, Hrs_clb, Hrnfl⟩

/-! ### The static mode, as before (2026-10-14, stage B7 part 2)

In the static mode the struct's configuration has the ghost state's voters, not joint
(`CfgStatic`): the struct and the ghost state can be read as `ownRawNode` held them until
stage B7 part 2 -- `ownRaftPhys γ.reCfg` and `ownRaftGhost` -- for the proofs that are about
the static mode only (a shrinking `ApplyConfChange`, `node.go`'s loop). -/

/-- (2026-10-20, W4) In the static mode the node's configuration has no witness or the
cluster's (`ghostRestM`). -/
theorem ghostRest_static_wit (γ : RaftNames) (rs : RNState) (g : RGh) (c : CfgM) (id : w64)
    (s : NState) :
    ghostRest (GF := GF) γ (rs.mode.toG g) c id s ⊢
      ⌜rs.mode = .static → c.wit = W64 0 ∨ c.wit = γ.reWit⌝ ∗ ghostRest γ (rs.mode.toG g) c id s := by
  iintro H
  cases hm : rs.mode with
  | static =>
    rw [hm] at *
    simp only [RNMode.toG, ghostRest, ghostRestM]
    icases H with ⟨%Hn, %Hps, %Hc⟩
    isplitr; · ipureintro; exact fun _ => Hc.2.2
    ipureintro; exact ⟨Hn, Hps, Hc⟩
  | dyn dec c0 h0 h1 =>
    iframe H
    ipureintro; intro h; cases h

theorem ownRawNode_static_open (γ : RaftNames) (rs : RNState) (Hm : rs.mode = .static)
    -- (2026-10-20, witness support) a cluster without a witness: `ApplyConfChange`'s
    -- premise (the static mode's configuration change has no witness yet, NoWitReconf)
    (hw0 : γ.reWit = W64 0)
    (fp : List EntryM) (cf : CfgM) (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhysCV (GF := GF) cf cf.voters r id s -∗
      ownStepGhost γ (rs.mode.toG ⟨rs.capplied, rs.cfg, fp⟩) cf id s -∗
      ownRaftPhys γ.reCfg r id s ∗ ownRaftGhost γ id (toPState s) ∗
      -- (D19p, 2026-10-18) the tracker within the tracked bound
      ⌜TrackedOk γ (CfgM.simple γ.reCfg (domSet s.progress \ γ.reCfg)) id⌝ ∗
      -- (2026-10-19, D21 M3)
      ⌜NsLink γ s⌝ ∗
      -- (2026-10-20, witness support) `ghostRest`'s `PSubOk`
      ⌜PSubOk (toPState s)⌝ := by
  iintro Hphys Hghost
  rw [Hm]
  simp only [RNMode.toG, ownStepGhost, ghostRest, ghostRestM, GMode.isDyn]
  icases Hghost with ⟨Hghost, %Hnl, %Hps, %HC⟩
  have hw : cf.wit = W64 0 := by
    rcases HC.2.2 with h | h
    · exact h
    · rw [h, hw0]
  icases ownRaftPhysC_toPhys cf r id s HC.1.2.1 hw $$ Hphys with ⟨Hphys, %Hlrn⟩
  rw [HC.1.1] at Hlrn ⊢
  iframe Hphys Hghost
  isplitr
  · ipureintro
    exact TrackedOk.of_eq (by rw [CfgM.voters_simple, CfgStatic.voters HC.1])
      (by rw [Hlrn]; rfl) HC.2.1
  isplitr
  · ipureintro; exact Hnl
  ipureintro; exact Hps

theorem ownRawNode_intro_static (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState)
    (s : NState) (ps : PState) (rnv : RawNode) (sv : SoftState) (hprev : HardStateM)
    (steps : List Loc)
    (Hm : rs.mode = .static)
    (Hrel : NStateRel s ps) (Hin : id ∈ γ.reCfg) (Hasync : rnv.asyncStorageWrites' = false)
    (Hdlen : rs.delivered.length = (uint.Z s.logst.applying).toNat)
    (Hunp : rs.unpersisted = s.logst.unpersisted) (Hsnap : s.logst.snap = none)
    (Hstok : StepsOk s rs.steps)
    (Htrm : rs.term = s.term) (Hstor : rs.storage = s.logst.storage)
    (Hpvoff : RNPv rs s) (Hrs_out : rs.outlb = s.gh.outlb)
    (Hrs_unst : rs.unst = s.gh.unst) (Hrs_clb : uint.Z rs.clb ≤ uint.Z s.logst.committed)
    (Hrnfl : RNFl rs s)
    -- (D19p, 2026-10-18) the tracker within the ghost state's tracked bound
    (Htrk : TrackedOk γ (CfgM.simple γ.reCfg (domSet s.progress \ γ.reCfg)) id)
    -- (2026-10-19, D21 M3) the no-snapshot mode only with a bootstrap log
    (Hnl : NsLink γ s)
    -- (2026-10-20, witness support) `ghostRest`'s `PSubOk`
    (Hps : PSubOk (toPState s)) :
    ⊢ rawNodeOwn rn rnv -∗ ownRaftPhys γ.reCfg rnv.raft' id s -∗
      ownRaftGhost (GF := GF) γ id ps -∗ sdrOk rnv.raft' rs.mode -∗
      rnv.prevSoftSt' ↦□ sv -∗ hsRO rnv.prevHardSt' hprev -∗ rnv.stepsOnAdvance' ↦* steps -∗
      ownSliceCap Loc rnv.stepsOnAdvance' (DFrac.own 1) -∗
      pendList γ id steps rs.steps -∗
      isCommitted γ rs.delivered -∗
      storedRecs γ s.logst.prev s.logst.stored -∗
      ownRawNode γ rn id rs := by
  iintro Hrn Hphys Hghost #Hsdrf #Hsoft #Hhard Hsteps Hcap Hpend #Hdeliv #Hstrecs
  obtain ⟨rfl, Hwf⟩ := Hrel
  ihave %Hst := ownRaftGhost_static γ id _ $$ Hghost
  ihave Hphys := ownRaftPhys_toC' $$ Hphys
  ihave Hghost : ownStepGhost γ (rs.mode.toG ⟨rs.capplied, rs.cfg, []⟩)
      (CfgM.simple γ.reCfg (domSet s.progress \ γ.reCfg)) id s $$ [Hghost]
  · rw [Hm]
    simp only [RNMode.toG, ownStepGhost, ghostRest, ghostRestM, GMode.isDyn]
    iframe Hghost
    isplitr
    · ipureintro; exact Hnl
    isplitr
    · ipureintro; exact Hps
    ipureintro; exact ⟨CfgStatic.simple γ _ Hst, Htrk, .inl rfl⟩
  iapply ownRawNode_intro γ rn id rs s _ [] rnv sv hprev steps Hwf (fun _ => Hin) rfl Hasync Hdlen
    Hunp Hsnap Hstok Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb Hrnfl
    $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hcap Hpend Hdeliv Hstrecs

/-- `ownRawNode_intro_static` at any non-joint configuration `c` of the ghost state's voters
(2026-10-20, witness support: `RestartNode` at a witness conf state, `cfgW`), its witness none or
the cluster's (the static `ghostRestM`), the struct at `c`. -/
theorem ownRawNode_intro_staticC (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState)
    (s : NState) (ps : PState) (c : CfgM) (rnv : RawNode) (sv : SoftState) (hprev : HardStateM)
    (steps : List Loc)
    (Hm : rs.mode = .static)
    (Hrel : NStateRel s ps) (Hin : id ∈ γ.reCfg) (Hasync : rnv.asyncStorageWrites' = false)
    (Hdlen : rs.delivered.length = (uint.Z s.logst.applying).toNat)
    (Hunp : rs.unpersisted = s.logst.unpersisted) (Hsnap : s.logst.snap = none)
    (Hstok : StepsOk s rs.steps)
    (Htrm : rs.term = s.term) (Hstor : rs.storage = s.logst.storage)
    (Hpvoff : RNPv rs s) (Hrs_out : rs.outlb = s.gh.outlb)
    (Hrs_unst : rs.unst = s.gh.unst) (Hrs_clb : uint.Z rs.clb ≤ uint.Z s.logst.committed)
    (Hrnfl : RNFl rs s)
    (Hci : c.incoming = γ.reCfg) (Hco : c.outgoing = ∅) (Hal : c.autoLeave = false)
    (Hcw : c.wit = W64 0 ∨ c.wit = γ.reWit)
    (Htrk : TrackedOk γ c id)
    (Hnl : NsLink γ s)
    (Hps : PSubOk (toPState s)) :
    ⊢ rawNodeOwn rn rnv -∗ ownRaftPhysCV c c.voters rnv.raft' id s -∗
      ownRaftGhost (GF := GF) γ id ps -∗ sdrOk rnv.raft' rs.mode -∗
      rnv.prevSoftSt' ↦□ sv -∗ hsRO rnv.prevHardSt' hprev -∗ rnv.stepsOnAdvance' ↦* steps -∗
      ownSliceCap Loc rnv.stepsOnAdvance' (DFrac.own 1) -∗
      pendList γ id steps rs.steps -∗
      isCommitted γ rs.delivered -∗
      storedRecs γ s.logst.prev s.logst.stored -∗
      ownRawNode γ rn id rs := by
  iintro Hrn Hphys Hghost #Hsdrf #Hsoft #Hhard Hsteps Hcap Hpend #Hdeliv #Hstrecs
  obtain ⟨rfl, Hwf⟩ := Hrel
  ihave %Hst := ownRaftGhost_static γ id _ $$ Hghost
  ihave Hghost : ownStepGhost γ (rs.mode.toG ⟨rs.capplied, rs.cfg, []⟩) c id s $$ [Hghost]
  · rw [Hm]
    simp only [RNMode.toG, ownStepGhost, ghostRest, ghostRestM, GMode.isDyn]
    iframe Hghost
    isplitr
    · ipureintro; exact Hnl
    isplitr
    · ipureintro; exact Hps
    ipureintro; exact ⟨⟨Hci, Hco, Hst⟩, Htrk, Hcw⟩
  iapply ownRawNode_intro γ rn id rs s _ [] rnv sv hprev steps Hwf (fun _ => Hin) Hal Hasync Hdlen
    Hunp Hsnap Hstok Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb Hrnfl
    $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hcap Hpend Hdeliv Hstrecs

/-- The mode is the ghost state's (2026-10-14, stage B7 part 2): static exactly when `γ` is. -/
theorem ownRawNode_mode (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) :
    ⊢ ownRawNode (GF := GF) γ rn id rs -∗
      ⌜(rs.mode = .static ↔ γ.reDyn = none)⌝ ∗ ownRawNode γ rn id rs := by
  iintro H
  iNamed H
  iunfold ownStepGhost at Hghost
  icases Hghost with ⟨Hg, Hr⟩
  ihave %Hm := ownRaftGhost_mode γ id (toPState s) (md := (rs.mode.toG _).isDyn) $$ Hg
  ihave Hghost : ownStepGhost γ (rs.mode.toG ⟨rs.capplied, rs.cfg, fp⟩) cf id s $$ [Hg Hr]
  · iunfold ownStepGhost; iframe Hg Hr
  isplitr
  · ipureintro
    rw [RNMode.toG_isDyn] at Hm
    cases hm : rs.mode with
    | static => rw [hm] at Hm; simp [RNMode.isDyn] at Hm; simp [Hm]
    | dyn dec c0 h0 _ => rw [hm] at Hm; simp [RNMode.isDyn] at Hm; simp [Option.isSome_iff_ne_none.1 Hm]
  iapply ownRawNode_intro γ rn id rs s cf fp rnv sv hprev steps Hwf Hin Hal Hasync Hdlen Hunp Hsnap
    Hstok Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb Hrnfl
    $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstrecs

/-- (2026-10-17) In a cluster started from a bootstrap log (`StartNode`: `γ.reBoot ≠ []`) every
node is past term `0` (`ownLogGhost_boot`): a pre-vote request rejected at a node's own term
(`Term: r.Term`) is never of term `0`, which `send` refuses. -/
theorem ownStepGhost_boot_term (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) (s : NState)
    (P : Prop) (Hb : P → γ.reBoot ≠ []) :
    ownStepGhost (GF := GF) γ md c id s ⊢ ⌜P → 1 ≤ uint.Z s.term⌝ ∗ ownStepGhost γ md c id s := by
  apply persistent_entails_right
  iintro H
  by_cases hP : P
  · iunfold ownStepGhost at H
    icases H with ⟨Hg, -⟩
    iunfold ownRaftGhost at Hg
    icases Hg with ⟨%γv, %voted, %kl, H⟩
    iNamed H
    icases ownLogGhost_boot γ id (toPState s) kl $$ Hlg with ⟨%Hx, -⟩
    ipureintro
    exact fun _ => Hx.2 (Hb hP)
  · ipureintro; exact fun h => absurd h hP

/-- (2026-10-19, D21 M3) In the cluster's no-snapshot mode the outbox holds no `MsgSnap`: the
node's mode is the cluster's (`NsLink`) and its outbox has none in the mode (`LogNsOk`). -/
theorem ownRaftPhysC_nsOut (γ : RaftNames) (md : GMode) (c : CfgM) {V : GSet w64} (r : Loc)
    (id : w64) (s : NState) :
    ⊢ ownRaftPhysCV (GF := GF) c V r id s -∗ ownStepGhost γ md c id s -∗
      ⌜γ.reNoSnap = true → ∀ x ∈ s.outbox, x.ty ≠ .snap⌝ ∗ ownRaftPhysCV c V r id s ∗
        ownStepGhost γ md c id s := by
  iintro Hphys Hghost
  icases ownRaftPhysC_ns c r id s $$ Hphys with ⟨%Hnsl, -, Hphys⟩
  iunfold ownStepGhost at Hghost
  icases Hghost with ⟨Hg, Hr⟩
  icases ghostRest_nsLink γ md c id s $$ Hr with ⟨%Hnl, Hr⟩
  iframe Hphys
  isplitr
  · ipureintro
    intro h
    exact (Hnsl (by rw [Hnl.1]; exact h)).2.2.2
  iunfold ownStepGhost
  iframe Hg Hr

/-- (2026-10-19, D21 M3) A node with nothing committed is of a cluster with no bootstrap log
(`ownLogGhost_boot`), so not in the no-snapshot mode: what `RestartNode`'s fresh node is. -/
theorem ownRaftGhost_noSnap_of_commit (γ : RaftNames) (id : w64) (ps : PState) {md : Bool}
    (Hc : uint.Z ps.commit = 0) :
    ownRaftGhost (GF := GF) γ id ps md ⊢ ⌜γ.reNoSnap = false⌝ ∗ ownRaftGhost γ id ps md := by
  apply persistent_entails_right
  iintro H
  iunfold ownRaftGhost at H
  icases H with ⟨%γv, %voted, %kl, H⟩
  iNamed H
  icases ownLogGhost_boot γ id ps kl $$ Hlg with ⟨%Hx, -⟩
  ipureintro
  cases h : γ.reNoSnap
  · rfl
  · exfalso
    have Hne := RaftNames.noSnap_boot h
    have := List.length_pos_iff.mpr Hne
    have := Hx.1
    omega

/-- (2026-10-17) The term ceiling raised on the static-mode physical state (to close a node opened
at a later term: `Bootstrap`'s, `RestartNode`'s). -/
theorem ownRaftPhys_raise_tc (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (tc : w64)
    (Hle : uint.Z s.gh.tc ≤ uint.Z tc) :
    ⊢ ownRaftPhys (GF := GF) cfg r id s -∗
      ownRaftPhys cfg r id { s with gh := { s.gh with tc := tc } } := by
  iintro H
  ihave H := ownRaftPhys_toC' $$ H
  ihave H := ownRaftPhysC_raise_tc (c := CfgM.simple cfg (domSet s.progress \ cfg)) r id s tc Hle $$ H
  iapply ownRaftPhysC_toS
  iexact H

/-- (2026-10-19, D21 M3) The no-snapshot mode set to `b` on the static-mode physical state of a
node out of the mode (`Bootstrap`'s, at the cluster's `RaftNames.reNoSnap`): into it, a
non-leader with no pending snapshot, its log's boundary at most `1` and something committed, over
a storage that never compacts past `1` (`NsCap`; `ownRaftPhysC_set_ns`). (2026-10-19, D21 M2r)
Leader transfer (`NGhost.xf`, on since `newRaft`) set to the same: kept off in the mode, whose
node is past term `0` with nothing in its outbox; turned on otherwise (`ownRaftPhysC_xf_off`). -/
theorem ownRaftPhys_set_ns (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (b : Bool)
    (H0 : s.gh.ns = false) (H0x : s.gh.xf = true)
    (Hb : b = true → s.role ≠ .leader ∧ s.logst.snap = none ∧ uint.Z s.logst.prev.index' ≤ 1 ∧
      1 ≤ uint.Z s.logst.committed ∧ ∀ m ∈ s.outbox, m.ty ≠ .snap)
    (Hbt : b = true → s.term ≠ W64 0 ∧ s.outbox = []) :
    ⊢ NsCap (GF := GF) b s.logst.storage -∗ ownRaftPhys cfg r id s -∗
      ownRaftPhys cfg r id { s with gh := { s.gh with ns := b, xf := b } } := by
  iintro #Hcap H
  cases b with
  | false =>
    have He : ({ s with gh := { s.gh with ns := false, xf := false } } : NState) =
        { s with gh := { s.gh with xf := false } } := by
      rw [← H0]
    rw [He]
    ihave H := ownRaftPhys_toC' $$ H
    ihave H := ownRaftPhysC_xf_off (c := CfgM.simple cfg (domSet s.progress \ cfg)) r id s H0 $$ H
    iapply ownRaftPhysC_toS
    iexact H
  | true =>
    obtain ⟨Hr, Hsn, Hp, Hc, Ho⟩ := Hb rfl
    obtain ⟨Ht, Hob⟩ := Hbt rfl
    have He : ({ s with gh := { s.gh with ns := true, xf := true } } : NState) =
        { s with gh := { s.gh with ns := true } } := by
      rw [← H0x]
    rw [He]
    ihave H := ownRaftPhys_toC' $$ H
    iunfold NsCap at Hcap
    ihave #Hc1 := Hcap $$ %rfl
    ihave H := ownRaftPhysC_set_ns (c := CfgM.simple cfg (domSet s.progress \ cfg)) r id s Hr Hsn Hp
      Hc Ho H0x Ht Hob $$ Hc1 H
    iapply ownRaftPhysC_toS
    iexact H

/-- (2026-10-19, D21 M2r) Leader transfer turned on (`ownRaftPhysC_xf_off`) on the static-mode
physical state, outside the no-snapshot mode. -/
theorem ownRaftPhys_xf_off (cfg : GSet w64) (r : Loc) (id : w64) (s : NState)
    (H0 : s.gh.ns = false) :
    ⊢ ownRaftPhys (GF := GF) cfg r id s -∗
      ownRaftPhys cfg r id { s with gh := { s.gh with xf := false } } := by
  iintro H
  ihave H := ownRaftPhys_toC' $$ H
  ihave H := ownRaftPhysC_xf_off (c := CfgM.simple cfg (domSet s.progress \ cfg)) r id s H0 $$ H
  iapply ownRaftPhysC_toS
  iexact H

/-- (2026-10-17) The term ceiling raised: a ghost step the client takes, with the budget for the
new ceiling, before a step that may queue messages of a later term (a received pre-vote request's,
a pre-campaign's, a transfer's campaign). -/
theorem ownRawNode_raise_tc (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (tc : w64)
    (Hle : uint.Z rs.tc ≤ uint.Z tc) :
    ⊢ ownRawNode (GF := GF) γ rn id rs -∗ ownRawNode γ rn id { rs with tc := tc } := by
  iintro H
  iNamed H
  have Hle' : uint.Z s.gh.tc ≤ uint.Z tc := by rw [← Hpvoff.2.1]; exact Hle
  ihave Hphys := ownRaftPhysC_raise_tc cf _ id s tc Hle' $$ Hphys
  ihave Hghost := ownStepGhost_congr γ _ cf id (s := s)
    (s' := { s with gh := { s.gh with tc := tc } }) rfl rfl rfl rfl $$ Hghost
  obtain ⟨H1, -, H3, H4⟩ := Hpvoff
  iapply ownRawNode_intro γ rn id { rs with tc := tc } { s with gh := { s.gh with tc := tc } } cf fp
    rnv sv hprev steps Hwf Hin Hal Hasync Hdlen Hunp Hsnap
    (stepsOk_mono s _ _ rfl ⟨rfl, rfl⟩ (Int.le_refl _) rfl Hle' Hstok) Htrm Hstor
    ⟨H1, rfl, Int.le_trans H3 Hle', fun h => Int.le_trans (H4 h) Hle'⟩ Hrs_out Hrs_unst Hrs_clb Hrnfl
    $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstrecs

/-- (2026-10-17) The term is within the ceiling. -/
theorem ownRawNode_term_tc (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) :
    ⊢ ownRawNode (GF := GF) γ rn id rs -∗
      ⌜uint.Z rs.term ≤ uint.Z rs.tc⌝ ∗ ownRawNode γ rn id rs := by
  iintro H
  iNamed H
  isplitr
  · ipureintro; rw [Htrm, Hpvoff.2.1]; exact Hpvoff.2.2.1
  iapply ownRawNode_intro γ rn id rs s cf fp rnv sv hprev steps Hwf Hin Hal Hasync Hdlen Hunp Hsnap
    Hstok Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb Hrnfl
    $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstrecs

/-- The storage handshake, at the RawNode (2026-10-10; until then `ownRawNode_persist`,
which lent the client the storage itself): the receipt of the application's append of
the entries the last `Ready` handed out (`appendReceipt`, for the node's storage) is
absorbed into the log's storage (`ownRaftLog_absorb`); afterwards nothing is
unpersisted. The right to append came with the `Ready` (`appendRight`); in between the
node may be stepped, ticked, or asked to propose or campaign, while the application
appends on its own. -/
theorem ownRawNode_appended (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) :
    ⊢ ownRawNode (GF := GF) γ rn id rs -∗ appendReceipt rs.storage rs.unpersisted ==∗
      ownRawNode γ rn id { rs with unpersisted := [] } := by
  iintro H Hr
  iunfold appendReceipt at Hr
  icases Hr with (%Hnil | ⟨%σa, Htok⟩)
  · have Hrs : { rs with unpersisted := [] } = rs := by
      cases rs; simp only at Hnil ⊢; rw [Hnil]
    rw [Hrs]
    imodintro
    iexact H
  iNamed H
  ihave Htok : appendedTok s.logst.storage σa s.logst.unpersisted $$ [Htok]
  · rw [← Hstor, ← Hunp]; iexact Htok
  icases ownRaftPhysC_log_at cf rnv.raft' id s $$ Hphys with ⟨Hlog, %Hgh0, Hlback⟩
  imod ownRaftLog_absorb s.log s.logst σa $$ Hlog Htok with Hlog
  ihave Hphys := Hlback $$ %_ Hlog %(LogGhOk.of_fields Hgh0 rfl rfl rfl rfl rfl)
    %(fun _ => logLast_le_of_fields rfl rfl rfl)
  ihave Hghost := ownStepGhost_congr γ _ cf id (s := s)
    (s' := { s with logst := { s.logst with unpersisted := [] } }) rfl rfl rfl rfl $$ Hghost
  imodintro
  iapply ownRawNode_intro γ rn id { rs with unpersisted := [] }
    { s with logst := { s.logst with unpersisted := [] } } cf fp rnv sv hprev steps Hwf Hin Hal Hasync
    Hdlen rfl Hsnap
    (stepsOk_mono s _ rs.steps rfl ⟨rfl, rfl⟩ (Int.le_refl _) rfl (Int.le_refl _) Hstok)
    Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb Hrnfl
    $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstrecs

/-- (D19i part 1) **Raising the floor** to `applying` -- the committed log handed out,
`delivered` -- with nothing unpersisted: the client (`node.go`, when the application's `Advance`
is handed over) gets the storage's floor witness, the application's right to compact and snapshot
up to it, and the node is marked raised (`RNState.flw`) until `Advance` moves `applied` there. -/
theorem ownRawNode_raise_floor (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState)
    (Hunp0 : rs.unpersisted = []) :
    ⊢ ownRawNode (GF := GF) γ rn id rs ==∗
      ownRawNode γ rn id { rs with flw := true } ∗
      ∃ x : w64, ⌜uint.Z x = (rs.delivered.length : Int)⌝ ∗ storFloor rs.storage x := by
  iintro H
  iNamed H
  icases ownRaftPhysC_log_at cf rnv.raft' id s $$ Hphys with ⟨Hlog, %Hgh0, Hlback⟩
  icases ownRaftLog_fl _ _ $$ Hlog with ⟨%Hflb, Hlog⟩
  imod ownRaftLog_raise_floor s.log s.logst s.logst.applying ⟨Hflb.1, Int.le_refl _⟩
    (Hunp ▸ Hunp0) Hsnap $$ Hlog with ⟨Hlog, Hfw⟩
  ihave Hphys := Hlback $$ %_ Hlog %(LogGhOk.of_fields Hgh0 rfl rfl rfl rfl rfl)
    %(fun _ => logLast_le_of_fields rfl rfl rfl)
  ihave Hghost := ownStepGhost_congr γ _ cf id (s := s)
    (s' := { s with logst := { s.logst with fl := s.logst.applying } }) rfl rfl rfl rfl $$ Hghost
  imodintro
  isplitr [Hfw]
  · iapply ownRawNode_intro γ rn id { rs with flw := true }
      { s with logst := { s.logst with fl := s.logst.applying } } cf fp rnv sv hprev steps Hwf Hin Hal
      Hasync Hdlen Hunp Hsnap
      (stepsOk_mono s _ rs.steps rfl ⟨rfl, rfl⟩ (Int.le_refl _) rfl (Int.le_refl _) Hstok)
      Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb
      ⟨fun h => by simp at h, Hrnfl.2⟩
      $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstrecs
  iexists s.logst.applying
  isplitr
  · ipureintro; have := uint_Z_nonneg s.logst.applying; rw [Hdlen]; omega
  rw [Hstor]
  iexact Hfw

end rawnode

end EtcdGrove
end Perennial

-- Projection lemmas, `@[simp, word_unfold]` (ProjSimps.lean). (2026-10-16, stage R5: the
-- hard and soft state records are `InvRaftPhys.lean`'s, their projection lemmas still here.)
proj_simps Perennial.EtcdGrove.hsAbs Perennial.EtcdGrove.nodeHardstate Perennial.EtcdGrove.nodeSoftstate
proj_simps Perennial.EtcdGrove.appendAckM Perennial.EtcdGrove.applyAckM
