/-
Port of `election_proof/inv_rawnode.v` (at 857d09190), reworked on 2026-10-09.

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
2026-10-10) pre-vote off (`s.prevote = false`, `NewRawNode` takes `Config.PreVote` unset):
then every queued message is of a term at most the node's (`OutTermOk`), which
`readyWithoutAccept` reports of the messages it hands out.

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
`Pending.self`, `.appendAck`, `.applyAck`. `hs_abs`, `hs_empty_abs`, `node_hardstate`,
`node_softstate`, `hardstate_val`, `softstate_val`, `append_ack_msg`, `apply_ack_msg`,
`pending_rel`, `pending_own`, `own_RawNode` are `hsAbs`, `hsEmptyAbs`, `nodeHardstate`,
`nodeSoftstate`, `hardstateVal`, `softstateVal`, `appendAckMsg`, `applyAckMsg`,
`pendingRel`, `pendingOwn`, `ownRawNode`; the `EqDecision` instances are `deriving
DecidableEq`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvReadylog
-- (2026-10-14, reconfiguration stage B7 part 2) the ghost modes
public import Proof.go_etcd_io.raft.v3.StepGhostMode

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-! ## The RawNode's state -/

structure HardSt where
  term : w64
  vote : w64
  commit : w64
deriving DecidableEq

structure SoftSt where
  lead : w64
  /-- `StateType` -/
  state : w64
deriving DecidableEq

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
  | applyAck (ents : List raftpb.Entry)

/-- The mode of a `RawNode`'s ghost state (2026-10-14, reconfiguration stage B7 part 2): static
(the voters fixed at `γ.reCfg`, conf-change entries data) or dynamic (the configuration changes
by applied conf entries: a decoder `dec` and an initial configuration `c0`; B5's
`ownRaftGhostR`). -/
inductive RNMode [FfiSyntax] where
  | static
  | dyn (dec : CCDec) (c0 : CCState) (h0 : CfgOk c0)

/-- What the application sees of a `RawNode` (2026-10-09). -/
structure RNState [FfiSyntax] where
  /-- The committed log handed out so far, from the start (as `isCommitted` takes it):
  every `Ready`'s `CommittedEntries`, in order, after the entries applied before the
  node was built. -/
  delivered : List raftpb.Entry
  /-- The entries `Ready` handed out (`Ready.Entries`) that the application must still
  append to the `Storage` (and give the receipt back: `ownRawNode_appended`). -/
  unpersisted : List raftpb.Entry
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

section defs
variable [FfiSyntax]

def RNMode.isDyn : RNMode → Bool
  | .static => false
  | .dyn .. => true

/-- The ghost mode `raft.Step` keeps for a `RawNode` in mode `md`, with the ghost part `g`. -/
def RNMode.toG : RNMode → RGh → GMode
  | .static, _ => .static
  | .dyn dec c0 h0, g => .dyn dec c0 h0 g

theorem RNMode.toG_isDyn (md : RNMode) (g : RGh) : (md.toG g).isDyn = md.isDyn := by
  cases md <;> rfl

/-- The voters the node's quorums are taken in, as the client sees them: `γ.reCfg` in the
static mode, the configuration in use in the dynamic one. -/
def RNState.vcfg (γ : RaftNames) (rs : RNState) : CfgM :=
  match rs.mode with
  | .static => CfgM.simple γ.reCfg ∅
  | .dyn .. => rs.cfg.cfg

/-- No conf entry in a range of a prefix is none in the longer log. -/
theorem NoConfIn_prefix {D F : List raftpb.Entry} {lo hi : Nat} (hp : D <+: F)
    (hhi : hi ≤ D.length) (h : NoConfIn D lo hi) : NoConfIn F lo hi := by
  intro k e hk1 hk2 he
  apply h k e hk1 hk2
  obtain ⟨t, rfl⟩ := hp
  rw [List.getElem?_append_left (by omega)] at he
  exact he

/-- A step in the mode of a `RawNode` (`RNMode.toG`), with the configuration index `ca`: the
mode afterwards is the node's at some `ca'`, moved only by a `MsgStorageApplyResp`, to at
most the new `applied` (`CidxMove`), and not at all in the static mode. -/
theorem RNMode.stepOut_ca {mode : RNMode} {ca : Nat} {cfg : CCState} {fp : List raftpb.Entry}
    {c : CfgM} {id : w64} {m : raftpb.Message} {s s' : NState} {md' : GMode}
    (H : (mode.toG ⟨ca, cfg, fp⟩).StepOut c id m s s' md') :
    ∃ ca', md' = mode.toG ⟨ca', cfg, fp⟩ ∧ ca ≤ ca' ∧
      ca' ≤ max ca (uint.nat s'.logst.applied) ∧ (mode = .static → ca' = ca) ∧
      (m.Type' ≠ MsgStorageApplyResp → ca' = ca) := by
  cases mode with
  | static =>
    exact ⟨ca, H.1, Nat.le_refl _, Nat.le_max_left _ _, fun _ => rfl, fun _ => rfl⟩
  | dyn dec c0 h0 =>
    obtain ⟨cidx', Hcm, rfl, -⟩ := H
    refine ⟨cidx', rfl, ?_, ?_, fun h => (by cases h), fun hm => ?_⟩
    · rcases Hcm with h | ⟨-, h⟩
      · rw [h]; exact Nat.le_refl _
      · rw [h]; exact Nat.le_max_left _ _
    · rcases Hcm with h | ⟨-, h⟩
      · rw [h]; exact Nat.le_max_left _ _
      · rw [h]; exact Nat.le_refl _
    · rcases Hcm with h | ⟨h, -⟩
      · exact h
      · exact absurd h hm

/-- A configuration in which the node is not its own quorum (`raft.Step`'s premise for a
read-index request: `IsSingleton`'s immediate answer is out of scope). -/
def NotSingleton (c : CfgM) : Prop := ¬ (GMap.size c.incoming = 1 ∧ GMap.size c.outgoing = 0)

/-- In the static mode, more than one voter is no singleton configuration. -/
theorem notSingleton_static {γ : RaftNames} {rs : RNState} (hm : rs.mode = .static)
    (h : 1 < GMap.size γ.reCfg) : NotSingleton (rs.vcfg γ) := by
  unfold NotSingleton RNState.vcfg; rw [hm]; simp only [CfgM.simple]; omega


def hsAbs (h : raftpb.HardState) : HardSt :=
  ⟨h.Term', h.Vote', h.Commit'⟩

def hsEmptyAbs (h : HardSt) : Bool :=
  decide (h.term = W64 0 ∧ h.vote = W64 0 ∧ h.commit = W64 0)

/-- `r.hardState()` and `r.softState()` of a node in physical state `s`. -/
def nodeHardstate (s : NState) : HardSt :=
  ⟨s.term, s.vote, s.logst.committed⟩
def nodeSoftstate (s : NState) : SoftSt :=
  ⟨s.lead, stateW64 s.role⟩

def hardstateVal (h : HardSt) : raftpb.HardState :=
  raftpb.HardState.mk h.term h.vote h.commit
def softstateVal (h : SoftSt) : SoftState :=
  SoftState.mk h.lead h.state

/-- The two local messages, as `newStorageAppendRespMsg` and `newStorageApplyRespMsg`
build them (with synchronous writes and no pending snapshot). -/
def appendAckMsg (id t : w64) (e : entryID) : raftpb.Message :=
  raftpb.Message.mk MsgStorageAppendResp id LocalAppendThread t
    e.term' e.index' slice.nil (W64 0) (W64 0) null false (W64 0) slice.nil slice.nil

def applyAckMsg (id : w64) (sl : GoSlice) : raftpb.Message :=
  raftpb.Message.mk MsgStorageApplyResp id LocalApplyThread (W64 0) (W64 0) (W64 0) sl
    (W64 0) (W64 0) null false (W64 0) slice.nil slice.nil

/-- A self-addressed response as `Advance` steps it (2026-10-10): what `Step`'s spec asks
of a `MsgVoteResp`, `MsgPreVoteResp` or `MsgAppResp` to the node itself, beyond its
term's bound (`PendingOk`) -- from and to the node, a nonzero term, no entries and no
context (`nil`), and a `MsgAppResp` that does not reject. `AAMsgOk` (`InvRaftPhys.lean`)
of a self-addressed message of `msgsAfterAppend`, without the term bound. -/
def SelfMsgOk (id : w64) (m : raftpb.Message) : Prop :=
  (m.Type' = MsgAppResp ∨ m.Type' = MsgVoteResp ∨ m.Type' = MsgPreVoteResp) ∧
  m.From' = id ∧ m.To' = id ∧ m.Term' ≠ W64 0 ∧ m.Entries' = slice.nil ∧
  m.Context' = slice.nil ∧ (m.Type' = MsgAppResp → m.Reject' = false)

/-- The pending step `acceptReady` queues for a self-addressed message. -/
def selfPending (m : raftpb.Message) : Pending :=
  .self (decide (m.Type' = MsgPreVoteResp)) m.Term'

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
      -- (2026-10-10) with pre-vote off, not a pre-vote response (`OutTermOk`)
      (s.prevote = false → pv = false)
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
    (Hpv : s'.prevote = s.prevote := by first | rfl | assumption) :
    StepsOk s steps → StepsOk s' steps := by
  have Hall : ∀ l : List Pending, (∀ p ∈ l, ApplyAckOk s p) → ∀ p ∈ l, ApplyAckOk s' p :=
    fun l H p Hp => applyAckOk_mono s s' p Hc Ha (H p Hp)
  induction steps with
  | nil => intro _; trivial
  | cons p rest IH =>
    cases p with
    | self pv t =>
      intro ⟨⟨H1, H1'⟩, H2⟩
      exact ⟨⟨by omega, by rw [Hpv]; exact H1'⟩, IH H2⟩
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
    (Hpv : s'.prevote = s.prevote := by first | rfl | assumption) :
    StepsOk s steps → StepsOk s' steps :=
  stepsOk_mono_le s s' steps (by rw [Ht]; exact Int.le_refl _) Hst Hc Ha Hpv

/-- What the storage holds agrees with the log up to an entry both have (2026-10-10):
Log Matching between two logs with records (`RecsAgree`, `logRecs_agree`), one of
which -- `L`, the log of the last `Ready`, which the storage holds -- ends at `e`. This
is why an acknowledgement of `e` that hits (`StableHit`: the log has `e.term` at
`e.index`) moves stable only entries the storage has, even after `MsgApp`s truncated
the log below `e` and put `e` back. -/
theorem stored_agree (b : entryID) (L F : List raftpb.Entry) (e : entryID)
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

end defs

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- What a pending step owns: the capacity of a `MsgStorageApplyResp`'s `Entries` --
`Ready`'s `CommittedEntries` slice, which `Step`'s spec asks to own and which `Ready`
therefore keeps for the node rather than handing to the application. -/
def pendingOwn (m : raftpb.Message) (p : Pending) : IProp GF :=
  match p with
  | .applyAck _ => ownSliceCap raftpb.Entry m.Entries' (DFrac.own 1)
  | _ => iprop(True)

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
  ihave %Hul := ownSlice_len $$ Huents
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
      Hpaused Hasz Hamx Hstor Hpend rfl rfl $$ Hl HisStorage HStorage Husnap Huents Huents_cap Hl_logger
      Hu_logger

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

/-- What `GMode.Pre` needs of the node, for any message but a snapshot or a storage-apply
acknowledgement (2026-10-14, stage B7 part 2). -/
def PreFacts (s : NState) : Prop :=
  s.role ≠ .preCandidate ∧ plogLastIndexZ (toPState s).base (toPState s).log + 2 ^ 61 < 2 ^ 64

theorem GMode.Pre.of_facts {md : GMode} {m : raftpb.Message} {ents : List raftpb.Entry}
    {s : NState} (h : PreFacts s) (h1 : m.Type' ≠ MsgSnap) (h3 : m.Type' ≠ MsgStorageApplyResp) :
    md.Pre m ents s := by
  cases md with
  | static => trivial
  | dyn dec c0 h0 g => exact ⟨h1, h.1, fun h' => absurd h' h3, fun _ => h.2⟩

/-- ... read off the struct, at a node with pre-vote off. -/
theorem ownRaftPhysC_preFacts (c : CfgM) {V : GSet w64} (r : Loc) (id : w64) (s : NState)
    (Hpv : s.prevote = false) :
    ⊢ ownRaftPhysCV (GF := GF) c V r id s -∗ ⌜PreFacts s⌝ ∗ ownRaftPhysCV c V r id s := by
  iintro H
  icases ownRaftPhysC_precand c r id s $$ H with ⟨%Hpc, H⟩
  icases ownRaftPhysC_last_bound c r id s $$ H with ⟨%Hb, H⟩
  iframe H
  ipureintro
  refine ⟨fun h => ?_, Hb⟩
  have := Hpc h; rw [Hpv] at this; cases this

/-- The dynamic mode's premises of a step of `raft.Step` (`GMode.Pre`) for a message that is
no snapshot and no storage-apply acknowledgement, at a node with pre-vote off (2026-10-14,
stage B7 part 2): no pre-candidate (`ownRaftPhysC_precand`), and for a proposal the log's
room (`ownRaftPhysC_last_bound`). -/
theorem ownRaftPhysC_pre (c : CfgM) {V : GSet w64} (r : Loc) (id : w64) (s : NState)
    (md : GMode) (m : raftpb.Message) (ents : List raftpb.Entry) (Hpv : s.prevote = false)
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
    refine ⟨h1, fun h => ?_, fun h => absurd h h3, fun _ => Hb⟩
    have := Hpc h; rw [Hpv] at this; cases this

end proof

section rawnode
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
-- `hlc := HasLC.hasLC`: the predicate holds the ghost state (`ownRaftGhost`), as in
-- `Spec/raft__Step.lean`
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The physical message queued for a pending step. A self-addressed response
(2026-10-10): `SelfMsgOk`, its term and type as `Pending.self` records them, and its
abstraction legitimately sent (`isMessage`, from the outbox `Ready` drained) -- what
`Step`'s spec asks of it besides the term bound (`PendingOk`); it has no entries, so the
abstraction is at `[]`. (Until 2026-10-10 `msgAbs m a ∗ ⌜m.To' = id⌝`, which `Step`'s
spec could not use.) -/
def pendingRel (γ : RaftNames) (id : w64) (m : raftpb.Message) (p : Pending) : IProp GF :=
  match p with
  | .self pv t => iprop(⌜SelfMsgOk id m ∧ m.Term' = t ∧ pv = decide (m.Type' = MsgPreVoteResp)⌝ ∗
      □ (∀ ty, ⌜mtypeOf m.Type' = some ty⌝ -∗ isMessage γ (absMsg ty m [])))
  | .appendAck t e => iprop(⌜m = appendAckMsg id t e⌝)
  | .applyAck ents => iprop(∃ sl, ⌜m = applyAckMsg id sl⌝ ∗ sl ↦*□ ents)

instance pendingRel_pers (γ : RaftNames) (id : w64) (m : raftpb.Message) (p : Pending) :
    Persistent (pendingRel (GF := GF) γ id m p) := by
  cases p <;> unfold pendingRel <;> infer_instance

/-- A message `Ready` hands to the application to send: what it contributes to the
protocol's messages (`msgAbs`: nothing, for a type the protocol does not describe) was
legitimately sent (`isMessage`). -/
def isRaftMsg (γ : RaftNames) (m : raftpb.Message) : IProp GF :=
  iprop(∃ a, msgAbs m a ∗ [∗list] x ∈ a.toList, isMessage γ x)

instance isRaftMsg_pers (γ : RaftNames) (m : raftpb.Message) :
    Persistent (isRaftMsg (GF := GF) γ m) := by
  unfold isRaftMsg; infer_instance

/-- The records of what the storage holds (2026-10-10): `L` (after `b`) is a log with
records (`logRecs`), as `ownLogGhost` keeps of the node's log; `ownRawNode` keeps it of
`stored`, which a `Ready` sets to the log (`ownRaftGhost_storedRecs`), so that a later
log with records can be matched against it (`stableOk_of_stored`). -/
def storedRecs (γ : RaftNames) (b : entryID) (L : List raftpb.Entry) : IProp GF :=
  iprop(⌜PlogWf b L⌝ ∗ logRecs γ b L)

instance storedRecs_pers (γ : RaftNames) (b : entryID) (L : List raftpb.Entry) :
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
theorem storedRecs_eq (γ : RaftNames) (b b' : entryID) (L L' : List raftpb.Entry)
    (Hb : b' = b) (HL : L' = L) :
    ⊢ storedRecs (GF := GF) γ b L -∗ storedRecs γ b' L' := by
  subst Hb HL; iintro H; iexact H

/-! ## The `RawNode` struct, with `raft` shared (2026-10-10)

The `AccessStrict` instances for `rawNodeOwn` are scoped (`open RawNodeOwnAccess`): the
`AccessStrict` classes' last parameters are `outParam`s, so a global instance would be
tried for a field of a whole-struct points-to as well (`NewRawNode`'s) and win.

`rawNodeOwn l v` is `l ↦ v` with the field nobody writes after `NewRawNode` -- `raft`, the
pointer to the raft struct -- persistent: `node.go`'s `Tick` reads `n.rn.raft` while `run`
owns the node (`raftOwn`, `InvRaftPhys.lean`, for the raft struct's own fields). -/
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

scoped instance (priority := high) rawNodeOwn_access_store_prevHardSt (l : Loc) (v : RawNode) (x : raftpb.HardState) :
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
theorem ownStepGhost_vcfg (γ : RaftNames) (rs : RNState) (fp : List raftpb.Entry) (c : CfgM)
    (id : w64) (s : NState) :
    ⊢ ownStepGhost (GF := GF) γ (rs.mode.toG ⟨rs.capplied, rs.cfg, fp⟩) c id s -∗
      ⌜c.incoming = (rs.vcfg γ).incoming ∧ c.outgoing = (rs.vcfg γ).outgoing⌝ ∗
      ownStepGhost γ (rs.mode.toG ⟨rs.capplied, rs.cfg, fp⟩) c id s := by
  iintro H
  unfold RNState.vcfg
  cases hm : rs.mode with
  | static =>
    simp only [hm, RNMode.toG, ownStepGhost, ghostRest]
    icases H with ⟨Hg, %HC⟩
    iframe Hg
    ipureintro
    exact ⟨⟨HC.1, HC.2.1⟩, HC⟩
  | dyn dec c0 h0 =>
    simp only [hm, RNMode.toG, ownStepGhost, ghostRest]
    icases H with ⟨Hg, %HC, Hr⟩
    iframe Hg Hr
    ipureintro
    have hc := HC.2.1
    refine ⟨⟨by rw [← hc], by rw [← hc]⟩, HC⟩

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
    (g : RGh) (c : CfgM) (id : w64) (s : NState) (D : List raftpb.Entry)
    (Hlen : (D.length : Int) ≤ uint.Z s.logst.committed) :
    ⊢ isCommitted γ D -∗ ownStepGhost (GF := GF) γ (.dyn dec c0 h0 g) c id s -∗
      ⌜D <+: (rOf s g).full⌝ ∗ ownStepGhost γ (.dyn dec c0 h0 g) c id s := by
  iintro #HD H
  iunfold ownStepGhost at H
  icases H with ⟨Hg, Hr⟩
  icases (entails_wand (persistent_entails_left (ownRaftGhost_cmt γ id (toPState s)))) $$ Hg
    with ⟨Hg, %fp', %Hf', #Hfr', #Hc⟩
  iunfold ghostRest at Hr
  icases Hr with ⟨%HC, #Hfr, Hcamp⟩
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

/-- See the file header. `s` is the node's physical state, `c` the configuration the struct is
at, `fp` the ghost full prefix (the dynamic mode's ghost part is `⟨rs.capplied, rs.cfg, fp⟩`);
`delivered` is the committed log up to `applying` (`isCommitted_agree` makes it the one such
list), `unpersisted` the log's. Since 2026-10-14 (reconfiguration stage B7 part 2) in either
mode (`rs.mode`): the struct at any configuration (`ownRaftPhysCV c`) and the ghost state as
`raft.Step` keeps it (`ownStepGhost`), with `NStateWf` for `NStateRel`. -/
def ownRawNode (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) : IProp GF :=
  iprop(∃ (s : NState) (cf : CfgM) (fp : List raftpb.Entry) (rnv : RawNode) (sv : SoftState)
      (steps : List raftpb.Message),
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
  -- or a `Ready.SoftState`), held read-only; `prevHardSt` is a value of `rnv`
  "#Hsoft" ∷ rnv.prevSoftSt' ↦□ sv ∗
  "Hsteps" ∷ rnv.stepsOnAdvance' ↦* steps ∗
  "Hsteps_cap" ∷ ownSliceCap raftpb.Message rnv.stepsOnAdvance' (DFrac.own 1) ∗
  "#Hpend" ∷ ([∗list] _k ↦ m;p ∈ steps;rs.steps, pendingRel γ id m p) ∗
  "Hpown" ∷ ([∗list] _k ↦ m;p ∈ steps;rs.steps, pendingOwn m p) ∗
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
  -- scope: pre-vote off (2026-10-10; `Config.PreVote` unset, `NewRawNode` copies it to
  -- `r.preVote`, never written again): pre-vote is an optimization, out of scope. With
  -- it off every message the node queues is of a term at most its own (`OutTermOk`), and
  -- (2026-10-14) the node is never a pre-candidate (`ownRaftPhysC_precand`)
  "%Hpvoff" ∷ ⌜s.prevote = false⌝ ∗
  -- the lower bounds for `node.go` (2026-10-10, `RNState.outlb`)
  "%Hrs_out" ∷ ⌜rs.outlb = s.gh.outlb⌝ ∗
  "%Hrs_unst" ∷ ⌜rs.unst = s.gh.unst⌝ ∗
  "%Hrs_clb" ∷ ⌜uint.Z rs.clb ≤ uint.Z s.logst.committed⌝)

/-- Closing the predicate; the pure premises are first, the resources in the order of
the definition. -/
theorem ownRawNode_intro (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState)
    (s : NState) (c : CfgM) (fp : List raftpb.Entry) (rnv : RawNode) (sv : SoftState)
    (steps : List raftpb.Message)
    (Hwf : NStateWf s) (Hin : rs.mode = .static → id ∈ γ.reCfg) (Hal : c.autoLeave = false)
    (Hasync : rnv.asyncStorageWrites' = false)
    (Hdlen : rs.delivered.length = (uint.Z s.logst.applying).toNat)
    (Hunp : rs.unpersisted = s.logst.unpersisted) (Hsnap : s.logst.snap = none)
    (Hstok : StepsOk s rs.steps)
    (Htrm : rs.term = s.term) (Hstor : rs.storage = s.logst.storage)
    (Hpvoff : s.prevote = false) (Hrs_out : rs.outlb = s.gh.outlb)
    (Hrs_unst : rs.unst = s.gh.unst) (Hrs_clb : uint.Z rs.clb ≤ uint.Z s.logst.committed) :
    ⊢ rawNodeOwn rn rnv -∗ ownRaftPhysCV c c.voters rnv.raft' id s -∗
      ownStepGhost (GF := GF) γ (rs.mode.toG ⟨rs.capplied, rs.cfg, fp⟩) c id s -∗
      sdrOk rnv.raft' rs.mode -∗
      rnv.prevSoftSt' ↦□ sv -∗ rnv.stepsOnAdvance' ↦* steps -∗
      ownSliceCap raftpb.Message rnv.stepsOnAdvance' (DFrac.own 1) -∗
      ([∗list] _k ↦ m;p ∈ steps;rs.steps, pendingRel γ id m p) -∗
      ([∗list] _k ↦ m;p ∈ steps;rs.steps, pendingOwn m p) -∗
      isCommitted γ rs.delivered -∗
      storedRecs γ s.logst.prev s.logst.stored -∗
      ownRawNode γ rn id rs := by
  iintro Hrn Hphys Hghost #Hsdrf #Hsoft Hsteps Hcap #Hpend Hpown #Hdeliv #Hstrecs
  unfold ownRawNode
  iexists s, c, fp, rnv, sv, steps
  simp only [named]
  iframe Hrn Hphys Hghost Hsdrf Hsoft Hsteps Hcap Hpend Hpown Hdeliv Hstrecs
  ipureintro
  exact ⟨Hwf, Hin, Hal, Hasync, Hdlen, Hunp, Hsnap, Hstok, Htrm, Hstor, Hpvoff, Hrs_out,
    Hrs_unst, Hrs_clb⟩

/-! ### The static mode, as before (2026-10-14, stage B7 part 2)

In the static mode the struct's configuration has the ghost state's voters, not joint
(`CfgStatic`): the struct and the ghost state can be read as `ownRawNode` held them until
stage B7 part 2 -- `ownRaftPhys γ.reCfg` and `ownRaftGhost` -- for the proofs that are about
the static mode only (a shrinking `ApplyConfChange`, `node.go`'s loop). -/

theorem ownRawNode_static_open (γ : RaftNames) (rs : RNState) (Hm : rs.mode = .static)
    (fp : List raftpb.Entry) (cf : CfgM) (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhysCV (GF := GF) cf cf.voters r id s -∗
      ownStepGhost γ (rs.mode.toG ⟨rs.capplied, rs.cfg, fp⟩) cf id s -∗
      ownRaftPhys γ.reCfg r id s ∗ ownRaftGhost γ id (toPState s) := by
  iintro Hphys Hghost
  rw [Hm]
  simp only [RNMode.toG, ownStepGhost, ghostRest, GMode.isDyn]
  icases Hghost with ⟨Hghost, %HC⟩
  icases ownRaftPhysC_toPhys cf r id s HC.2.1 $$ Hphys with ⟨Hphys, -⟩
  rw [HC.1]
  iframe Hphys Hghost

theorem ownRawNode_intro_static (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState)
    (s : NState) (ps : PState) (rnv : RawNode) (sv : SoftState) (steps : List raftpb.Message)
    (Hm : rs.mode = .static)
    (Hrel : NStateRel s ps) (Hin : id ∈ γ.reCfg) (Hasync : rnv.asyncStorageWrites' = false)
    (Hdlen : rs.delivered.length = (uint.Z s.logst.applying).toNat)
    (Hunp : rs.unpersisted = s.logst.unpersisted) (Hsnap : s.logst.snap = none)
    (Hstok : StepsOk s rs.steps)
    (Htrm : rs.term = s.term) (Hstor : rs.storage = s.logst.storage)
    (Hpvoff : s.prevote = false) (Hrs_out : rs.outlb = s.gh.outlb)
    (Hrs_unst : rs.unst = s.gh.unst) (Hrs_clb : uint.Z rs.clb ≤ uint.Z s.logst.committed) :
    ⊢ rawNodeOwn rn rnv -∗ ownRaftPhys γ.reCfg rnv.raft' id s -∗
      ownRaftGhost (GF := GF) γ id ps -∗ sdrOk rnv.raft' rs.mode -∗
      rnv.prevSoftSt' ↦□ sv -∗ rnv.stepsOnAdvance' ↦* steps -∗
      ownSliceCap raftpb.Message rnv.stepsOnAdvance' (DFrac.own 1) -∗
      ([∗list] _k ↦ m;p ∈ steps;rs.steps, pendingRel γ id m p) -∗
      ([∗list] _k ↦ m;p ∈ steps;rs.steps, pendingOwn m p) -∗
      isCommitted γ rs.delivered -∗
      storedRecs γ s.logst.prev s.logst.stored -∗
      ownRawNode γ rn id rs := by
  iintro Hrn Hphys Hghost #Hsdrf #Hsoft Hsteps Hcap #Hpend Hpown #Hdeliv #Hstrecs
  obtain ⟨rfl, Hwf⟩ := Hrel
  ihave %Hst := ownRaftGhost_static γ id _ $$ Hghost
  ihave Hphys := ownRaftPhys_toC' $$ Hphys
  ihave Hghost : ownStepGhost γ (rs.mode.toG ⟨rs.capplied, rs.cfg, []⟩)
      (CfgM.simple γ.reCfg (domSet s.progress \ γ.reCfg)) id s $$ [Hghost]
  · rw [Hm]
    simp only [RNMode.toG, ownStepGhost, ghostRest, GMode.isDyn]
    iframe Hghost
    ipureintro; exact CfgStatic.simple γ _ Hst
  iapply ownRawNode_intro γ rn id rs s _ [] rnv sv steps Hwf (fun _ => Hin) rfl Hasync Hdlen
    Hunp Hsnap Hstok Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb
    $$ Hrn Hphys Hghost Hsdrf Hsoft Hsteps Hcap Hpend Hpown Hdeliv Hstrecs

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
    | dyn dec c0 h0 => rw [hm] at Hm; simp [RNMode.isDyn] at Hm; simp [Option.isSome_iff_ne_none.1 Hm]
  iapply ownRawNode_intro γ rn id rs s cf fp rnv sv steps Hwf Hin Hal Hasync Hdlen Hunp Hsnap
    Hstok Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb
    $$ Hrn Hphys Hghost Hsdrf Hsoft Hsteps Hsteps_cap Hpend Hpown Hdeliv Hstrecs

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
  ihave Hghost := ownStepGhost_congr γ _ cf id (s := s)
    (s' := { s with logst := { s.logst with unpersisted := [] } }) rfl rfl rfl rfl $$ Hghost
  imodintro
  iapply ownRawNode_intro γ rn id { rs with unpersisted := [] }
    { s with logst := { s.logst with unpersisted := [] } } cf fp rnv sv steps Hwf Hin Hal Hasync
    Hdlen rfl Hsnap
    (stepsOk_mono s _ rs.steps rfl ⟨rfl, rfl⟩ (Int.le_refl _) rfl rfl Hstok)
    Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb
    $$ Hrn Hphys Hghost Hsdrf Hsoft Hsteps Hsteps_cap Hpend Hpown Hdeliv Hstrecs

end rawnode

end EtcdGrove
end Perennial

-- Projection lemmas, `@[simp, word_unfold]` (ProjSimps.lean).
proj_simps Perennial.EtcdGrove.hsAbs Perennial.EtcdGrove.nodeHardstate Perennial.EtcdGrove.nodeSoftstate
