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
(`netStepTypes`, `NetMsgOk`, now over the message's state), `DynNoSnap` (gone, stage U3c), `DynCCPreOp`/`DynCCPre`
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
2026-10-17, `RNPv`; from 2026-10-10 pre-vote off; 2026-10-17 to 2026-10-25 pre-vote off in the
dynamic mode) in the dynamic mode a pre-candidate's campaign guard (`PreGuardF`), and
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

public import Proof.go_etcd_io.raft.v3.ApiVocab
public import Proof.go_etcd_io.raft.v3.InvReadylog
-- (2026-10-14, reconfiguration stage B7 part 2) the ghost modes
public import Proof.go_etcd_io.raft.v3.StepGhostMode
public import Proof.go_etcd_io.raft.v3.SnapConf
-- (2026-10-16, stage R5) `StepMsg`, `RestMsgOk` for `NetMsgOk`; `ccV2Of` for `DynCCPre`
public import Spec.go_etcd_io.raft.v3.raft__Step
public import Proof.go_etcd_io.raft.v3.CCApply
-- (D22l) `phsWit`, `phsNext`
public import Proof.go_etcd_io.raft.v3.Protocol.CommitWit
public import Proof.go_etcd_io.raft.v3.Protocol.Term0

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-! ## The RawNode's state -/

-- (2026-10-16, stage R5) `HardSt`, `SoftSt` are `InvRaftPhys.lean`'s (stage R4)

-- (2026-10-26, raft's signature, stage 1) `Pending` moved to `Proof.go_etcd_io.raft.v3.ApiVocab`.

-- (2026-10-26, raft's signature, stage 1) `RNMode` moved to `Proof.go_etcd_io.raft.v3.ApiVocab`.

-- (2026-10-26, raft's signature, stage 1) `SnapLoan` moved to `Proof.go_etcd_io.raft.v3.ApiVocab`.

-- (2026-10-26, raft's signature, stage 1) `RNState` moved to `Proof.go_etcd_io.raft.v3.ApiVocab`.

section defs
variable [GooseExts]

-- (2026-10-26, raft's signature, stage 1) `RNMode.isDyn` moved to `Proof.go_etcd_io.raft.v3.ApiVocab`.

/-- The ghost mode `raft.Step` keeps for a `RawNode` in mode `md`, with the ghost part `g`. -/
def RNMode.toG : RNMode → RGh → GMode
  | .static, _ => .static
  | .dyn dec c0 h0 _, g => .dyn dec c0 h0 g

theorem RNMode.toG_isDyn (md : RNMode) (g : RGh) : (md.toG g).isDyn = md.isDyn := by
  cases md <;> rfl

-- (2026-10-26, raft's signature, stage 1) `NoConfIn_prefix` moved to `Proof.go_etcd_io.raft.v3.ApiVocab`.

/-- A step in the mode of a `RawNode` (`RNMode.toG`), with the configuration index `ca`: the
mode afterwards is the node's at some `ca'`, moved only by a `MsgStorageApplyResp`, to at
most the new `applied` (`CidxMove`), and not at all in the static mode. -/
theorem RNMode.stepOut_ca {mode : RNMode} {ca : Nat} {cfg : CCState} {fp : List EntryM}
    {ds : DecMap} {c : CfgM} {id : w64} {m : MessageM} {s s' : NState} {md' : GMode}
    (H : (mode.toG ⟨ca, cfg, fp, ds⟩).StepOut c id m s s' md') (hs : m.Type' ≠ MsgSnap)
    (ha : m.Type' = MsgStorageAppendResp → s'.logst.applied = s.logst.applied) :
    ∃ ca', md' = mode.toG ⟨ca', cfg, fp, ds⟩ ∧ ca ≤ ca' ∧
      ca' ≤ max ca (uint.nat s'.logst.applied) ∧ (mode = .static → ca' = ca) ∧
      (m.Type' ≠ MsgStorageApplyResp → ca' = ca) := by
  cases mode with
  | static =>
    exact ⟨ca, H.1, Nat.le_refl _, Nat.le_max_left _ _, fun _ => rfl, fun _ => rfl⟩
  | dyn dec c0 h0 _ =>
    obtain ⟨g', Hcm, rfl, -⟩ := H
    rcases Hcm with h | h | ⟨hty, h⟩ | ⟨hty, h, -⟩
    · exact absurd h.1 hs
    · subst h
      exact ⟨ca, rfl, Nat.le_refl _, Nat.le_max_left _ _, fun h => (by cases h), fun _ => rfl⟩
    · subst h
      exact ⟨_, rfl, Nat.le_max_left _ _, Nat.le_refl _, fun h => (by cases h),
        fun hm => absurd hty hm⟩
    · exact absurd (ha hty) h

/-- (2026-10-28, stage U3c) A snapshot's step in the mode of a `RawNode`: the mode afterwards is the
node's at the same configuration index and configuration (a restore keeps them, `GMove`), with some
full prefix `fp'` (a restore's), the same at a pre-candidate (which no restore makes). -/
theorem RNMode.stepOut_snap {mode : RNMode} {ca : Nat} {cfg : CCState} {fp : List EntryM}
    {ds : DecMap} {c : CfgM} {id : w64} {m : MessageM} {s s' : NState} {md' : GMode}
    (H : (mode.toG ⟨ca, cfg, fp, ds⟩).StepOut c id m s s' md') (hs : m.Type' = MsgSnap) :
    ∃ fp' ds', md' = mode.toG ⟨ca, cfg, fp', ds'⟩ ∧ (s'.role = .preCandidate → fp' = fp) := by
  cases mode with
  | static => exact ⟨fp, ds, H.1, fun _ => rfl⟩
  | dyn dec c0 h0 _ =>
    obtain ⟨g', Hcm, rfl, -⟩ := H
    rcases Hcm with ⟨-, hci, hcf, -, hpc⟩ | h | ⟨hty, -⟩ | ⟨hty, -⟩
    · refine ⟨g'.fp, g'.decs, ?_, fun h => hpc h⟩
      cases g'
      simp only at hci hcf
      subst hci hcf
      rfl
    · subst h; exact ⟨fp, ds, rfl, fun _ => rfl⟩
    · rw [hs] at hty; simp [MsgSnap, MsgStorageApplyResp] at hty
    · rw [hs] at hty; simp [MsgSnap, MsgStorageAppendResp] at hty


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
  | .appendAck t _ e sn => st = ⟨appendAckM id t (e.getD (entryID.mk (W64 0) (W64 0))), [], sn, [], []⟩
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
  | .appendAck t b e _ => uint.Z t ≤ uint.Z s.term ∧
      -- (D22 S-d3b) the last of what the storage holds after the `Ready`'s boundary `b` (not the
      -- log's current one, which a restore moves), and the term past `0` (the entry's record and
      -- the term bound of the log, at the `Ready`): an acknowledgement of term `0` would be a
      -- local message, of the current term whatever it is
      ∀ x, e = some x → plogLast b s.logst.stored = x ∧ 1 ≤ uint.Z t
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
  | .appendAck t b e sn :: rest => PendingOk s (.appendAck t b e sn) ∧ ∀ p ∈ rest, ApplyAckOk s p
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
  | .appendAck _ _ _ _ :: _, H => exact (H _ List.mem_cons_self).elim
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
    | appendAck t b e sn =>
      intro ⟨⟨H1, H2⟩, Hr⟩
      refine ⟨⟨by omega, ?_⟩, Hall rest Hr⟩
      rw [Hst.2]; exact H2
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
  | appendAck t b e sn =>
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
  | appendAck t b e sn =>
    intro ⟨_, Hr⟩ pv t' Hm
    exact Hr _ Hm
  | applyAck ce =>
    intro H pv t' Hm
    exact H _ (List.mem_cons_of_mem _ Hm)


/-- (D22 S-d3b, 2026-10-21) `StepsOk` across a step that need not keep the log's boundary (a
restore's): it is stated on `stored`, not on `prev` (`PendingOk`). -/
theorem stepsOk_mono_st (s s' : NState) (steps : List Pending)
    (Ht : uint.Z s.term ≤ uint.Z s'.term)
    (Hsd : s'.logst.stored = s.logst.stored)
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
    | appendAck t b e sn =>
      intro ⟨⟨H1, H2⟩, Hr⟩
      refine ⟨⟨by omega, ?_⟩, Hall rest Hr⟩
      rw [Hsd]; exact H2
    | applyAck ce =>
      intro H; exact Hall _ H

/-- (D22 S-d3b) A queued storage acknowledgement of a `StepsOk` queue is `PendingOk` (there is at
most one, and it is followed by apply acknowledgements only). -/
theorem stepsOk_ack {s : NState} {steps : List Pending} {t : w64} {b : entryID}
    {e : Option entryID} {sn : Option SnapshotM} (H : StepsOk s steps)
    (hm : Pending.appendAck t b e sn ∈ steps) : PendingOk s (.appendAck t b e sn) := by
  induction steps with
  | nil => cases hm
  | cons p rest IH =>
    cases p with
    | self pv t' =>
      rcases List.mem_cons.1 hm with h | h
      · cases h
      · exact IH H.2 h
    | appendAck t' b' e' sn' =>
      rcases List.mem_cons.1 hm with h | h
      · cases h; exact H.1
      · exact (H.2 _ h).elim
    | applyAck ce =>
      exact (H _ hm).elim

/-- (D22 S-d3b) The term of a queued storage acknowledgement, after a step that does not move the
term back, is the term before when it is the term after. -/
theorem ack_term_back {t : w64} {s s' : NState} (h1 : uint.Z t ≤ uint.Z s.term)
    (h2 : uint.Z s.term ≤ uint.Z s'.term) (h3 : s'.term = t) : s.term = t := by
  rw [h3] at h2
  exact uint_Z_inj.mp (by omega)

/-! ## The messages of the `RawNode`/`node` API (2026-10-16, stage R5)

Moved here from the old specs (`RawNode__Step.lean`, `RawNode__ApplyConfChange.lean`,
`RawNode__Propose.lean`, `node`'s): `InvNode.lean` and the specs share them. -/

-- (2026-10-26, raft's signature, stage 1) `netStepTypes` moved to `Proof.go_etcd_io.raft.v3.ApiVocab`.

-- (2026-10-26, raft's signature, stage 1) `UnstampedType` moved to `Proof.go_etcd_io.raft.v3.ApiVocab`.

-- (2026-10-26, raft's signature, stage 1) `NetMsgOk` moved to `Proof.go_etcd_io.raft.v3.ApiVocab`.

-- (2026-10-26, raft's signature, stage 1) `NetMsgOk.resps` moved to `Proof.go_etcd_io.raft.v3.ApiVocab`.

omit [GooseExts] in
theorem netStepTypes_nonneg {t : w32} (h : t ∈ netStepTypes) : 0 ≤ sint.Z t := by
  simp only [netStepTypes, List.mem_cons, List.not_mem_nil, _root_.or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> decide

omit [GooseExts] in
theorem netStepTypes_ne_prop {t : w32} (h : t ∈ netStepTypes) : t ≠ MsgProp := by
  intro he
  rw [he] at h
  simp [netStepTypes, MsgProp, MsgApp, MsgAppResp, MsgVote, MsgVoteResp, MsgHeartbeat,
    MsgHeartbeatResp, MsgReadIndex, MsgReadIndexResp, MsgTimeoutNow, MsgTransferLeader,
    MsgForgetLeader, MsgUnreachable, MsgSnapStatus, MsgPreVote, MsgPreVoteResp, MsgSnap] at h

theorem netStepTypes_stepMsg {m : MessageM} (h : m.Type' ∈ netStepTypes) : StepMsg m := by
  simp only [StepMsg, stepMsgTypes]
  simp only [netStepTypes, List.mem_cons, List.not_mem_nil, _root_.or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> simp [h]


/-! ### What a sender in the no-snapshot mode promises the receiver (2026-10-19, D21 M2r)

A message a `Ready` hands out in the cluster's no-snapshot mode is `SentMsgOk` (`isRaftMsg`'s
clause, `InvRaftPhys.lean`): at the node it is addressed to, every clause of `NetMsgOk` but for a
forwarded proposal, which `node.Step` takes as `fwdP` (D21g (A)). -/


-- (2026-10-26, raft's signature, stage 1) `SentMsgOk.ne_timeoutNow` moved to `Proof.go_etcd_io.raft.v3.ApiVocab`.

-- (2026-10-26, raft's signature, stage 1) `SentMsgOk.ne_transferLeader` moved to `Proof.go_etcd_io.raft.v3.ApiVocab`.

-- (2026-10-26, raft's signature, stage 1) `NetMsgOk.of_sent` moved to `Proof.go_etcd_io.raft.v3.ApiVocab`.

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

-- (2026-10-28, stage U3c) `DynNoSnap` (the dynamic mode took no snapshot message, from 2026-10-14,
-- stage B7 part 2) is gone: `RawNode.Step` takes a `MsgSnap` in either mode.

-- (2026-10-26, raft's signature, stage 1) `DynCCPreOp` moved to `Proof.go_etcd_io.raft.v3.ApiVocab`.

/-- The dynamic mode's premises of `ApplyConfChange` (2026-10-14, stage B7 part 2), at the change
`o` the application passes: it is the decoded change (`dec`, from the entry and the log before
it) of the next conf-change entry `e` of the committed log handed out, at position `k` (log index
`k + 1`), past every applied one (`capplied ≤ k`, none in between: in order, once); it applies to
the configuration in use (`ccStepB`: no `confchange` error, fewer than `2^62` tracked ids -- Go
panics otherwise). (Until 2026-10-29, stage U5, also its result no auto-leave joint configuration:
`appliedTo`'s automatic leave was out of `raft.Step`'s scope.) -/
def DynCCPre (dec : CCDec) (rs : RNState) (o : ConfChangeIM) (k : Nat) (e : EntryM)
    (cs' : CCState) : Prop :=
  DynCCPreOp dec rs.delivered rs.capplied rs.cfg (ccV2Of o) k e cs'

-- (2026-10-26, raft's signature, stage 1) `propEntryM` moved to `Proof.go_etcd_io.raft.v3.ApiVocab`.

/-- The scalars of the message `Propose`, `confChangeToMsg` and `node.Propose` build,
`pb.Message{Type: MsgProp, ...}` (2026-10-16, stage R5; until then `propMsg esl`, the Goose
value with its entries' slice). `Propose`/`node.run` set `From` to the node's id. -/
def propMsgM : MessageM := { (zero_val MessageM) with Type' := MsgProp }

/-- The entry `confChangeToMsg` builds for the conf change `o` marshalled as `bs`:
`pb.Entry{Type: typ, Data: data}` (2026-10-16, stage R5; R4 dropped the value builder
`ccEntry`). -/
def ccEntryM (o : Option ConfChangeIM) (bs : List w8) : EntryM := ⟨W64 0, W64 0, confChangeEntryType o, bs⟩

end defs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
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
  -- (D22 S-d1b) the stable part's bound (the storage may be lent)
  icases ownRaftLog_stable_bound _ _ $$ H0 with ⟨%Hsb, H0⟩
  iNamed H0
  ihave %Hul := entsPts_len _ _ _ $$ Huents
  isplitr
  · ipureintro
    have : (ls.uents.length : Int) < 2^63 := by
      rw [Hul.1]; have := word.signed_range lv.unstable'.entries'.len; word
    rw [List.length_append]; push_cast
    omega
  · iapply ownRaftLog_intro l lv lv.storage' σ _ _ ls rfl Hcm Hap Hidx Hnowrap Hstore Hoffset
      Happlied Hpapplied Hcommitted Hssnap Hapg Hip Hipb Hpersist Happlying
      Hpaused Hasz Hamx Hstor Hpend Hfl Hsksn Hsip Hsipn Hlent Hq Hprel Hsat rfl rfl rfl rfl $$ Hl HisStorage HStorage Husnap Hpksn Hkcert Huents
      Huents_cap Hl_logger Hu_logger

/-- The in-progress part of the log is a prefix of what the storage will hold
(`LogPersistRel`): the log and `stored` agree below `offsetInProgress`. -/
theorem persistRel_agree {prev : entryID} {sents uents stored : List EntryM} {ip : w64}
    (H : LogPersistRel sents uents
      (uint.Z ip - (uint.Z prev.index' + (sents.length : Int) + 1)) stored)
    (Hip1 : uint.Z prev.index' + (sents.length : Int) + 1 ≤ uint.Z ip)
    (Hip2 : uint.Z ip ≤ uint.Z prev.index' + (sents.length : Int) + 1 + (uents.length : Int))
    (j : w64) (hj1 : uint.Z prev.index' < uint.Z j) (hj2 : uint.Z j < uint.Z ip) :
    plogTermAt prev (sents ++ uents) j = plogTermAt prev stored j := by
  obtain ⟨Hpre, -⟩ := H
  have h1 : ¬ uint.Z j < uint.Z prev.index' := by omega
  have h2 : ¬ uint.Z j = uint.Z prev.index' := by omega
  unfold plogTermAt
  simp only [h1, h2, ↓reduceIte]
  congr 1
  generalize hk : (uint.Z j - uint.Z prev.index' - 1).toNat = k
  generalize hn : (uint.Z ip - (uint.Z prev.index' + (sents.length : Int) + 1)).toNat = n at Hpre
  have Hkl : k < (sents ++ uents.take n).length := by
    simp only [List.length_append, List.length_take]
    omega
  have H1 : (sents ++ uents)[k]? = (sents ++ uents.take n)[k]? := by
    by_cases hks : k < sents.length
    · rw [List.getElem?_append_left hks, List.getElem?_append_left hks]
    · rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega),
        List.getElem?_take_of_lt (by simp only [List.length_append, List.length_take] at Hkl; omega)]
  rw [H1]
  obtain ⟨tl, htl⟩ := Hpre
  rw [← htl, List.getElem?_append_left Hkl]

/-- (D22 S-d3b, 2026-10-21) The log and what the storage will hold agree below
`offsetInProgress`, with no snapshot pending or one in progress (`Hpersist`, `SipOk`:
`LogPersistRel`, `persistRel_agree`); and the boundary is at most the commit index. -/
theorem ownRaftLog_persistRel (l : Loc) (ls : LogState) :
    ⊢ ownRaftLog (GF := GF) l ls -∗
      ⌜uint.Z ls.prev.index' ≤ uint.Z ls.committed ∧
        ((ls.snap = none ∨ ls.sip = true) →
          ∀ j : w64, uint.Z ls.prev.index' < uint.Z j → uint.Z j < uint.Z ls.inprogress →
            plogTermAt ls.prev (ls.sents ++ ls.uents) j = plogTermAt ls.prev ls.stored j)⌝ ∗
      ownRaftLog l ls := by
  iintro H0
  iNamed H0
  isplitr
  · ipureintro
    refine ⟨Happlied.1, fun Hc j h1 h2 => ?_⟩
    have Hrel : LogPersistRel ls.sents ls.uents
        (uint.Z ls.inprogress - uint.Z lv.unstable'.offset') ls.stored := by
      rcases Hc with Hc | Hc
      · exact (Hpersist Hc).rel
      · exact Hprel.1 Hc
    rw [Hoffset] at Hrel Hipb
    exact persistRel_agree Hrel Hipb.1 Hipb.2 j h1 h2
  · iapply ownRaftLog_intro l lv lv.storage' σ _ _ ls rfl Hcm Hap Hidx Hnowrap Hstore Hoffset
      Happlied Hpapplied Hcommitted Hssnap Hapg Hip Hipb Hpersist Happlying
      Hpaused Hasz Hamx Hstor Hpend Hfl Hsksn Hsip Hsipn Hlent Hq Hprel Hsat rfl rfl rfl rfl $$ Hl HisStorage HStorage Husnap Hpksn Hkcert Huents
      Huents_cap Hl_logger Hu_logger

/-- ... read through the struct. -/
theorem ownRaftPhysC_persistRel (c : CfgM) {V : GSet w64} (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhysCV (GF := GF) c V r id s -∗
      ⌜uint.Z s.logst.prev.index' ≤ uint.Z s.logst.committed ∧
        ((s.logst.snap = none ∨ s.logst.sip = true) →
          ∀ j : w64, uint.Z s.logst.prev.index' < uint.Z j →
            uint.Z j < uint.Z s.logst.inprogress →
            plogTermAt s.logst.prev (s.logst.sents ++ s.logst.uents) j =
              plogTermAt s.logst.prev s.logst.stored j)⌝ ∗
      ownRaftPhysCV c V r id s := by
  iintro H
  icases ownRaftPhysC_log_same c r id s $$ H with ⟨Hlog, Hback⟩
  icases ownRaftLog_persistRel _ _ $$ Hlog with ⟨%Hb, Hlog⟩
  ihave H := Hback $$ Hlog
  iframe H
  ipureintro; exact Hb

/-- (2026-10-28, stage U4a) ... read through the struct: `applying` at most the commit index. -/
theorem ownRaftPhysC_applying (c : CfgM) {V : GSet w64} (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhysCV (GF := GF) c V r id s -∗
      ⌜uint.Z s.logst.applying ≤ uint.Z s.logst.committed⌝ ∗ ownRaftPhysCV c V r id s := by
  iintro H
  icases ownRaftPhysC_log_same c r id s $$ H with ⟨Hlog, Hback⟩
  icases ownRaftLog_fl _ _ $$ Hlog with ⟨%Hb, Hlog⟩
  ihave H := Hback $$ Hlog
  iframe H
  ipureintro; exact Hb.2.1

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

/-- (2026-10-28, stage U0) A node with a snapshot pending is a follower. -/
def SnapFol (s : NState) : Prop := s.logst.snap ≠ none → s.role = .follower

/-- `SnapFol` across a step that, if it ends at a non-follower with a snapshot pending, started at
one (`SnapRoleBack`). -/
theorem SnapFol.step {s s' : NState} (H : SnapFol s) (h : SnapRoleBack s s') : SnapFol s' :=
  fun hsn => Classical.byContradiction fun hr => (h hr hsn).1 (H (h hr hsn).2)

/-- (2026-10-17) The pre-vote scope and the term ceiling, as `ownRawNode` keeps them: (2026-10-25,
T-M M2b; from 2026-10-17 pre-vote off in the dynamic mode) in the dynamic mode a pre-candidate's
campaign guard (`PreGuardF`, at the ghost part's full prefix `fp`); the ceiling `rs.tc` the
struct's (`NGhost.tc`), at least the term, and one past it at a pre-candidate (a won pre-vote
campaigns at `term + 1`: the pre-campaign's budget). -/
def RNPv (rs : RNState) (fp : List EntryM) (s : NState) : Prop :=
  (rs.mode.isDyn = true → PreGuardF fp s) ∧ rs.tc = s.gh.tc ∧
  uint.Z s.term ≤ uint.Z s.gh.tc ∧
  (s.role = .preCandidate → uint.Z s.term + 1 ≤ uint.Z s.gh.tc) ∧
  -- (2026-10-28, stage U0) a node with a snapshot pending is a follower (`SnapFol`): `hup` checks
  -- `promotable`, and a restore makes a follower (`SnapRoleBack`); `appliedSnap`'s rebuild needs it
  SnapFol s

/-- The guard as the mode's (`GMode.Guard`), at the ghost part over `fp`. -/
theorem RNPv.guard {rs : RNState} {fp : List EntryM} {s : NState} (H : RNPv rs fp s) (ca : Nat)
    (cfg : CCState) {ds : DecMap} : (rs.mode.toG ⟨ca, cfg, fp, ds⟩).Guard s := by
  have H1 := H.1
  revert H1
  cases rs.mode with
  | static => intro _; trivial
  | dyn dec c0 h0 _ => intro H1; exact H1 rfl

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
  MsgForgetLeader, MsgUnreachable, MsgSnapStatus, MsgTimeoutNow, MsgTransferLeader, MsgSnap]))

/-- **`raft.Step`'s premises of a message from the network** (`NetMsgOk`) at a `RawNode`'s
state (`RNPv rs s`, the term `rs.term = s.term`; the ceiling covering the message's term and a
transfer's campaign, a pre-vote request only past term `0`): every premise up to `RestMsgOk`,
vacuous at a type the network does not deliver. `k` is `raft.Step`'s spec at the message (what it
takes after `RestMsgOk` is left in `X`). Shared by `RawNode.Step` (`RawNode__Step.lean`) and
`run`'s step (`InvNodeRun.lean`, `wp_rn_raft_Step_net`). -/
theorem NetMsgOk.raftStep {γ : RaftNames} {id : w64} {rs : RNState} {s : NState} {md : GMode} {m : MessageM}
    {ents : List EntryM} {sn : Option SnapshotM} {ctx : List w8} {rsp : List Loc} {X : Prop}
    (Hok : NetMsgOk id ⟨m, ents, sn, ctx, rsp⟩) {fp : List EntryM} (Hpv : RNPv rs fp s) (Htrm : rs.term = s.term)
    (Hmtc : uint.Z m.Term' ≤ uint.Z rs.tc)
    (Htn : m.Type' = MsgTimeoutNow → max (uint.Z rs.term) (uint.Z m.Term') + 1 ≤ uint.Z rs.tc)
    -- (2026-10-29, stage U4) at term `0` the log is empty (`ownStepGhost_term0`): a pre-vote request
    -- is granted there; until then `m.Type' = MsgPreVote → 1 ≤ uint.Z s.term`, from a bootstrap log
    (Hb1 : s.term = W64 0 → plogLast s.logst.prev (s.logst.sents ++ s.logst.uents) = base0)
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
      (m.Type' = MsgStorageAppendResp →
        (∀ sv, sn = some sv →
          snapHit s.logst.snap sv.Metadata'.Index' = s.logst.sat ∧
          uint.Z sv.Metadata'.Index' ≤ uint.Z s.logst.prev.index' ∧
          s.role = .follower ∧ ((md.isDyn = false ∧ SnapAckOk γ id sv) ∨ SnapAckDyn md s sv) ∧
          (s.logst.snap ≠ none → s.logst.lent = false →
            uint.Z sv.Metadata'.Index' ≤ uint.Z s.logst.sxt) ∧
          (∀ k, s.gh.snp = some k → uint.Z k.sid.index' ≤ uint.Z sv.Metadata'.Index')) ∧
        uint.Z m.Term' ≤ uint.Z s.term ∧
        (m.Term' = W64 0 ∨ m.Term' = s.term → m.Index' ≠ W64 0 →
          StableOk (ackLog s.logst sn) (entryID.mk m.LogTerm' m.Index')) ∧ s.gh.unst = false) →
      (m.Type' = MsgStorageApplyResp → m.Term' = W64 0) →
      (m.Type' = MsgReadIndex → m.Term' = W64 0) →
      (m.Type' = MsgReadIndexResp → m.To' = id ∧ m.Term' ≠ W64 0 ∧ m.From' ≠ W64 0 ∧
        m.From' ≠ id) →
      RestMsgOk s m ents ctx → X) : X := by
  have Hok0 := Hok
  simp only [NetMsgOk] at Hok0
  obtain ⟨Hty, Hnri, Hri, Hself, Hrej, -, Hpvf, -⟩ := Hok0
  have Hnr : ∀ {t : w32}, m.Type' = t → ¬ UnstampedType t →
      m.To' = id ∧ m.Term' ≠ W64 0 ∧ m.From' ≠ W64 0 :=
    fun h ht => Hnri (h ▸ ht)
  have Htcb : uint.Z s.gh.tc < 2 ^ 64 := by word
  refine k (netStepTypes_stepMsg Hty) (by not_net) (fun h => Hnr h (by ty_ne))
    (fun h => ⟨(Hnr h (by ty_ne)).1, (Hnr h (by ty_ne)).2.1⟩)
    (fun h => ⟨(Hnr h (by ty_ne)).1, (Hnr h (by ty_ne)).2.1, (Hnr h (by ty_ne)).2.2, Hpvf h,
      fun hz => plogUpToDate_base0 _ _ _ (Hb1 hz),
      .inr (by rw [← Hpv.2.1]; exact Hmtc)⟩)
    (fun h => ⟨(Hnr h (by ty_ne)).1, (Hnr h (by ty_ne)).2.1, (Hnr h (by ty_ne)).2.2,
      fun hp => by have := Hpv.2.2.2.1 hp; omega⟩)
    (fun h => ⟨(Hnr h (by ty_ne)).1, (Hnr h (by ty_ne)).2.1, (Hnr h (by ty_ne)).2.2,
      Hself (.inl h)⟩)
    (fun h => ⟨(Hnr h (by ty_ne)).1, (Hnr h (by ty_ne)).2.1, (Hnr h (by ty_ne)).2.2,
      Hself (.inr (.inl h))⟩)
    (fun h => ⟨(Hnr h (by ty_ne)).1, (Hnr h (by ty_ne)).2.1, (Hnr h (by ty_ne)).2.2, Hrej h⟩)
    (fun h => ⟨(Hnr h (by ty_ne)).1, (Hnr h (by ty_ne)).2.1, (Hnr h (by ty_ne)).2.2,
      Hself (.inr (.inr (.inl h)))⟩)
    -- (2026-10-20, D22 S-c) a leader's snapshot, from another node
    (fun h => ⟨(Hnr h (by ty_ne)).1, (Hnr h (by ty_ne)).2.1, (Hnr h (by ty_ne)).2.2,
      Hself (.inr (.inr (.inr (.inr h))))⟩)
    (by not_net) (by not_net) (by not_net) (by not_net) (fun h => Hri (.inl h))
    (fun h => ⟨(Hnr h (by ty_ne)).1, (Hnr h (by ty_ne)).2.1, (Hnr h (by ty_ne)).2.2,
      Hself (.inr (.inr (.inr (.inl h))))⟩)
    (Hok.restMsgOk (st := ⟨m, ents, sn, ctx, rsp⟩) (fun h => by
      have := Htn h; rw [Hpv.2.1, Htrm] at this
      have := Int.le_max_left (uint.Z s.term) (uint.Z m.Term')
      have := Int.le_max_right (uint.Z s.term) (uint.Z m.Term')
      simp only at h ⊢
      exact ⟨by omega, by omega, Hfla⟩) Hxo)

/-- The mode's guard from the guard in the dynamic mode. -/
theorem RNMode.guard_of {mode : RNMode} {fp : List EntryM} {s : NState}
    (h : mode.isDyn = true → PreGuardF fp s) (ca : Nat) (cfg : CCState) {ds : DecMap} :
    (mode.toG ⟨ca, cfg, fp, ds⟩).Guard s := by
  cases mode with
  | static => trivial
  | dyn dec c0 h0 _ => exact h rfl

/-- In the static mode `RNPv` does not depend on the full prefix. -/
theorem RNPv.static_fp {rs : RNState} {fp fp' : List EntryM} {s : NState} (H : RNPv rs fp s)
    (hm : rs.mode = .static) : RNPv rs fp' s :=
  ⟨fun h => (by rw [hm] at h; cases h), H.2⟩

/-- `RNPv` after a step of `raft.Step` (`PreCandStep`): the guard kept (`PreGuardF.pc`), the ceiling
kept, the term within the ceiling, and a pre-campaign (`MsgHup`) only with the ceiling one past the
term. -/
theorem RNPv.step [GoGlobalContext] [GoSemanticsFunctions] {rs rs' : RNState} {fp : List EntryM}
    {s s' : NState} {m : MessageM}
    (H : RNPv rs fp s)
    (hmd : rs'.mode = rs.mode) (htc : rs'.tc = rs.tc) (_hpv : s'.prevote = s.prevote)
    (hgh : s'.gh = s.gh) (ht : uint.Z s'.term ≤ uint.Z s.gh.tc) (hpc : PreCandStep m s s')
    (hhup : m.Type' = MsgHup → uint.Z s.term + 1 ≤ uint.Z s.gh.tc) : RNPv rs' fp s' := by
  obtain ⟨H1, H2, -, H4, H5⟩ := H
  refine ⟨fun h => PreGuardF.pc hpc (H1 (hmd ▸ h)), by rw [htc, hgh]; exact H2,
    by rw [hgh]; exact ht, fun h => ?_, H5.step hpc.2⟩
  obtain ⟨Ht, Hor⟩ := hpc.1 h
  rw [hgh, Ht]
  rcases Hor with ⟨Hr, -⟩ | ⟨Hh, -⟩
  · exact H4 Hr
  · exact hhup Hh

/-- `RNPv` across a step that keeps the term, the role and the ghost bounds, and the guard
(`hg`). -/
theorem RNPv.keep {rs rs' : RNState} {fp : List EntryM} {s s' : NState} (H : RNPv rs fp s)
    (hmd : rs'.mode = rs.mode) (htc : rs'.tc = rs.tc) (_hpv : s'.prevote = s.prevote)
    (hgh : s'.gh = s.gh) (ht : s'.term = s.term) (hr : s'.role = s.role)
    (hsn : s'.logst.snap = s.logst.snap)
    (hg : PreGuardF fp s → PreGuardF fp s') : RNPv rs' fp s' := by
  obtain ⟨H1, H2, H3, H4, H5⟩ := H
  refine ⟨fun h => hg (H1 (hmd ▸ h)), by rw [htc, hgh]; exact H2,
    by rw [hgh, ht]; exact H3, fun h => by rw [hgh, ht]; exact H4 (hr ▸ h),
    fun h => by rw [hr]; exact H5 (hsn ▸ h)⟩

/-- (2026-10-28, stage U3c) `RNPv` at another full prefix, the same at a pre-candidate (the guard
reads the prefix only there). -/
theorem RNPv.fp_pc {rs : RNState} {fp fp' : List EntryM} {s : NState} (H : RNPv rs fp s)
    (h : s.role = .preCandidate → fp' = fp) : RNPv rs fp' s := by
  refine ⟨fun hd hl hr => ?_, H.2⟩
  obtain rfl := h hr
  exact H.1 hd hl hr

/-- `RNPv.keep` in the static mode, where the guard is not kept. -/
theorem RNPv.keepS {rs rs' : RNState} {fp : List EntryM} {s s' : NState} (H : RNPv rs fp s)
    (hmd : rs'.mode = rs.mode) (htc : rs'.tc = rs.tc) (_hpv : s'.prevote = s.prevote)
    (hgh : s'.gh = s.gh) (ht : s'.term = s.term) (hr : s'.role = s.role)
    (hsn : s'.logst.snap = s.logst.snap)
    (hm : rs.mode = .static) : RNPv rs' fp s' := by
  obtain ⟨-, H2, H3, H4, H5⟩ := H
  refine ⟨fun h => (by rw [hmd, hm] at h; cases h), by rw [htc, hgh]; exact H2,
    by rw [hgh, ht]; exact H3, fun h => by rw [hgh, ht]; exact H4 (hr ▸ h),
    fun h => by rw [hr]; exact H5 (hsn ▸ h)⟩

/-- (D22 S-d3a, 2026-10-21) **A snapshot `Ready`'s loan, as the node keeps it** (`RNState.slent`):
the ghost mirror of the lent storage (`NGhost.slent`, `SnpOk`) and of the snapshot handed out
(`NGhost.snp`); with a loan, the snapshot still pending or (D22 S-d3b, 2026-10-21) a later one
restored past it (`RawNode.Step` takes a `MsgSnap` with a loan since S-d3b: the restore found the
log without the later snapshot's last entry, `ackBaseW`), the lent snapshot at most the commit
index, the floor the storage was lent at, what the storage will hold the batch handed out
(`stored = unpersisted`), `applying` at most the snapshot's index, the committed log up to the
snapshot extending `delivered`, and its acknowledgement queued last, after the node's own
responses (a snapshot `Ready` hands out no committed entries), at the snapshot as its boundary.
(Until S-d3b: the snapshot still pending, `psnap` off, and `psnap → steps = []`.) -/
def LoanOk (rs : RNState) (s : NState) : Prop :=
  s.gh.slent = rs.slent.isSome ∧
  (rs.slent = none → s.gh.snp = none ∧ ∀ t b e sv, Pending.appendAck t b e (some sv) ∉ rs.steps) ∧
  (∀ l, rs.slent = some l →
    s.gh.snp = some (snapTrip l.snap l.snap.Metadata'.ConfState'.lists) ∧
    (s.logst.snap = some (snapId l.snap) ∨
      ∃ s2, s.logst.snap = some s2 ∧ uint.Z l.snap.Metadata'.Index' < uint.Z s2.index' ∧
        rs.psnap = true) ∧
    uint.Z l.snap.Metadata'.Index' ≤ uint.Z s.logst.committed ∧
    l.fl = s.logst.fl ∧
    s.logst.stored = s.logst.unpersisted ∧
    -- (2026-10-28, stage U3c) strictly (`SnapRdy`, `SipOk`): `appliedSnap` moves `applied`
    uint.Z s.logst.applying < uint.Z l.snap.Metadata'.Index' ∧
    rs.delivered <+: l.dlv ∧ l.dlv.length = (uint.Z l.snap.Metadata'.Index').toNat ∧
    ∃ pre t e, rs.steps = pre ++ [Pending.appendAck t (snapId l.snap) e (some l.snap)] ∧
      ∀ p ∈ pre, ∃ pv t', p = .self pv t')

/-- (2026-10-28, stage U4a) **The record of the storage's terms is of the committed log handed
out** (`LogState.stb`/`sdt`, `StorTermsOk`): with a snapshot pending and the storage not lent, the
term `sdt[k]` is that of `delivered`'s entry at index `stb + k + 1`. Made by a restore when none
was pending, of the log's terms after its boundary up to `applying` (`restoreSdt`), which are
`delivered`'s: both are prefixes of the global committed log (`RawNode.Step`). So the floor raised
with a snapshot pending comes with `delivered`'s terms (`ownRawNode_raise_floor`). -/
def SdtTie (rs : RNState) (s : NState) : Prop :=
  s.logst.snap ≠ none →
    ∀ k t, s.logst.sdt[k]? = some t →
      (rs.delivered.map (·.Term'))[uint.nat s.logst.stb + k]? = some t

/-- `SdtTie` across a step that keeps the record, with no snapshot pending that was not, and only
extends `delivered`. -/
theorem SdtTie.keep {rs rs' : RNState} {s s' : NState} (H : SdtTie rs s)
    (hsn : s'.logst.snap ≠ none → s.logst.snap ≠ none)
    (hb : s'.logst.stb = s.logst.stb) (hd : s'.logst.sdt = s.logst.sdt)
    (hdl : rs.delivered <+: rs'.delivered) : SdtTie rs' s' := by
  intro h1 k t ht
  rw [hd] at ht; rw [hb]
  have := H (hsn h1) k t ht
  obtain ⟨u, hu⟩ := hdl
  rw [← hu, List.map_append, List.getElem?_append_left (List.getElem?_eq_some_iff.1 this).1]
  exact this

/-- `SdtTie` across a frame step (`NetFrame`, `LocalFrame`: the pending snapshot and the record
kept, `delivered` unchanged). -/
theorem SdtTie.ofRec {rs rs' : RNState} {s s' : NState} (H : SdtTie rs s)
    (hsn : s'.logst.snap = s.logst.snap) (hr : logStoreRec s'.logst = logStoreRec s.logst)
    (hdl : rs'.delivered = rs.delivered := by rfl) : SdtTie rs' s' :=
  SdtTie.keep H (by rw [hsn]; exact fun h => h) (congrArg (·.2.1) hr) (congrArg (·.2.2) hr)
    (by rw [hdl]; exact List.prefix_refl _)

/-- `SdtTie` across a `MsgSnap`'s step (`SnapLogStep`): the record kept, or the restore's of the
log's terms (`restoreSdt`), which are `delivered`'s (`Hdag`, `ownStepGhost_dlv_terms`). -/
theorem SdtTie.snap {rs rs' : RNState} {s s' : NState} {sv : SnapshotM} {m : MessageM}
    (H : SdtTie rs s)
    (Hdag : ∀ k t, (logTermsTo s.logst)[k]? = some t →
      (rs.delivered.map (·.Term'))[uint.nat s.logst.prev.index' + k]? = some t)
    (Hsl : SnapLogStep sv m s s') (hdl : rs'.delivered = rs.delivered := by rfl) :
    SdtTie rs' s' := by
  intro h1 k t ht
  rw [hdl]
  rcases Hsl with ⟨-, h2, -, -, hb, hd⟩ | ⟨-, -, -, -, -, -, hb, hd⟩
  · rw [hd] at ht; rw [hb]; rw [h2] at h1; exact H h1 k t ht
  · rw [hd] at ht; rw [hb]
    unfold restoreSdt at ht ⊢
    cases hs : s.logst.snap with
    | none => simp only [hs, Option.isSome_none] at ht ⊢; exact Hdag k t ht
    | some _ =>
      simp only [hs, Option.isSome_some, ↓reduceIte] at ht ⊢
      exact H (by rw [hs]; simp) k t ht

/-- No snapshot pending: nothing to tie. -/
theorem SdtTie.of_none {rs : RNState} {s : NState} (h : s.logst.snap = none) : SdtTie rs s :=
  fun h' => absurd h h'

/-- No loan, no snapshot acknowledgement queued. -/
theorem LoanOk.none_noack {rs : RNState} {s : NState} (H : LoanOk rs s) (h : rs.slent = none) :
    s.gh.snp = none ∧ ∀ t b e sv, Pending.appendAck t b e (some sv) ∉ rs.steps := H.2.1 h

/-- An empty queue: no loan. -/
theorem LoanOk.none_of_nil {rs : RNState} {s : NState} (H : LoanOk rs s) (h : rs.steps = []) :
    rs.slent = none := by
  cases hl : rs.slent with
  | none => rfl
  | some l =>
    obtain ⟨-, -, -, -, -, -, -, -, pre, t, e, Hst, -⟩ := H.2.2 l hl
    rw [h] at Hst; simp at Hst

/-- `LoanOk` across a step that keeps what it reads (the commit index not moved back). -/
theorem LoanOk.keep {rs rs' : RNState} {s s' : NState} (H : LoanOk rs s)
    (hgh : s'.gh = s.gh) (hsn : s'.logst.snap = s.logst.snap) (hfl : s'.logst.fl = s.logst.fl)
    (hsd : s'.logst.stored = s.logst.stored) (hu : s'.logst.unpersisted = s.logst.unpersisted)
    (hap : s'.logst.applying = s.logst.applying)
    (hcm : uint.Z s.logst.committed ≤ uint.Z s'.logst.committed)
    (hsl : rs'.slent = rs.slent := by rfl) (hst : rs'.steps = rs.steps := by rfl)
    (hd : rs'.delivered = rs.delivered := by rfl) (hps : rs'.psnap = rs.psnap := by rfl) :
    LoanOk rs' s' := by
  obtain ⟨H1, H2, H3⟩ := H
  refine ⟨by rw [hgh, hsl]; exact H1, fun h => ?_, fun l h => ?_⟩
  · rw [hgh, hst]; exact H2 (hsl ▸ h)
  · obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := H3 l (hsl ▸ h)
    rw [hgh, hsn, hfl, hsd, hu, hap, hd, hst, hps]
    exact ⟨a1, a2, Int.le_trans a3 hcm, a4, a5, a6, a7, a8, a9⟩

/-- `LoanOk` across `RawNode.Step`: the ghost state kept, and with a loan what it reads of the log,
but for the pending snapshot, which (D22 S-d3b) a restore past the commit index replaces. -/
theorem LoanOk.step {rs : RNState} {s s' : NState} {b : Bool} (t : w64) (H : LoanOk rs s)
    (hgh : s'.gh = s.gh)
    (hkeep : rs.slent ≠ none →
      (s'.logst.snap = s.logst.snap ∨
        ∃ s2, s'.logst.snap = some s2 ∧ uint.Z s.logst.committed < uint.Z s2.index' ∧
          b = true) ∧
      s'.logst.fl = s.logst.fl ∧
      s'.logst.stored = s.logst.stored ∧ s'.logst.unpersisted = s.logst.unpersisted ∧
      s'.logst.applying = s.logst.applying ∧
      uint.Z s.logst.committed ≤ uint.Z s'.logst.committed) :
    LoanOk { rs with term := t, psnap := rs.psnap || b } s' := by
  obtain ⟨H1, H2, H3⟩ := H
  refine ⟨by rw [hgh]; exact H1, fun h => ?_, fun l h => ?_⟩
  · rw [hgh]; exact H2 h
  · have hl : rs.slent = some l := h
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := H3 l hl
    obtain ⟨k1, k2, k3, k4, k5, k6⟩ := hkeep (by rw [hl]; simp)
    refine ⟨by rw [hgh]; exact a1, ?_, Int.le_trans a3 k6, by rw [k2]; exact a4,
      by rw [k3, k4]; exact a5, by rw [k5]; exact a6, a7, a8, a9⟩
    rcases k1 with k1 | ⟨s2, h2, hgt, hb⟩
    · rw [k1]
      rcases a2 with a2 | ⟨s2, h2, hlt, hps⟩
      · exact .inl a2
      · exact .inr ⟨s2, h2, hlt, by simp [hps]⟩
    · exact .inr ⟨s2, h2, by omega, by simp [hb]⟩

/-- (D22 S-d3b) The queue's snapshot acknowledgement is the loan's (it holds at most one storage
acknowledgement, after the node's own responses). -/
theorem LoanOk.ack_eq {rs : RNState} {s : NState} (H : LoanOk rs s) {t : w64} {b : entryID}
    {e : Option entryID} {sv : SnapshotM} (hm : Pending.appendAck t b e (some sv) ∈ rs.steps) :
    ∃ l, rs.slent = some l ∧ sv = l.snap ∧ b = snapId l.snap := by
  cases hl : rs.slent with
  | none => exact absurd hm ((H.none_noack hl).2 t b e sv)
  | some l =>
    obtain ⟨-, -, -, -, -, -, -, -, pre, t', e', Hst, Hpre⟩ := H.2.2 l hl
    rw [Hst] at hm
    rcases List.mem_append.1 hm with h | h
    · obtain ⟨pv, t'', h'⟩ := Hpre _ h; cases h'
    · simp only [List.mem_singleton, Pending.appendAck.injEq] at h
      exact ⟨l, rfl, Option.some.inj h.2.2.2, h.2.1⟩

/-- (D22 S-d3b) With a storage acknowledgement queued and no restore since its `Ready` (the boundary
and the pending snapshot the `Ready`'s), no snapshot is pending or one is in progress (the loan's,
`SnpOk`): the log's persistence relation holds (`ownRaftPhysC_persistRel`). -/
theorem ack_snap_sip {rs : RNState} {s : NState} (H : LoanOk rs s) (Hsn : SnpOk s.gh s.logst) :
    (∃ t b e sn, Pending.appendAck t b e sn ∈ rs.steps ∧ s.logst.prev = b ∧
      s.logst.snap = sn.map snapId) → s.logst.snap = none ∨ s.logst.sip = true := by
  rintro ⟨t, b, e, sn, hm, -, hsn⟩
  cases sn with
  | none => exact .inl hsn
  | some sv =>
    obtain ⟨l, hl, rfl, -⟩ := H.ack_eq hm
    obtain ⟨a1, -⟩ := H.2.2 l hl
    exact .inr ((Hsn.2.1 _ a1).1 hsn).1

/-- What `GMode.Pre` needs of the node, for any message but a snapshot or a storage-apply
acknowledgement (2026-10-14, stage B7 part 2): (2026-10-25, T-M M2b; until then no pre-candidate in
the dynamic mode) the mode's campaign guard (`GMode.Guard`), and room in the log. -/
def PreFacts (md : GMode) (s : NState) : Prop :=
  md.Guard s ∧
  plogLastIndexZ (toPState s).base (toPState s).log + 2 ^ 61 < 2 ^ 64

/-- (2026-10-20, D22 S-c) `GMode.Pre` for any message but a storage-apply acknowledgement, a
snapshot's included (`GMode.Pre` asks nothing of one). -/
theorem RNMode.pre_net {mode : RNMode} {g : RGh} {m : MessageM} {ents : List EntryM}
    {s : NState} (h : PreFacts (mode.toG g) s)
    (h3 : m.Type' ≠ MsgStorageApplyResp) : (mode.toG g).Pre m ents s := by
  cases mode with
  | static => trivial
  | dyn dec c0 h0 _ =>
    exact ⟨h.1, fun h' => absurd h' h3, fun _ => h.2⟩

theorem GMode.Pre.of_facts {md : GMode} {m : MessageM} {ents : List EntryM}
    {s : NState} (h : PreFacts md s) (h1 : m.Type' ≠ MsgSnap)
    (h3 : m.Type' ≠ MsgStorageApplyResp) :
    md.Pre m ents s := by
  cases md with
  | static => trivial
  | dyn dec c0 h0 g => exact ⟨h.1, fun h' => absurd h' h3, fun _ => h.2⟩

/-- ... read off the struct, with the mode's guard (2026-10-25, T-M M2b: until then at a node with
pre-vote off in the dynamic mode). -/
theorem ownRaftPhysC_preFacts (c : CfgM) {V : GSet w64} (r : Loc) (id : w64) (s : NState)
    {md : GMode} (Hg : md.Guard s) :
    ⊢ ownRaftPhysCV (GF := GF) c V r id s -∗ ⌜PreFacts md s⌝ ∗ ownRaftPhysCV c V r id s := by
  iintro H
  icases ownRaftPhysC_last_bound c r id s $$ H with ⟨%Hb, H⟩
  iframe H
  ipureintro
  exact ⟨Hg, Hb⟩

end proof

section rawnode
variable [GooseExts] [GooseSemantics] [GooseInterp]
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

-- (2026-10-26, raft's signature, stage 1) `msgDat` moved to `Proof.go_etcd_io.raft.v3.ApiVocab`.

-- (2026-10-26, raft's signature, stage 1) `msgDat_pers` moved to `Proof.go_etcd_io.raft.v3.ApiVocab`.

-- (2026-10-26, raft's signature, stage 1) `isRaftMsg` moved to `Proof.go_etcd_io.raft.v3.ApiVocab`.

-- (2026-10-26, raft's signature, stage 1) `isRaftMsg_pers` moved to `Proof.go_etcd_io.raft.v3.ApiVocab`.

-- (2026-10-26, raft's signature, stage 1) `isRaftMsg_dat` moved to `Proof.go_etcd_io.raft.v3.ApiVocab`.

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
    exact ⟨.inl Hsn, Hun, stored_agree _ _ _ _ HwL HwF HRA He Hhit.2⟩
  iexact Hg

/-- (D22 S-d3a) `stableOk_of_stored` for a log state `ls` with the node's log and records' base
and what it holds (the acknowledgement's `ackLog`), the storage holding the pending snapshot
(`sapp`) or none pending. -/
theorem stableOk_of_stored_ls (γ : RaftNames) (id : w64) (s : NState) {md : Bool}
    (ls : LogState) (e : entryID)
    (Hls : ls.prev = s.logst.prev ∧ ls.stored = s.logst.stored ∧
      ls.sents ++ ls.uents = s.logst.sents ++ s.logst.uents)
    (He : plogLast s.logst.prev s.logst.stored = e)
    (Hsn : ls.snap = none ∨ ls.sapp = true) (Hun : ls.unpersisted = []) :
    ⊢ storedRecs γ s.logst.prev s.logst.stored -∗ ownRaftGhost (GF := GF) γ id (toPState s) md -∗
      ⌜StableOk ls e⌝ ∗ ownRaftGhost γ id (toPState s) md := by
  iintro #Hst Hg
  icases ownRaftGhost_storedRecs_keep γ id (toPState s) $$ Hg with ⟨Hg, #Hlr⟩
  unfold storedRecs
  icases Hst with ⟨%HwL, #HrL⟩
  icases Hlr with ⟨%HwF, #HrF⟩
  icases logRecs_agree γ _ _ _ _ $$ HrL HrF with %HRA
  isplitr
  · ipureintro
    intro Hhit
    obtain ⟨Hp, Hs, Hl⟩ := Hls
    refine ⟨Hsn, Hun, ?_⟩
    have Ht : plogTermAt s.logst.prev (s.logst.sents ++ s.logst.uents) e.index' = some e.term' := by
      have := Hhit.2; rw [Hp, Hl] at this; exact this
    rw [Hs, Hl, Hp]
    exact stored_agree _ _ _ _ HwL HwF HRA He Ht
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

-- (D22 S-d3b, 2026-10-21) `storedRecsP` (the records gated by `RNState.psnap`, D22 S-c to S-d3a) is
-- gone: the records are kept at the queued acknowledgement's boundary (`ackInv`).

/-! ### The acknowledgement across a restore (D22 S-d3b, 2026-10-21)

A `MsgSnap` may come between a `Ready` and its `Advance` (`node.go` steps the network while the
application persists the `Ready`). Its restore moves the log's boundary past the commit index, so
the queued `MsgStorageAppendResp` acknowledges entries of a log with another boundary: what the
storage holds after the `Ready`'s boundary `b` (`LogState.stored`). Its `stableTo` must then miss
(had it hit, the storage, at `b`, would be shadowed by the restored snapshot with a stable part
after it, and the next `Ready`'s `ApplySnapshot` then `Append` would panic on the gap). It does:
a hit at the acknowledged entry, by Log Matching between `stored` and the log (both with records),
puts `stored`'s entry at the restored boundary `p` at `p`'s term -- which the restore excluded.

That is a fact of the restore's moment, carried to the `Advance` (`ackBaseW`): the restore saw the
log without `p`'s last entry (`restore`'s `!matchTerm`, `SnapLogStep`), and `stored` agreed with
the log up to `offsetInProgress` (`LogPersistRel`); above it, a `MsgApp` of the acknowledgement's
term had cut the batch, at an entry the term's leader's log has and `stored` has not
(`ackLostW`, `AppTrunc`); the restored snapshot is in that leader's log too (`isMessage`'s
`snap`), so `stored` agreeing with it at `p` would agree with it below, at the cut, against the
cut. A later restore carries the fact on: the new boundary's snapshot is in the same leader's log,
which has `p`'s entry. All of it only while the term is the acknowledgement's: after a term change
the acknowledgement is stale (`raft.Step`'s lower-term arm: no `stableTo`). -/

/-- (D22 S-d3b) The term of a leader's entry is past `0`: its campaign does not wrap the term
(`CampOk`). -/
theorem isLeader_term_nz (γ : RaftNames) (id term : w64) :
    ⊢ isLeader (GF := GF) γ id term -∗ ⌜term ≠ W64 0⌝ := by
  unfold isLeader isWin isWinCore
  iintro ⟨%q, %c, ⟨%γw, %F0, %k, %M, -, #HcK, -, -, -⟩, -⟩
  icases isCampK_ok γ id term F0 k $$ HcK with %H
  ipureintro; exact H.term_nz

/-- (D22 S-d3b) A record's term is past `0`: a leader's (`isLeader_term_nz`) or a boot entry's
(`1`). -/
theorem isEntryR_term_nz (γ : RaftNames) (e : EntryM) (pt : w64) :
    ⊢ isEntryR (GF := GF) γ e pt -∗ ⌜e.Term' ≠ W64 0⌝ := by
  unfold isEntryR
  iintro (⟨%ldr, %_, %_, %_, %_, #Hl, -, -, -, -, -⟩ | ⟨%Hb, -⟩)
  · iapply isLeader_term_nz γ ldr e.Term' $$ Hl
  · ipureintro
    obtain ⟨-, -, Ht, -⟩ := Hb
    rw [Ht]; word

omit [GooseSemantics] go_gctx [StorageModel GF] sem package_sem in
/-- (Lean helper, as `StepGhost.lean`'s.) -/
private theorem ite_pos_elim' {PROP : Type _} [BI PROP] {c : Prop} [Decidable c] (P Q : PROP)
    (h : c) : (if c then P else Q) ⊢ P := by
  rw [ite_eq_left_iff.mpr (fun hn => absurd h hn)]

/-- (Lean helper, as `StepGhost.lean`'s `logRecs_lookup_b`.) One entry's record. -/
private theorem logRecs_lookup_b' (γ : RaftNames) (b : entryID) (es : List EntryM)
    (k : Nat) (e : EntryM) :
    es[k]? = some e → uint.Z b.index' + (k : Int) + 1 < 2 ^ 64 →
    ⊢ logRecs (GF := GF) γ b es -∗
      ∃ pt, ⌜plogTermAt b es (pidx b k) = some pt⌝ ∗ isEntryR γ e pt := by
  intro He Hr
  unfold logRecs
  iintro #H
  ihave #He' := BigSepL.bigSepL_lookup He $$ H
  iapply ite_pos_elim' _ _ Hr $$ He'

/-- (D22 S-d3b) The last entry of a non-empty log with records has a term past `0`. -/
theorem storedRecs_last_term (γ : RaftNames) (b : entryID) (L : List EntryM) (hne : L ≠ [])
    (Hnw : uint.Z b.index' + (L.length : Int) < 2 ^ 64) :
    ⊢ storedRecs (GF := GF) γ b L -∗
      ⌜(plogLast b L).term' ≠ W64 0 ∧
        plogTermAt b L (plogLast b L).index' = some (plogLast b L).term'⌝ := by
  iintro #H
  unfold storedRecs
  icases H with ⟨%Hwf, #Hr⟩
  obtain ⟨x, Hx⟩ : ∃ x, L.getLast? = some x := by
    cases h : L.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.1 h) hne
    | some x => exact ⟨x, rfl⟩
  have Hk := getLast?_some_getElem? L x Hx
  have Hlen : 0 < L.length := List.length_pos_iff.2 hne
  have Hxi := Hwf _ _ Hk
  have Hpl : plogLast b L = entId x := by simp [plogLast, Hx]
  rw [Hpl]
  icases logRecs_lookup_b' γ b L _ x Hk (by omega) $$ Hr with ⟨%pt, -, #He⟩
  icases isEntryR_term_nz γ x pt $$ He with %Ht
  ipureintro
  refine ⟨Ht, ?_⟩
  exact plogTermAt_lookup b L _ _ x Hk (by simp only [entId]; push_cast at Hxi ⊢; omega)

/-- (D22 S-d3b) No term of a node's log is above the node's term (`TermsLe`, `ownLogGhost`). -/
theorem ownRaftGhost_terms_le (γ : RaftNames) (id : w64) (ps : PState) {md : Bool} :
    ownRaftGhost (GF := GF) γ id ps md ⊢
      ⌜∀ j x, plogTermAt ps.base ps.log j = some x → uint.Z x ≤ uint.Z ps.term⌝ ∗
        ownRaftGhost γ id ps md := by
  apply persistent_entails_right
  iintro H
  unfold ownRaftGhost
  icases H with ⟨%γv, %voted, %kl, H⟩
  iNamed H
  unfold ownLogGhost
  icases Hlg with ⟨%γm, %terms, %γa, %acks, %fp, %γc, %camps, %γl, %vlogs, %γw, %wins, Hlg⟩
  iNamed Hlg
  ipureintro
  intro j x Hx
  obtain ⟨Hfo, -, Htl⟩ := Hfull
  have hj := (plogTermAt_some_range _ _ _ _ Hx).1
  rw [← full_term_at ps.base fp ps.log j Hfo hj] at Hx
  exact (Htl j x Hx).1

/-- (D22 S-d3b) **The batch a `MsgApp` of term `t` cut** from what the storage holds after `b`
(`es`), above `offsetInProgress` `ip`: nothing (all of `es` is in progress), or an index `c`,
between the boundary and `ip`, at which a log of the leader of `t` (`leadFull`) has an entry and
`es` has another or none -- the cut (`AppTrunc`). -/
def ackLostW (γ : RaftNames) (t : w64) (b : entryID) (es : List EntryM) (ip : w64) : IProp GF :=
  iprop(⌜plogLastIndexZ b es < uint.Z ip⌝ ∨
    ∃ (c : w64) (G : List EntryM), ⌜uint.Z b.index' < uint.Z c ∧ uint.Z c ≤ uint.Z ip ∧
      (plogTermAt base0 G c).isSome ∧ plogTermAt base0 G c ≠ plogTermAt b es c⌝ ∗
      leadFull γ t G)

instance ackLostW_pers (γ : RaftNames) (t : w64) (b : entryID) (es : List EntryM) (ip : w64) :
    Persistent (ackLostW (GF := GF) γ t b es ip) := by
  unfold ackLostW; infer_instance

/-- (D22 S-d3b) **A restore's mark** on what the storage holds after `b` (`es`), at the restored
boundary `p`: `es` has no entry of `p`'s term at `p`'s index (what the acknowledgement's miss
needs), and a log of the leader of `t` has `p` (what a later restore needs). -/
def ackBaseW (γ : RaftNames) (t : w64) (b : entryID) (es : List EntryM) (p : entryID) :
    IProp GF :=
  iprop(⌜plogTermAt b es p.index' ≠ some p.term'⌝ ∗
    ∃ G, leadFull γ t G ∗ ⌜plogTermAt base0 G p.index' = some p.term'⌝)

instance ackBaseW_pers (γ : RaftNames) (t : w64) (b : entryID) (es : List EntryM) (p : entryID) :
    Persistent (ackBaseW (GF := GF) γ t b es p) := by
  unfold ackBaseW; infer_instance

/-- (D22 S-d3b) A queued acknowledgement of term `t` of the log up to `e` after the `Ready`'s
boundary `b`, at the node's state `s`: no restore since the `Ready` (the boundary and the pending
snapshot the `Ready`'s; at the term `t`, the cut, `ackLostW`), or a restore past `b` (at the term
`t`, with an entry acknowledged, its mark, `ackBaseW`). -/
abbrev ackArm (γ : RaftNames) (t : w64) (b : entryID) (e : Option entryID) (sn : Option SnapshotM)
    (s : NState) : IProp GF :=
  iprop((⌜s.logst.prev = b ∧ s.logst.snap = sn.map snapId⌝ ∗
          (∀ (_ : s.term = t), ackLostW γ t b s.logst.stored s.logst.inprogress)) ∨
        (⌜uint.Z b.index' < uint.Z s.logst.prev.index'⌝ ∗
          (∀ (_ : e ≠ none ∧ s.term = t), ackBaseW γ t b s.logst.stored s.logst.prev)))

instance ackArm_pers (γ : RaftNames) (t : w64) (b : entryID) (e : Option entryID)
    (sn : Option SnapshotM) (s : NState) : Persistent (ackArm (GF := GF) γ t b e sn s) := by
  unfold ackArm; infer_instance

/-- (D22 S-d3b, 2026-10-21) **What the node keeps for its queued storage acknowledgement** (`ownRawNode`'s
`Hstrecs`): the records of what the storage holds after the `Ready`'s boundary (`storedRecs`, for
Log Matching), and the acknowledgement's arm (`ackArm`). (Until S-d3b `storedRecsP γ psnap prev
stored`: the records at the log's boundary, while no restore since the `Ready`; with a restore
nothing, and `RawNode.Step` took a `MsgSnap` only with an empty queue.) -/
abbrev ackInv (γ : RaftNames) (rs : RNState) (s : NState) : IProp GF :=
  iprop(∀ (t : w64) (b : entryID) (e : Option entryID) (sn : Option SnapshotM)
      (_ : Pending.appendAck t b e sn ∈ rs.steps),
    storedRecs γ b s.logst.stored ∗ ackArm γ t b e sn s)

instance ackInv_pers (γ : RaftNames) (rs : RNState) (s : NState) :
    Persistent (ackInv (GF := GF) γ rs s) := by
  unfold ackInv; infer_instance

/-- No storage acknowledgement queued: nothing to keep. -/
theorem ackInv_none (γ : RaftNames) (rs : RNState) (s : NState)
    (h : ∀ t b e sn, Pending.appendAck t b e sn ∉ rs.steps) :
    ⊢ ackInv (GF := GF) γ rs s := by
  unfold ackInv
  iintro %t %b %e %sn %hm
  exact absurd hm (h t b e sn)

theorem ackLostW_mono (γ : RaftNames) (t : w64) (b : entryID) (es : List EntryM) {ip ip' : w64}
    (h : uint.Z ip ≤ uint.Z ip') :
    ackLostW (GF := GF) γ t b es ip ⊢ ackLostW γ t b es ip' := by
  unfold ackLostW
  iintro (%H | ⟨%c, %G, %Hc, #HG⟩)
  · ileft; ipureintro; omega
  · iright; iexists c, G; iframe HG; ipureintro
    exact ⟨Hc.1, by omega, Hc.2.2.1, Hc.2.2.2⟩

/-- **`ackInv` across a step that keeps the boundary, the pending snapshot and what the storage
holds**, does not move the term back nor `offsetInProgress` (every step but a `MsgSnap`'s and a
truncating `MsgApp`'s), with the queue unchanged. -/
theorem ackInv_keep (γ : RaftNames) {rs rs' : RNState} {s s' : NState}
    (hst : rs'.steps = rs.steps) (Hstok : StepsOk s rs.steps)
    (hterm : uint.Z s.term ≤ uint.Z s'.term)
    (hpv : s'.logst.prev = s.logst.prev) (hsn : s'.logst.snap = s.logst.snap)
    (hsd : s'.logst.stored = s.logst.stored)
    (hip : uint.Z s.logst.inprogress ≤ uint.Z s'.logst.inprogress) :
    ackInv (GF := GF) γ rs s ⊢ ackInv γ rs' s' := by
  iintro #H
  unfold ackInv
  iintro %t %b %e %sn %hm
  rw [hst] at hm
  have Hpo := stepsOk_ack Hstok hm
  icases H $$ %t %b %e %sn %hm with ⟨#Hr, #Ha⟩
  unfold ackArm
  rw [hsd, hpv, hsn]
  iframe Hr
  icases Ha with (⟨%Hp, #Hl⟩ | ⟨%Hp, #Hb⟩)
  · ileft
    isplitr
    · ipureintro; exact Hp
    iintro %ht
    ihave #Hl' := Hl $$ %(ack_term_back Hpo.1 hterm ht)
    iapply ackLostW_mono γ t b _ hip $$ Hl'
  · iright
    isplitr
    · ipureintro; exact Hp
    iintro %ht
    iapply Hb $$ %(And.intro ht.1 (ack_term_back Hpo.1 hterm ht.2))

/-- (D22 S-d3b) **A restore's mark, established** (`ackBaseW`, the pure core): with what the
storage holds after `b` (`es`) agreeing with a log `G2` of the leader of `t` that has the restored
snapshot `p`'s entry, down from `p` (Log Matching, `RecsAgree`), `es` agrees with the node's log
below `offsetInProgress` `ip` (`persistRel_agree`), and the cut above it (`ackLostW`: `G` agrees
with `G2`, `leadFull_agree`), `es` having `p`'s term at `p` would make the log have it, against the
restore's `!matchTerm`. -/
theorem nobase_core {b p : entryID} {es R G2 : List EntryM} {ip : w64}
    (HwE : PlogWf b es) (HwG : PlogWfR base0 G2) (HRA : RecsAgree b es base0 G2)
    (HG2 : plogTermAt base0 G2 p.index' = some p.term')
    (Hbp : uint.Z b.index' < uint.Z p.index')
    (Hagree : ∀ j : w64, uint.Z b.index' < uint.Z j → uint.Z j < uint.Z ip →
      plogTermAt b R j = plogTermAt b es j)
    (Hnm : ¬ PlogMatches b R p)
    (Hcut : plogLastIndexZ b es < uint.Z ip ∨
      ∃ (c : w64), uint.Z b.index' < uint.Z c ∧ uint.Z c ≤ uint.Z ip ∧
        ((plogTermAt base0 G2 c).isSome → plogTermAt base0 G2 c ≠ plogTermAt b es c)) :
    plogTermAt b es p.index' ≠ some p.term' := by
  intro Hes
  have Hmd := plog_match_down b es base0 G2 p.index' (PlogWf_wfR _ _ HwE) HwG HRA
    (by rw [Hes]; rfl) (by rw [Hes, HG2])
  have Hrange := plogTermAt_some_range _ _ _ _ Hes
  by_cases hlt : uint.Z p.index' < uint.Z ip
  · apply Hnm
    unfold PlogMatches
    rw [Hagree _ Hbp hlt]; exact Hes
  · rcases Hcut with Hc | ⟨c, Hc1, Hc2, Hc3⟩
    · omega
    · have hG2c : (plogTermAt base0 G2 c).isSome := by
        apply full_term_at_some G2 c p.index' (by rw [HG2]; rfl) (by omega)
      apply Hc3 hG2c
      exact (Hmd c (by omega) (by rw [base0_index]; exact uint_Z_nonneg _) (by omega)).symm

/-- (D22 S-d3b) **The acknowledgement misses after a restore**: an entry `x` of what the storage
holds after `b` (or `b` itself) is not where the log (at a later boundary `p`, `es` without `p`'s
entry) would hit, by Log Matching between the two logs' records (`stored_agree`'s, across
boundaries). -/
theorem stableHit_miss {b : entryID} {es : List EntryM} {ls : LogState}
    (HwE : PlogWf b es) (HwR : PlogWf ls.prev (ls.sents ++ ls.uents))
    (HRA : RecsAgree b es ls.prev (ls.sents ++ ls.uents))
    (Hbp : uint.Z b.index' < uint.Z ls.prev.index')
    (Hnb : plogTermAt b es ls.prev.index' ≠ some ls.prev.term') :
    ¬ StableHit ls (plogLast b es) := by
  rintro ⟨⟨Ho, -⟩, Ht⟩
  unfold logOffset at Ho
  have Hli := plogLast_index b es HwE
  have HtE : plogTermAt b es (plogLast b es).index' = some (plogLast b es).term' := by
    cases Hl : es.getLast? with
    | none =>
      have : es = [] := List.getLast?_eq_none_iff.mp Hl
      subst this
      simp only [plogLast, List.getLast?_nil] at Ho ⊢
      exfalso; omega
    | some x =>
      have Hk := getLast?_some_getElem? es x Hl
      have He : plogLast b es = entId x := by simp [plogLast, Hl]
      have Hpos : 0 < es.length := by
        cases es with
        | nil => simp at Hl
        | cons _ _ => simp
      have Hx := HwE _ _ Hk
      rw [He]
      exact plogTermAt_lookup b es _ _ x Hk (by simp only [entId]; push_cast at Hx ⊢; omega)
  have Hmd := plog_match_down b es ls.prev (ls.sents ++ ls.uents) (plogLast b es).index'
    (PlogWf_wfR _ _ HwE) (PlogWf_wfR _ _ HwR) HRA (by rw [HtE]; rfl) (by rw [HtE, Ht])
  have := Hmd ls.prev.index' (by omega) (Int.le_refl _) (by omega)
  rw [plogTermAt_base] at this
  exact Hnb this

/-- (D22 S-d3b) A restore's mark carried to a later restore (the pure core): `es` without the
boundary `p`'s term at `p`, and logs of the leader of the term with `p` (`Gp`) and with the new
boundary `q` (`G2`, past `p`): `es` with `q`'s term at `q` would agree with `G2` down to `p`, where
`G2` agrees with `Gp`. -/
theorem nobase_core2 {b p q : entryID} {es G2 : List EntryM}
    (HwE : PlogWf b es) (HwG : PlogWfR base0 G2) (HRA : RecsAgree b es base0 G2)
    (HG2 : plogTermAt base0 G2 q.index' = some q.term')
    (Hbp : uint.Z b.index' < uint.Z p.index') (Hpq : uint.Z p.index' ≤ uint.Z q.index')
    (HGp : (plogTermAt base0 G2 p.index').isSome → plogTermAt base0 G2 p.index' = some p.term')
    (Hnb : plogTermAt b es p.index' ≠ some p.term') :
    plogTermAt b es q.index' ≠ some q.term' := by
  intro Hes
  have Hmd := plog_match_down b es base0 G2 q.index' (PlogWf_wfR _ _ HwE) HwG HRA
    (by rw [Hes]; rfl) (by rw [Hes, HG2])
  have hG2p : (plogTermAt base0 G2 p.index').isSome :=
    full_term_at_some G2 p.index' q.index' (by rw [HG2]; rfl) Hpq
  apply Hnb
  rw [Hmd p.index' (by omega) (by rw [base0_index]; exact uint_Z_nonneg _) Hpq]
  exact HGp hG2p

/-- (D22 S-d3b) A `MsgApp`'s entries are in its leader's log (`isMessage`'s `app`, as a full log
from the start, `leadFull`). -/
theorem isMessage_app_leadFull (γ : RaftNames) (m : MessageM) (ents : List EntryM) :
    isMessage (GF := GF) γ (absMsg .app m ents) ⊢
      □ (∀ e, ⌜e ∈ ents⌝ -∗ ∃ G, leadFull γ m.Term' G ∗
          ⌜plogTermAt base0 G e.Index' = some e.Term'⌝) := by
  unfold isMessage absMsg absMsgFrom
  iintro ⟨%Hpay, -, ⟨%bL, %l, %fp, #Hlp, %Hpure, #Hfull, -⟩, -⟩
  imodintro
  iintro %e %He
  iexists fp ++ l
  isplitr
  · iapply leadFull_intro γ m.From' m.Term' bL l fp $$ Hlp Hfull
  icases lpfull_fp γ m.From' m.Term' bL l fp $$ Hfull with ⟨-, %Hfp⟩
  ipureintro
  obtain ⟨Hwf, Hnw⟩ := Hpay
  simp only [Msg.mkV] at Hwf Hnw Hpure
  obtain ⟨k, Hk⟩ := List.getElem?_of_mem He
  have Hki := Hwf k e Hk
  have Hkl : k < ents.length := (List.getElem?_eq_some_iff.1 Hk).1
  have Hb := plog_prefix_batch bL l (entryID.mk m.LogTerm' m.Index') ents Hnw Hpure.1 Hpure.2
    e.Index' (by simp only at Hki ⊢; push_cast at Hki; omega)
    (by simp only at Hki ⊢; push_cast at Hki; omega)
  have Hr := (plogTermAt_some_range _ _ _ _ Hpure.1).1
  rw [full_term_at bL fp l _ Hfp.1 (by simp only at Hki Hr; push_cast at Hki; omega), Hb]
  exact plogTermAt_lookup _ ents _ k e Hk (by simp only at Hki ⊢; exact Hki)

/-- (D22 S-d3b) A `MsgSnap`'s snapshot is in its leader's log (`isMessage`'s `snap`). -/
theorem isMessage_snap_leadFull (γ : RaftNames) (m : MessageM) (sv : SnapshotM)
    (voters : CSLists) :
    isMessage (GF := GF) γ (absSnap m sv voters) ⊢
      ∃ G, leadFull γ m.Term' G ∗
        ⌜plogTermAt base0 G (snapId sv).index' = some (snapId sv).term'⌝ := by
  unfold isMessage absSnap absSnapFrom
  iintro ⟨-, -, ⟨%bL, %l, %fp, #Hlp, %Hpure, #Hfull, -⟩, -⟩
  iexists fp ++ l
  isplitr
  · iapply leadFull_intro γ m.From' m.Term' bL l fp $$ Hlp Hfull
  icases lpfull_fp γ m.From' m.Term' bL l fp $$ Hfull with ⟨-, %Hfp⟩
  ipureintro
  simp only [Msg.mkS] at Hpure
  have Hr := (plogTermAt_some_range _ _ _ _ Hpure).1
  show plogTermAt base0 (fp ++ l) sv.Metadata'.Index' = some sv.Metadata'.Term'
  rw [full_term_at bL fp l _ Hfp.1 Hr]
  exact Hpure

/-- (D22 S-d3b) **`ackInv` across a `MsgApp`'s step**: as `ackInv_keep`, but for `offsetInProgress`,
which a truncation moves back (`AppTrunc`) -- to a cut, an entry of the message's batch, which its
leader's log has (`isMessage_app_leadFull`) and the log, which agreed with `stored` there
(`persistRel_agree`), did not have. -/
theorem ackInv_app (γ : RaftNames) {rs rs' : RNState} {s s' : NState} {m : MessageM}
    {ents : List EntryM} (hst : rs'.steps = rs.steps) (Hstok : StepsOk s rs.steps)
    (hterm : uint.Z s.term ≤ uint.Z s'.term)
    (hpv : s'.logst.prev = s.logst.prev) (hsn : s'.logst.snap = s.logst.snap)
    (hsd : s'.logst.stored = s.logst.stored) (Htr : AppTrunc m ents s s')
    (Hrel : (∃ t b e sn, Pending.appendAck t b e sn ∈ rs.steps ∧ s.logst.prev = b ∧
        s.logst.snap = sn.map snapId) →
      ∀ j : w64, uint.Z s.logst.prev.index' < uint.Z j →
      uint.Z j < uint.Z s.logst.inprogress →
      plogTermAt s.logst.prev (s.logst.sents ++ s.logst.uents) j =
        plogTermAt s.logst.prev s.logst.stored j)
    (Hcm : uint.Z s.logst.prev.index' ≤ uint.Z s.logst.committed) :
    ⊢ ackInv (GF := GF) γ rs s -∗
      □ (∀ e, ⌜e ∈ ents⌝ -∗ ∃ G, leadFull γ m.Term' G ∗
          ⌜plogTermAt base0 G e.Index' = some e.Term'⌝) -∗
      ackInv γ rs' s' := by
  iintro #H #Hents
  by_cases hip : uint.Z s.logst.inprogress ≤ uint.Z s'.logst.inprogress
  · iapply ackInv_keep γ hst Hstok hterm hpv hsn hsd hip $$ H
  have hlt : uint.Z s'.logst.inprogress < uint.Z s.logst.inprogress := by omega
  obtain ⟨Htm, Hcm', e, He, Hei, Hnm⟩ := Htr hlt
  unfold ackInv
  iintro %t %b %e0 %sn %hm
  rw [hst] at hm
  have Hpo := stepsOk_ack Hstok hm
  icases H $$ %t %b %e0 %sn %hm with ⟨#Hr, #Ha⟩
  unfold ackArm
  rw [hsd, hpv, hsn]
  iframe Hr
  icases Ha with (⟨%Hp, -⟩ | ⟨%Hp, #Hb⟩)
  · ileft
    isplitr
    · ipureintro; exact Hp
    iintro %ht
    have Hrel' := Hrel ⟨t, b, e0, sn, hm, Hp⟩
    obtain ⟨Hpb, -⟩ := Hp
    icases Hents $$ %e %He with ⟨%G, #HG, %HGe⟩
    rw [← ht, Htm]
    unfold ackLostW
    iright
    iexists s'.logst.inprogress, G
    iframe HG
    ipureintro
    have Hlt0 : uint.Z s.logst.prev.index' < uint.Z s'.logst.inprogress := by omega
    rw [← Hei] at Hlt0 ⊢
    refine ⟨by rw [← Hpb]; exact Hlt0, Int.le_refl _, by rw [HGe]; rfl, ?_⟩
    rw [HGe, ← Hpb, ← Hrel' _ Hlt0 (by rw [Hei]; exact hlt)]
    intro Hc
    exact Hnm Hc.symm
  · iright
    isplitr
    · ipureintro; exact Hp
    iintro %ht
    iapply Hb $$ %(And.intro ht.1 (ack_term_back Hpo.1 hterm ht.2))

/-- (D22 S-d3b) **`ackInv` across a `MsgSnap`'s step**: kept (`ackInv_keep`) if the log is (a stale
snapshot, or one the log has), and otherwise -- a restore past the commit index, of a snapshot the
message's leader's log has (`isMessage_snap_leadFull`) and the log had not -- the restored arm,
its mark established (`nobase_core`, from the cut, `ackLostW`; `nobase_core2`, from a mark). -/
theorem ackInv_snap (γ : RaftNames) {rs rs' : RNState} {s s' : NState} {m : MessageM}
    {sv : SnapshotM} (hst : rs'.steps = rs.steps) (Hstok : StepsOk s rs.steps)
    (hterm : uint.Z s.term ≤ uint.Z s'.term) (hsd : s'.logst.stored = s.logst.stored)
    (Hsl : SnapLogStep sv m s s')
    (Hrel : (∃ t b e sn, Pending.appendAck t b e sn ∈ rs.steps ∧ s.logst.prev = b ∧
        s.logst.snap = sn.map snapId) →
      ∀ j : w64, uint.Z s.logst.prev.index' < uint.Z j →
      uint.Z j < uint.Z s.logst.inprogress →
      plogTermAt s.logst.prev (s.logst.sents ++ s.logst.uents) j =
        plogTermAt s.logst.prev s.logst.stored j)
    (Hcm : uint.Z s.logst.prev.index' ≤ uint.Z s.logst.committed) :
    ⊢ ackInv (GF := GF) γ rs s -∗
      (∃ G, leadFull γ m.Term' G ∗
        ⌜plogTermAt base0 G (snapId sv).index' = some (snapId sv).term'⌝) -∗
      ackInv γ rs' s' := by
  iintro #H #HG2
  rcases Hsl with ⟨hpv, hsn, -, hip, -⟩ | ⟨Htm, hpv, hsn, -, Hgt, Hnm, -⟩
  · iapply ackInv_keep γ hst Hstok hterm hpv hsn hsd (by rw [hip]; exact Int.le_refl _) $$ H
  icases HG2 with ⟨%G2, #HG2, %HG2p⟩
  ihave ⟨%HwG2, #HrG2⟩ := leadFull_wf γ m.Term' G2 $$ HG2
  unfold ackInv
  iintro %t %b %e0 %sn %hm
  rw [hst] at hm
  have Hpo := stepsOk_ack Hstok hm
  icases H $$ %t %b %e0 %sn %hm with ⟨#Hr, #Ha⟩
  unfold ackArm
  rw [hsd, hpv]
  iframe Hr
  iunfold storedRecs at Hr
  icases Hr with ⟨%HwE, #HrE⟩
  icases logRecs_agree γ _ _ _ _ $$ HrE HrG2 with %HRA
  iright
  icases Ha with (⟨%Hp, #Hl⟩ | ⟨%Hp, #Hb⟩)
  · have Hrel' := Hrel ⟨t, b, e0, sn, hm, Hp⟩
    obtain ⟨Hpb, -⟩ := Hp
    isplitr
    · ipureintro
      show uint.Z b.index' < uint.Z sv.Metadata'.Index'
      rw [← Hpb]; omega
    iintro %ht
    have Ht0 : s.term = t := ack_term_back Hpo.1 hterm ht.2
    have HmT : m.Term' = t := Htm.symm.trans ht.2
    unfold ackBaseW
    isplitr
    · ihave #Hl' := Hl $$ %Ht0
      unfold ackLostW
      icases Hl' with (%Hc | ⟨%c, %G, %Hc, #HG⟩)
      · ipureintro
        rw [Hpb] at Hnm
        exact nobase_core HwE (PlogWf_wfR _ _ HwG2.1) HRA HG2p
          (by rw [← Hpb]; show _ < uint.Z sv.Metadata'.Index'; omega)
          (fun j h1 h2 => by rw [← Hpb]; exact Hrel' j (by rw [Hpb]; exact h1) h2) Hnm (.inl Hc)
      · rw [← HmT]
        ihave %Hag : ⌜(plogTermAt base0 G2 c).isSome →
            plogTermAt base0 G c = plogTermAt base0 G2 c⌝ $$ []
        · by_cases hs : (plogTermAt base0 G2 c).isSome
          · icases leadFull_agree γ m.Term' G G2 c Hc.2.2.1 hs $$ HG HG2 with %Hq
            ipureintro; exact fun _ => Hq
          · ipureintro; exact fun h => absurd h hs
        ipureintro
        rw [Hpb] at Hnm
        refine nobase_core HwE (PlogWf_wfR _ _ HwG2.1) HRA HG2p
          (by rw [← Hpb]; show _ < uint.Z sv.Metadata'.Index'; omega)
          (fun j h1 h2 => by rw [← Hpb]; exact Hrel' j (by rw [Hpb]; exact h1) h2) Hnm
          (.inr ⟨c, Hc.1, Hc.2.1, fun hs => ?_⟩)
        rw [← Hag hs]; exact Hc.2.2.2
    · iexists G2; rw [← HmT]; iframe HG2; ipureintro; exact HG2p
  · isplitr
    · ipureintro
      show uint.Z b.index' < uint.Z sv.Metadata'.Index'
      omega
    iintro %ht
    have Ht0 : s.term = t := ack_term_back Hpo.1 hterm ht.2
    have HmT : m.Term' = t := Htm.symm.trans ht.2
    ihave #Hb' := Hb $$ %(And.intro ht.1 Ht0)
    iunfold ackBaseW at Hb'
    icases Hb' with ⟨%Hnb, %Gp, #HGp, %HGpp⟩
    unfold ackBaseW
    isplitr
    · ihave %Hag : ⌜(plogTermAt base0 G2 s.logst.prev.index').isSome →
          plogTermAt base0 G2 s.logst.prev.index' = some s.logst.prev.term'⌝ $$ []
      · by_cases hs : (plogTermAt base0 G2 s.logst.prev.index').isSome
        · ihave #HGp' : leadFull γ m.Term' Gp $$ []
          · rw [HmT]; iexact HGp
          icases leadFull_agree γ m.Term' Gp G2 s.logst.prev.index' (by rw [HGpp]; rfl) hs
            $$ HGp' HG2 with %Hq
          ipureintro; exact fun _ => by rw [← Hq]; exact HGpp
        · ipureintro; exact fun h => absurd h hs
      ipureintro
      exact nobase_core2 HwE (PlogWf_wfR _ _ HwG2.1) HRA HG2p Hp
        (by show _ ≤ uint.Z sv.Metadata'.Index'; omega) Hag Hnb
    · iexists G2; rw [← HmT]; iframe HG2; ipureintro; exact HG2p

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
  icases Hr with ⟨%Hnl, ⟨%HC, #HM, #Hfr, Hcamp⟩, #Hcl⟩
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
  isplitl [Hcamp]
  · isplitr
    · ipureintro; exact HC
    iframe HM
    isplitr
    · iexact Hfr
    iexact Hcamp
  iexact Hcl

/-! ## The one predicate for a `RawNode` -/

/-- The persistent `stepDownOnRemoval` field (2026-10-14, stage B7 part 2): nobody writes it
after `newRaft`. (2026-10-14 to 2026-10-25 also on in the dynamic mode, so that a leader an
`ApplyConfChange` removes steps down; since T-M M2c either way: without it the leader stays
leader outside the configuration, `switchToConfig`.) -/
def sdrOk (r : Loc) (_md : RNMode) : IProp GF :=
  iprop(∃ b : Bool, r.[raft, go!"stepDownOnRemoval"] ↦□ b)

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

/-- (D22l) `prevHardSt`: a pointer to a read-only hard state `h` (`hsRO`), the record `ph`
(`RNState.phs`), with its witness (`phsWit`: the hard state of an earlier `Ready`, or zero). -/
def prevHS (γ : RaftNames) (p : Loc) (h ph : HardStateM) : IProp GF :=
  iprop(hsRO p h ∗ ⌜h = ph⌝ ∗ phsWit γ h)

instance prevHS_persistent (γ : RaftNames) (p : Loc) (h ph : HardStateM) :
    Persistent (prevHS (GF := GF) γ p h ph) := by
  unfold prevHS; infer_instance

theorem prevHS_hsRO (γ : RaftNames) (p : Loc) (h ph : HardStateM) :
    prevHS (GF := GF) γ p h ph ⊢ hsRO p h := by
  unfold prevHS; iintro ⟨#H, -, -⟩; iexact H

theorem prevHS_eq (γ : RaftNames) (p : Loc) (h ph : HardStateM) :
    prevHS (GF := GF) γ p h ph ⊢ ⌜h = ph⌝ := by
  unfold prevHS; iintro ⟨-, %H, -⟩; ipureintro; exact H

theorem prevHS_wit (γ : RaftNames) (p : Loc) (h ph : HardStateM) :
    prevHS (GF := GF) γ p h ph ⊢ phsWit γ ph := by
  unfold prevHS; iintro ⟨-, %H, #W⟩; subst H; iexact W

theorem prevHS_of_zero (γ : RaftNames) (p : Loc) (h : HardStateM) (Hz : h = hsZero) :
    hsRO (GF := GF) p h ⊢ prevHS γ p h hsZero := by
  unfold prevHS; iintro #H; iframe H; subst Hz
  isplitr; · ipureintro; rfl
  iapply phsWit_zero

theorem prevHS_intro (γ : RaftNames) (p : Loc) (h : HardStateM) :
    ⊢ hsRO (GF := GF) p h -∗ phsWit γ h -∗ prevHS γ p h h := by
  unfold prevHS; iintro #H #W; iframe H W; ipureintro; rfl

/-- (D22 S-d3a, 2026-10-21) The queue while a snapshot is lent (`RNState.slent`): half of the
snapshot handed out (the other half is the application's, `rd.Snapshot`), and the queue once the
whole snapshot is back -- its acknowledgement shares the pointer (`newStorageAppendRespMsg`). -/
abbrev lentPend (o : Option SnapLoan) (P : IProp GF) : IProp GF :=
  match o with
  | none => P
  | some l => iprop(ownSnapM l.ptr (DFrac.own (1 : Qp).half) l.snap ∗
      (ownSnapM l.ptr (DFrac.own 1) l.snap -∗ P))

/-- (2026-10-28, the conf-change decision switch) **A loan's decisions** (`SnapLoan.decs`): recorded
(`decLb`), and the loan's committed log folds over them to the snapshot's configuration in the
dynamic mode (its certificate's, `raftSnapCert_decs`): what `Advance` installs (`RNMode.foldCfg`). -/
def loanDec (γ : RaftNames) (l : SnapLoan) : IProp GF :=
  iprop(decLb γ l.decs ∗ ⌜∀ D, γ.dyn = some D →
    D.fold l.decs l.dlv = some (snapTrip l.snap l.snap.Metadata'.ConfState'.lists).cfgM⌝)

instance loanDec_pers (γ : RaftNames) (l : SnapLoan) : Persistent (loanDec (GF := GF) γ l) := by
  unfold loanDec; infer_instance

/-- (2026-10-28, the decision switch) A lower bound of the decisions joins the ghost part, in
either mode (`ownStepGhost_absorb`). -/
theorem ownStepGhost_absorbM (γ : RaftNames) (mode : RNMode) (g : RGh) (c : CfgM) (id : w64)
    (s : NState) (M : DecMap) :
    decLb (GF := GF) γ M ∗ ownStepGhost γ (mode.toG g) c id s ⊢
      ⌜M ⊆ g.decs ∪ M ∨ mode.isDyn = false⌝ ∗
        ownStepGhost γ (mode.toG { g with decs := g.decs ∪ M }) c id s := by
  cases mode with
  | static =>
    have e : ∀ g' : RGh, RNMode.static.toG g' = GMode.static := fun _ => rfl
    rw [e, e]
    iintro ⟨-, H⟩
    isplitr
    · ipureintro; right; rfl
    iexact H
  | dyn dec c0 h0 h1 =>
    iintro ⟨#HM, H⟩
    simp only [RNMode.toG]
    icases (ownStepGhost_dyn γ dec c0 h0 g c id s).1 $$ H with ⟨%Hp, #Hg, Hr, #Hl⟩
    icases decLb_compat γ g.decs M $$ [Hg HM] with %Hc
    · iframe Hg HM
    ihave H := (ownStepGhost_dyn γ dec c0 h0 g c id s).2 $$ [Hr]
    · iframe Hg Hr Hl; ipureintro; exact Hp
    isplitr
    · ipureintro; left; exact DecCompat.sub_right Hc
    iapply ownStepGhost_absorb γ dec c0 h0 g c id s M
    iframe HM H

/-- (2026-10-28, the conf-change decision switch) **A1 over the client's decisions**: in the dynamic
mode, every conf entry of `D` at the positions `[lo, hi)` is rejected by the mode's decoder over
some decisions recorded (`NoUndecConfIn`, `decLb`): skipped. (Until then no conf entry at all,
`NoConfIn`.) Nothing in the static mode. Persistent. -/
def undecFree (γ : RaftNames) (md : RNMode) (D : List EntryM) (lo hi : Nat) : IProp GF :=
  iprop(∃ M : DecMap, decLb γ M ∗ ⌜∀ dec c0 h0 h1, md = .dyn dec c0 h0 h1 →
    NoUndecConfIn (effDec dec M) D lo hi⌝)

instance undecFree_pers (γ : RaftNames) (md : RNMode) (D : List EntryM) (lo hi : Nat) :
    Persistent (undecFree (GF := GF) γ md D lo hi) := by
  unfold undecFree; infer_instance

theorem undecFree_noConf (γ : RaftNames) (md : RNMode) {D : List EntryM} {lo hi : Nat}
    (h : NoConfIn D lo hi) : ⊢ undecFree (GF := GF) γ md D lo hi := by
  unfold undecFree
  iexists ∅
  isplitr; · iapply decLb_empty
  ipureintro; intro _ _ _ _ _; exact h.noUndec

theorem undecFree_empty (γ : RaftNames) (md : RNMode) (D : List EntryM) (a : Nat) :
    ⊢ undecFree (GF := GF) γ md D a a :=
  undecFree_noConf γ md (fun _ _ _ h2 _ => absurd h2 (by omega))

theorem undecFree_static (γ : RaftNames) {md : RNMode} (h : md.isDyn = false) (D : List EntryM)
    (lo hi : Nat) : ⊢ undecFree (GF := GF) γ md D lo hi := by
  unfold undecFree
  iexists ∅
  isplitr; · iapply decLb_empty
  ipureintro; intro _ _ _ _ hm; rw [hm] at h; cases h

theorem undecFree_mono (γ : RaftNames) (md : RNMode) {D : List EntryM} {lo hi lo' hi' : Nat}
    (h1 : lo ≤ lo') (h2 : hi' ≤ hi) :
    undecFree (GF := GF) γ md D lo hi ⊢ undecFree γ md D lo' hi' := by
  unfold undecFree
  iintro ⟨%M, #HM, %H⟩
  iexists M
  iframe HM
  ipureintro; intro dec c0 h0 h1' hm; exact (H dec c0 h0 h1' hm).mono h1 h2

theorem undecFree_prefix (γ : RaftNames) (md : RNMode) {D D' : List EntryM} {lo hi : Nat}
    (hp : D <+: D') (hh : hi ≤ D.length) :
    undecFree (GF := GF) γ md D lo hi ⊢ undecFree γ md D' lo hi := by
  unfold undecFree
  iintro ⟨%M, #HM, %H⟩
  iexists M
  iframe HM
  ipureintro; intro dec c0 h0 h1 hm; exact (H dec c0 h0 h1 hm).prefix hp hh

theorem undecFree_of_prefix (γ : RaftNames) (md : RNMode) {D D' : List EntryM} {lo hi : Nat}
    (hp : D <+: D') (hh : hi ≤ D.length) :
    undecFree (GF := GF) γ md D' lo hi ⊢ undecFree γ md D lo hi := by
  unfold undecFree
  iintro ⟨%M, #HM, %H⟩
  iexists M
  iframe HM
  ipureintro; intro dec c0 h0 h1 hm; exact (H dec c0 h0 h1 hm).of_prefix hp hh

/-- With more decisions recorded (`M`, which joins the witness). -/
theorem undecFree_join (γ : RaftNames) (md : RNMode) (D : List EntryM) (lo hi : Nat) (M : DecMap) :
    decLb (GF := GF) γ M ∗ undecFree γ md D lo hi ⊢
      ∃ M' : DecMap, decLb γ M' ∗ ⌜M ⊆ M'⌝ ∗
        ⌜∀ dec c0 h0 h1, md = .dyn dec c0 h0 h1 → NoUndecConfIn (effDec dec M') D lo hi⌝ := by
  unfold undecFree
  iintro ⟨#HM, %M2, #HM2, %H⟩
  icases decLb_compat γ M M2 $$ [HM HM2] with %Hc
  · iframe HM HM2
  ihave #Hu := decLb_union γ M M2 $$ [HM HM2]
  · iframe HM HM2
  iexists M ∪ M2
  iframe Hu
  ipureintro
  refine ⟨DecCompat.sub_left M M2, fun dec c0 h0 h1 hm => ?_⟩
  exact (H dec c0 h0 h1 hm).mono_dec (effDec_mono dec (DecCompat.sub_right Hc))

theorem undecFree_trans (γ : RaftNames) (md : RNMode) (D : List EntryM) (a b c : Nat) :
    undecFree (GF := GF) γ md D a b ∗ undecFree γ md D b c ⊢ undecFree γ md D a c := by
  iintro ⟨H1, H2⟩
  ihave ⟨%M1, #HM1, %H1p⟩ : iprop(∃ M : DecMap, decLb γ M ∗ ⌜∀ dec c0 h0 h1, md = .dyn dec c0 h0 h1 →
      NoUndecConfIn (effDec dec M) D a b⌝) $$ [H1]
  · unfold undecFree; iexact H1
  icases undecFree_join γ md D b c M1 $$ [HM1 H2] with ⟨%M', #HM', %Hsub, %H2p⟩
  · iframe HM1 H2
  unfold undecFree
  iexists M'
  iframe HM'
  ipureintro; intro dec c0 h0 h1 hm
  exact ((H1p dec c0 h0 h1 hm).mono_dec (effDec_mono dec Hsub)).trans (H2p dec c0 h0 h1 hm)

/-- `loanDec` of a loan, if any (what the driver holds of a `Ready`'s loan, `nodeDriverBusy`). -/
def loanDecO (γ : RaftNames) : Option SnapLoan → IProp GF
  | none => iprop(True)
  | some l => loanDec γ l

instance loanDecO_pers (γ : RaftNames) (o : Option SnapLoan) : Persistent (loanDecO (GF := GF) γ o) := by
  cases o <;> unfold loanDecO <;> infer_instance

/-- (D22 S-d3a) The committed log up to a lent snapshot (`SnapLoan.dlv`); (2026-10-28, stage U0)
and the snapshot's `ConfState` naming a node (the pending one's, `pendKsn`): what makes its
certificate's facts hold when `Advance` applies it (`raft.Step`'s `SnapAckOk`); (stage U3c) and the
committed log ending at the snapshot's id (`ownRawNodeReady_loanLast`), so that it is the full prefix
the certificate's dynamic clause speaks of (`SnapAckDyn`); (2026-10-28) and its decisions
(`loanDec`). -/
abbrev loanCom (γ : RaftNames) (o : Option SnapLoan) : IProp GF :=
  match o with
  | none => iprop(True)
  | some l => iprop(isCommitted γ l.dlv ∗ loanDec γ l ∗ ⌜(∃ x, l.snap.Metadata'.ConfState'.lists.Has x) ∧
      plogLast base0 l.dlv = snapId l.snap⌝)

instance loanCom_pers (γ : RaftNames) (o : Option SnapLoan) :
    Persistent (loanCom (GF := GF) γ o) := by
  cases o <;> unfold loanCom <;> infer_instance

/-- (2026-10-26, D22 J2, R-loc) **The pending snapshot is local to the node**: the receiver-local
fact (`snapLocal`, `RaftNames.reSnapLoc`) of the pending snapshot's index, if one is pending.
`RawNode.Step` of a `MsgSnap` sets it from the message's (`netP`); every other step keeps or clears
the pending snapshot; a `Ready` that hands the snapshot out reads it (`ownRawNode_loanLoc`). -/
def snapLocOk (γ : RaftNames) (id : w64) (o : Option entryID) : IProp GF :=
  match o with
  | none => iprop(True)
  | some p => snapLocal γ id p.index'

instance snapLocOk_pers (γ : RaftNames) (id : w64) (o : Option entryID) :
    Persistent (snapLocOk (GF := GF) γ id o) := by
  cases o <;> unfold snapLocOk <;> infer_instance

/-- No snapshot pending: nothing to know. -/
theorem snapLocOk_none (γ : RaftNames) (id : w64) : ⊢ snapLocOk (GF := GF) γ id none := by
  unfold snapLocOk; iintro; itrivial

/-- The fact at a pending snapshot of index `i`. -/
theorem snapLocOk_some (γ : RaftNames) (id : w64) (p : entryID) :
    snapLocOk (GF := GF) γ id (some p) ⊣⊢ snapLocal γ id p.index' := by
  unfold snapLocOk; exact .rfl

/-- A step that keeps the pending snapshot or clears it keeps the fact. -/
theorem snapLocOk_keep (γ : RaftNames) (id : w64) {o o' : Option entryID}
    (h : o' = o ∨ o' = none) : snapLocOk (GF := GF) γ id o ⊢ snapLocOk γ id o' := by
  rcases h with h | h
  · rw [h]
  · rw [h]; iintro -; iapply snapLocOk_none

/-- No snapshot pending unless one was stepped or lent (`ownRawNode`'s `Hsnap`): nothing to know. -/
theorem snapLocOk_of_snap (γ : RaftNames) (id : w64) {o : Option entryID} {P : Prop}
    (hs : P → o = none) (hp : P) : ⊢ snapLocOk (GF := GF) γ id o := by
  rw [hs hp]; iapply snapLocOk_none

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
  iprop(∃ (s : NState) (cf : CfgM) (fp : List EntryM) (ds : DecMap) (rnv : RawNode) (sv : SoftState)
      (hprev : HardStateM) (steps : List Loc),
  "Hrn" ∷ rawNodeOwn rn rnv ∗
  "Hphys" ∷ ownRaftPhysCV cf cf.voters rnv.raft' id s ∗
  "Hghost" ∷ ownStepGhost γ (rs.mode.toG ⟨rs.capplied, rs.cfg, fp, ds⟩) cf id s ∗
  "#Hsdrf" ∷ sdrOk rnv.raft' rs.mode ∗
  "%Hwf" ∷ ⌜NStateWf s⌝ ∗
  -- scope (static mode): the node is a voter (`Step`'s premise for a snapshot; a shrinking
  -- `ApplyConfChange`'s). (From 2026-10-14 to 2026-10-29, stage U5, also no auto-leave joint
  -- configuration, `cf.autoLeave = false`: `appliedTo`'s automatic leave was out of `raft.Step`'s
  -- scope.)
  "%Hin" ∷ ⌜rs.mode = .static → id ∈ γ.reCfg⌝ ∗
  -- scope: synchronous storage writes (`Config.AsyncStorageWrites` unset); `NewRawNode`
  -- copies the `Config` field
  "%Hasync" ∷ ⌜rnv.asyncStorageWrites' = false⌝ ∗
  -- `prevSoftSt`: a pointer to a `SoftState` nobody writes (it is either `NewRawNode`'s
  -- or a `Ready.SoftState`), held read-only; (2026-10-16, stage R5) `prevHardSt`: a pointer
  -- to a read-only hard state (`NewRawNode`'s `r.hardState()` or a `Ready.HardState`)
  "#Hsoft" ∷ rnv.prevSoftSt' ↦□ sv ∗
  "#Hhard" ∷ prevHS γ rnv.prevHardSt' hprev rs.phs ∗
  "Hsteps" ∷ rnv.stepsOnAdvance' ↦* steps ∗
  "Hsteps_cap" ∷ ownSliceCap Loc rnv.stepsOnAdvance' (DFrac.own 1) ∗
  -- (2026-10-16, stage R5) each queued message owned, with its record (until then
  -- `pendingRel` of the Goose value, persistent, and `pendingOwn`)
  -- (D22 S-d3a) while a snapshot is lent, half of it, the queue once it is whole (`lentPend`)
  "Hpend" ∷ lentPend rs.slent (pendList γ id steps rs.steps) ∗
  "#Hdeliv" ∷ isCommitted γ rs.delivered ∗
  -- the records of what the storage holds (2026-10-10), for the acknowledgement
  -- `Advance` steps (`PendingOk`, `stableOk_of_stored`)
  -- (2026-10-20, D22 S-c to D22 S-d3a: while no snapshot may be pending, `storedRecsP`) (D22
  -- S-d3b) at the `Ready`'s boundary, with what the acknowledgement's miss after a restore needs
  -- (`ackInv`)
  "#Hstrecs" ∷ ackInv γ rs s ∗
  -- (D22 S-d3a) the committed log up to a lent snapshot
  "#Hloanc" ∷ loanCom γ rs.slent ∗
  "%Hdlen" ∷ ⌜rs.delivered.length = (uint.Z s.logst.applying).toNat⌝ ∗
  "%Hunp" ∷ ⌜rs.unpersisted = s.logst.unpersisted⌝ ∗
  -- no snapshot pending unless a `MsgSnap` was stepped (`RNState.psnap`) or one is lent
  -- (`RNState.slent`, D22 S-d3a); until 2026-10-20, D22 S-c, none at all; (2026-10-28, stage U3c)
  -- in either mode (until then none in the dynamic mode, `DynNoSnap`)
  "%Hsnap" ∷ ⌜rs.psnap = false ∧ rs.slent = none → s.logst.snap = none⌝ ∗
  -- the queue is steppable (since 2026-10-10 unconditionally: until then only for an
  -- `advanceable` one)
  "%Hstok" ∷ ⌜StepsOk s rs.steps⌝ ∗
  "%Htrm" ∷ ⌜rs.term = s.term⌝ ∗
  "%Hstor" ∷ ⌜rs.storage = s.logst.storage⌝ ∗
  -- (2026-10-17; until then pre-vote off, `s.prevote = false`, its scope) in the dynamic mode a
  -- pre-candidate's campaign guard (2026-10-25, T-M M2b; until then pre-vote off there), and the
  -- term ceiling (`RNPv`)
  "%Hpvoff" ∷ ⌜RNPv rs fp s⌝ ∗
  -- the lower bounds for `node.go` (2026-10-10, `RNState.outlb`)
  "%Hrs_out" ∷ ⌜rs.outlb = s.gh.outlb⌝ ∗
  "%Hrs_unst" ∷ ⌜rs.unst = s.gh.unst⌝ ∗
  "%Hrs_clb" ∷ ⌜uint.Z rs.clb ≤ uint.Z s.logst.committed⌝ ∗
  -- (D19i part 1) the floor and `applied`
  "%Hrnfl" ∷ ⌜RNFl rs s⌝ ∗
  -- (D22 S-d3a) a snapshot `Ready`'s loan
  "%Hloan" ∷ ⌜LoanOk rs s⌝ ∗
  -- (2026-10-26, D22 J2, R-loc) the pending snapshot's receiver-local fact
  "#Hsloc" ∷ snapLocOk γ id s.logst.snap ∗
  -- (2026-10-28, stage U4a) the record of the storage's terms
  "%Hsdt" ∷ ⌜SdtTie rs s⌝)

/-- Closing the predicate; the pure premises are first, the resources in the order of
the definition. (2026-10-16, stage R5: the hard state `hprev` after the soft state; the
queue `pendList`, owned; no `pendingOwn`.) -/
theorem ownRawNode_intro (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState)
    (s : NState) (c : CfgM) (fp : List EntryM) {ds : DecMap} (rnv : RawNode) (sv : SoftState)
    (hprev : HardStateM) (steps : List Loc)
    (Hwf : NStateWf s) (Hin : rs.mode = .static → id ∈ γ.reCfg)
    (Hasync : rnv.asyncStorageWrites' = false)
    (Hdlen : rs.delivered.length = (uint.Z s.logst.applying).toNat)
    (Hunp : rs.unpersisted = s.logst.unpersisted)
    (Hsnap : rs.psnap = false ∧ rs.slent = none → s.logst.snap = none)
    (Hstok : StepsOk s rs.steps)
    (Htrm : rs.term = s.term) (Hstor : rs.storage = s.logst.storage)
    (Hpvoff : RNPv rs fp s) (Hrs_out : rs.outlb = s.gh.outlb)
    (Hrs_unst : rs.unst = s.gh.unst) (Hrs_clb : uint.Z rs.clb ≤ uint.Z s.logst.committed)
    (Hrnfl : RNFl rs s) (Hloan : LoanOk rs s) (Hsdt : SdtTie rs s) :
    ⊢ rawNodeOwn rn rnv -∗ ownRaftPhysCV c c.voters rnv.raft' id s -∗
      ownStepGhost (GF := GF) γ (rs.mode.toG ⟨rs.capplied, rs.cfg, fp, ds⟩) c id s -∗
      sdrOk rnv.raft' rs.mode -∗
      rnv.prevSoftSt' ↦□ sv -∗ prevHS γ rnv.prevHardSt' hprev rs.phs -∗ rnv.stepsOnAdvance' ↦* steps -∗
      ownSliceCap Loc rnv.stepsOnAdvance' (DFrac.own 1) -∗
      lentPend rs.slent (pendList γ id steps rs.steps) -∗
      isCommitted γ rs.delivered -∗
      ackInv γ rs s -∗
      loanCom γ rs.slent -∗
      -- (2026-10-26, D22 J2) the pending snapshot's receiver-local fact
      snapLocOk γ id s.logst.snap -∗
      ownRawNode γ rn id rs := by
  iintro Hrn Hphys Hghost #Hsdrf #Hsoft #Hhard Hsteps Hcap Hpend #Hdeliv #Hstrecs #Hloanc #Hsloc
  unfold ownRawNode
  iexists s, c, fp, ds, rnv, sv, hprev, steps
  simp only [named]
  iframe Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hcap Hpend Hdeliv Hstrecs Hloanc Hsloc
  ipureintro
  exact ⟨Hwf, Hin, Hasync, Hdlen, Hunp, Hsnap, Hstok, Htrm, Hstor, Hpvoff, Hrs_out,
    Hrs_unst, Hrs_clb, Hrnfl, Hloan, Hsdt⟩

/-! ### The static mode, as before (2026-10-14, stage B7 part 2)

In the static mode the struct's configuration has the ghost state's voters, not joint
(`CfgStatic`): the struct and the ghost state can be read as `ownRawNode` held them until
stage B7 part 2 -- `ownRaftPhys γ.reCfg` and `ownRaftGhost` -- for the proofs that are about
the static mode only (a shrinking `ApplyConfChange`, `node.go`'s loop). -/

theorem ownRawNode_static_open (γ : RaftNames) (rs : RNState) (Hm : rs.mode = .static)
    (fp : List EntryM) (ds : DecMap) (cf : CfgM) (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhysCV (GF := GF) cf cf.voters r id s -∗
      ownStepGhost γ (rs.mode.toG ⟨rs.capplied, rs.cfg, fp, ds⟩) cf id s -∗
      ownRaftPhys γ.reCfg r id s ∗ ownRaftGhost γ id (toPState s) ∗
      -- (D19p, 2026-10-18) the tracker within the tracked bound
      ⌜TrackedOk γ (CfgM.simple γ.reCfg (domSet s.progress \ γ.reCfg)) id⌝ ∗
      -- (2026-10-19, D21 M3)
      ⌜NsLink γ s⌝ ∗
      -- (D22 S-b′3) the storage's certificate link
      certLink γ s.logst.storage := by
  iintro Hphys Hghost
  rw [Hm]
  simp only [RNMode.toG, ownStepGhost, ghostRest, ghostRestM, GMode.isDyn]
  icases Hghost with ⟨Hghost, %Hnl, %HC, #Hcl⟩
  icases ownRaftPhysC_toPhys cf r id s HC.1.2.1 $$ Hphys with ⟨Hphys, %Hlrn⟩
  rw [HC.1.1] at Hlrn ⊢
  iframe Hphys Hghost
  isplitr
  · ipureintro
    exact TrackedOk.of_eq (by rw [CfgM.voters_simple, CfgStatic.voters HC.1])
      (by rw [Hlrn]; rfl) HC.2
  iframe Hcl
  ipureintro; exact Hnl

theorem ownRawNode_intro_static (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState)
    (s : NState) (ps : PState) (rnv : RawNode) (sv : SoftState) (hprev : HardStateM)
    (steps : List Loc)
    (Hm : rs.mode = .static)
    (Hrel : NStateRel s ps) (Hin : id ∈ γ.reCfg) (Hasync : rnv.asyncStorageWrites' = false)
    (Hdlen : rs.delivered.length = (uint.Z s.logst.applying).toNat)
    (Hunp : rs.unpersisted = s.logst.unpersisted)
    (Hsnap : rs.psnap = false ∧ rs.slent = none → s.logst.snap = none)
    (Hstok : StepsOk s rs.steps)
    (Htrm : rs.term = s.term) (Hstor : rs.storage = s.logst.storage)
    {fp : List EntryM} (Hpvoff : RNPv rs fp s) (Hrs_out : rs.outlb = s.gh.outlb)
    (Hrs_unst : rs.unst = s.gh.unst) (Hrs_clb : uint.Z rs.clb ≤ uint.Z s.logst.committed)
    (Hrnfl : RNFl rs s) (Hloan : LoanOk rs s) (Hsdt : SdtTie rs s)
    -- (D19p, 2026-10-18) the tracker within the ghost state's tracked bound
    (Htrk : TrackedOk γ (CfgM.simple γ.reCfg (domSet s.progress \ γ.reCfg)) id)
    -- (2026-10-19, D21 M3) the no-snapshot mode only with a bootstrap log
    (Hnl : NsLink γ s) :
    ⊢ rawNodeOwn rn rnv -∗ ownRaftPhys γ.reCfg rnv.raft' id s -∗
      ownRaftGhost (GF := GF) γ id ps -∗ sdrOk rnv.raft' rs.mode -∗
      rnv.prevSoftSt' ↦□ sv -∗ prevHS γ rnv.prevHardSt' hprev rs.phs -∗ rnv.stepsOnAdvance' ↦* steps -∗
      ownSliceCap Loc rnv.stepsOnAdvance' (DFrac.own 1) -∗
      lentPend rs.slent (pendList γ id steps rs.steps) -∗
      isCommitted γ rs.delivered -∗
      ackInv γ rs s -∗
      loanCom γ rs.slent -∗
      -- (D22 S-b′3) the storage's certificate link
      certLink γ s.logst.storage -∗
      -- (2026-10-26, D22 J2) the pending snapshot's receiver-local fact
      snapLocOk γ id s.logst.snap -∗
      ownRawNode γ rn id rs := by
  iintro Hrn Hphys Hghost #Hsdrf #Hsoft #Hhard Hsteps Hcap Hpend #Hdeliv #Hstrecs #Hloanc #Hcl #Hsloc
  obtain ⟨rfl, Hwf⟩ := Hrel
  ihave %Hst := ownRaftGhost_static γ id _ $$ Hghost
  ihave Hphys := ownRaftPhys_toC' $$ Hphys
  ihave Hghost : ownStepGhost γ (rs.mode.toG ⟨rs.capplied, rs.cfg, [], ∅⟩)
      (CfgM.simple γ.reCfg (domSet s.progress \ γ.reCfg)) id s $$ [Hghost]
  · rw [Hm]
    simp only [RNMode.toG, ownStepGhost, ghostRest, ghostRestM, GMode.isDyn]
    iframe Hghost Hcl
    isplitr
    · ipureintro; exact Hnl
    ipureintro; exact ⟨CfgStatic.simple γ _ Hst, Htrk⟩
  iapply ownRawNode_intro γ rn id rs s _ [] rnv sv hprev steps Hwf (fun _ => Hin) Hasync Hdlen
    Hunp Hsnap Hstok Htrm Hstor (Hpvoff.static_fp Hm) Hrs_out Hrs_unst Hrs_clb Hrnfl Hloan
    Hsdt $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hcap Hpend Hdeliv Hstrecs Hloanc Hsloc

/-- The mode is the ghost state's (2026-10-14, stage B7 part 2): static exactly when `γ` is. -/
theorem ownRawNode_mode (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) :
    ⊢ ownRawNode (GF := GF) γ rn id rs -∗
      ⌜(rs.mode = .static ↔ γ.reDyn = none)⌝ ∗ ownRawNode γ rn id rs := by
  iintro H
  iNamed H
  iunfold ownStepGhost at Hghost
  icases Hghost with ⟨Hg, Hr⟩
  ihave %Hm := ownRaftGhost_mode γ id (toPState s) (md := (rs.mode.toG _).isDyn) $$ Hg
  ihave Hghost : ownStepGhost γ (rs.mode.toG ⟨rs.capplied, rs.cfg, fp, ds⟩) cf id s $$ [Hg Hr]
  · iunfold ownStepGhost; iframe Hg Hr
  isplitr
  · ipureintro
    rw [RNMode.toG_isDyn] at Hm
    cases hm : rs.mode with
    | static => rw [hm] at Hm; simp [RNMode.isDyn] at Hm; simp [Hm]
    | dyn dec c0 h0 _ => rw [hm] at Hm; simp [RNMode.isDyn] at Hm; simp [Option.isSome_iff_ne_none.1 Hm]
  iapply ownRawNode_intro γ rn id rs s cf fp rnv sv hprev steps Hwf Hin Hasync Hdlen Hunp Hsnap
    Hstok Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb Hrnfl Hloan
    Hsdt $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstrecs Hloanc Hsloc

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

/-- (2026-10-29, stage U4) **At term `0` a node's log is empty** (`ownLogGhost_term0`), in every
cluster: what `NetMsgOk.raftStep` needs of a pre-vote request at term `0`, which is granted
(`plogUpToDate_base0`; a rejection would be sent at term `0`, which `send` refuses). Replaces
`ownStepGhost_boot_term`'s use there, which needed a bootstrap log. -/
theorem ownStepGhost_term0 (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) (s : NState) :
    ownStepGhost (GF := GF) γ md c id s ⊢
      ⌜s.term = W64 0 → plogLast s.logst.prev (s.logst.sents ++ s.logst.uents) = base0⌝ ∗
      ownStepGhost γ md c id s := by
  apply persistent_entails_right
  iintro H
  iunfold ownStepGhost at H
  icases H with ⟨Hg, -⟩
  iunfold ownRaftGhost at Hg
  icases Hg with ⟨%γv, %voted, %kl, H⟩
  iNamed H
  icases ownLogGhost_term0 γ id (toPState s) kl $$ Hlg with %H
  ipureintro; exact H

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

/-- (2026-10-20, D22 S-c) A node with nothing committed is of a cluster with no bootstrap log
(`ownLogGhost_boot`), so not in the no-transfer mode (`RaftNames.reNoXfer_ok`): what
`RestartNode`'s fresh node is. -/
theorem ownRaftGhost_noXfer_of_commit (γ : RaftNames) (id : w64) (ps : PState) {md : Bool}
    (Hc : uint.Z ps.commit = 0) :
    ownRaftGhost (GF := GF) γ id ps md ⊢ ⌜γ.reNoXfer = false⌝ ∗ ownRaftGhost γ id ps md := by
  apply persistent_entails_right
  iintro H
  iunfold ownRaftGhost at H
  icases H with ⟨%γv, %voted, %kl, H⟩
  iNamed H
  icases ownLogGhost_boot γ id ps kl $$ Hlg with ⟨%Hx, -⟩
  ipureintro
  cases h : γ.reNoXfer
  · rfl
  · exfalso
    have Hne := RaftNames.noXfer_boot h
    have := List.length_pos_iff.mpr Hne
    have := Hx.1
    omega

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

/-- (2026-10-19, D21 M2r) Leader transfer turned on (`ownRaftPhysC_xf_off`) on the static-mode
physical state (2026-10-19, D22 S-a: in either no-snapshot mode). -/
theorem ownRaftPhys_xf_off (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhys (GF := GF) cfg r id s -∗
      ownRaftPhys cfg r id { s with gh := { s.gh with xf := false } } := by
  iintro H
  ihave H := ownRaftPhys_toC' $$ H
  ihave H := ownRaftPhysC_xf_off (c := CfgM.simple cfg (domSet s.progress \ cfg)) r id s $$ H
  iapply ownRaftPhysC_toS
  iexact H

/-- (2026-10-19, D21 M3) The no-snapshot mode set to `b` on the static-mode physical state of a
node out of the mode (`Bootstrap`'s, at the cluster's `RaftNames.reNoSnap`): into it, a
non-leader with no pending snapshot, its log's boundary at most `1` and something committed, over
a storage that never compacts past `1` (`NsCap`; `ownRaftPhysC_set_ns`). (2026-10-19, D21 M2r)
Leader transfer (`NGhost.xf`, off since `newRaft`) set to `bx` (2026-10-19, D22 S-a: the cluster's
`RaftNames.reNoXfer`, independent of `b`; until then `b` too): kept off, or turned on
(`ownRaftPhysC_xf_off`); (2026-10-20, D22 S-c) and the boot flag (`NGhost.bt`) to `bx` too, past
term `0` with nothing in the outbox (`ownRaftPhysC_set_bt`; until then the no-snapshot mode asked
these). -/
theorem ownRaftPhys_set_ns (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (b bx : Bool)
    (H0 : s.gh.ns = false) (H0x : s.gh.xf = true) (H0b : s.gh.bt = false)
    (Hb : b = true → s.role ≠ .leader ∧ s.logst.snap = none ∧ uint.Z s.logst.prev.index' ≤ 1 ∧
      1 ≤ uint.Z s.logst.committed ∧ ∀ m ∈ s.outbox, m.ty ≠ .snap)
    (Hbt : bx = true → s.term ≠ W64 0 ∧ s.outbox = []) :
    ⊢ NsCap (GF := GF) b s.logst.storage -∗ ownRaftPhys cfg r id s -∗
      ownRaftPhys cfg r id { s with gh := { s.gh with ns := b, xf := bx, bt := bx } } := by
  iintro #Hcap H
  -- the mode first (transfer still off), then transfer
  ihave H : ownRaftPhys cfg r id { s with gh := { s.gh with ns := b } } $$ [H]
  · cases b with
    | false =>
      have He : ({ s with gh := { s.gh with ns := false } } : NState) = s := by
        rw [← H0]
      rw [He]
      iexact H
    | true =>
      obtain ⟨Hr, Hsn, Hp, Hc, Ho⟩ := Hb rfl
      ihave H := ownRaftPhys_toC' $$ H
      iunfold NsCap at Hcap
      ihave #Hc1 := Hcap $$ %rfl
      ihave H := ownRaftPhysC_set_ns (c := CfgM.simple cfg (domSet s.progress \ cfg)) r id s Hr Hsn
        Hp Hc Ho $$ Hc1 H
      iapply ownRaftPhysC_toS
      iexact H
  cases bx with
  | true =>
    obtain ⟨Ht, Hob⟩ := Hbt rfl
    ihave H := ownRaftPhys_toC' $$ H
    ihave H := ownRaftPhysC_set_bt
      (c := CfgM.simple cfg (domSet ({ s with gh := { s.gh with ns := b } } : NState).progress \ cfg))
      r id { s with gh := { s.gh with ns := b } } Ht Hob $$ H
    ihave H := ownRaftPhysC_toS $$ H
    have He : ({ s with gh := { s.gh with ns := b, xf := true, bt := true } } : NState) =
        { ({ s with gh := { s.gh with ns := b } } : NState) with
          gh := { ({ s with gh := { s.gh with ns := b } } : NState).gh with bt := true } } := by
      rw [← H0x]
    rw [He]
    iexact H
  | false =>
    ihave H := ownRaftPhys_xf_off cfg r id { s with gh := { s.gh with ns := b } } $$ H
    have He : ({ s with gh := { s.gh with ns := b, xf := false, bt := false } } : NState) =
        { ({ s with gh := { s.gh with ns := b } } : NState) with
          gh := { ({ s with gh := { s.gh with ns := b } } : NState).gh with xf := false } } := by
      rw [← H0b]
    rw [He]
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
  obtain ⟨H1, -, H3, H4, H5⟩ := Hpvoff
  iapply ownRawNode_intro γ rn id { rs with tc := tc } { s with gh := { s.gh with tc := tc } } cf fp
    rnv sv hprev steps Hwf Hin Hasync Hdlen Hunp Hsnap
    (stepsOk_mono s _ _ rfl ⟨rfl, rfl⟩ (Int.le_refl _) rfl Hle' Hstok) Htrm Hstor
    ⟨H1, rfl, Int.le_trans H3 Hle', fun h => Int.le_trans (H4 h) Hle', H5⟩ Hrs_out Hrs_unst Hrs_clb Hrnfl
    ⟨Hloan.1, Hloan.2.1, Hloan.2.2⟩
    Hsdt $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstrecs Hloanc Hsloc

/-- (2026-10-17) The term is within the ceiling. -/
theorem ownRawNode_term_tc (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) :
    ⊢ ownRawNode (GF := GF) γ rn id rs -∗
      ⌜uint.Z rs.term ≤ uint.Z rs.tc⌝ ∗ ownRawNode γ rn id rs := by
  iintro H
  iNamed H
  isplitr
  · ipureintro; rw [Htrm, Hpvoff.2.1]; exact Hpvoff.2.2.1
  iapply ownRawNode_intro γ rn id rs s cf fp rnv sv hprev steps Hwf Hin Hasync Hdlen Hunp Hsnap
    Hstok Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb Hrnfl Hloan
    Hsdt $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstrecs Hloanc Hsloc

/-- The storage handshake, at the RawNode (2026-10-10; until then `ownRawNode_persist`,
which lent the client the storage itself): the receipt of the application's append of
the entries the last `Ready` handed out (`appendReceipt`, for the node's storage) is
absorbed into the log's storage (`ownRaftLog_absorb`); afterwards nothing is
unpersisted. The right to append came with the `Ready` (`appendRight`); in between the
node may be stepped, ticked, or asked to propose or campaign, while the application
appends on its own. -/
theorem ownRawNode_appended (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState)
    -- (D22 S-d3a) no snapshot lent: a lent storage comes back with `Advance` (`snapReceipt`)
    (Hsl : rs.slent = none) :
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
    { s with logst := { s.logst with unpersisted := [] } } cf fp rnv sv hprev steps Hwf Hin Hasync
    Hdlen rfl Hsnap
    (stepsOk_mono s _ rs.steps rfl ⟨rfl, rfl⟩ (Int.le_refl _) rfl (Int.le_refl _) Hstok)
    Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb Hrnfl
    ⟨Hloan.1, Hloan.2.1, (fun l (h : rs.slent = some l) => by rw [Hsl] at h; cases h)⟩
    Hsdt $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstrecs Hloanc Hsloc

/-- (2026-10-28, stage U4a) `delivered`'s terms after the log's boundary are the log's, up to
`applying` (`logTermsTo`): both are prefixes of the global committed log (`isCommitted_agree`), the
log's committed prefix after its full prefix of the boundary's length. -/
theorem ownStepGhost_dlv_terms (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) (s : NState)
    (D : List EntryM) (HD : (D.length : Int) = uint.Z s.logst.applying)
    (Hac : uint.Z s.logst.applying ≤ uint.Z s.logst.committed) :
    ⊢ isCommitted (GF := GF) γ D -∗ ownStepGhost γ md c id s -∗
      ⌜∀ k t, (logTermsTo s.logst)[k]? = some t →
        (D.map (·.Term'))[uint.nat s.logst.prev.index' + k]? = some t⌝ ∗
      ownStepGhost γ md c id s := by
  iintro #HD' H
  iunfold ownStepGhost at H
  icases H with ⟨Hg, Hr⟩
  icases ownRaftGhost_committed γ id (toPState s) $$ Hg with ⟨%fp, %Hf, #Hc⟩
  icases isCommitted_agree γ _ _ $$ HD' Hc with %Hag
  isplitr
  · ipureintro
    intro k t Ht
    have Hfl : (fp.length : Int) = uint.Z s.logst.prev.index' := Hf.1
    have HL : (toPState s).log = s.logst.sents ++ s.logst.uents := rfl
    have HC : (toPState s).commit = s.logst.committed := rfl
    rw [HL, HC] at Hag
    unfold logTermsTo at Ht
    rw [List.getElem?_map] at Ht
    obtain ⟨e, He, rfl⟩ := Option.map_eq_some_iff.1 Ht
    have hk := (List.getElem?_eq_some_iff.1 He).1
    rw [List.length_take] at hk
    rw [List.getElem?_take_of_lt (by omega)] at He
    have He2 : (fp ++ (s.logst.sents ++ s.logst.uents))[fp.length + k]? = some e := by
      rw [List.getElem?_append_right (by omega)]; simpa using He
    have Hn : uint.nat s.logst.prev.index' = fp.length := by
      have := uint_nat_eq s.logst.prev.index'; omega
    have hlt : fp.length + k < D.length := by
      have := uint_nat_eq s.logst.applying; have := uint_nat_eq s.logst.prev.index'; omega
    have HX : ((fp ++ (s.logst.sents ++ s.logst.uents)).take
        (uint.Z s.logst.committed).toNat)[fp.length + k]? = some e := by
      rw [List.getElem?_take_of_lt (by omega)]; exact He2
    have HDe : D[fp.length + k]? = some e := by
      rcases Hag with h | h
      · obtain ⟨u, hu⟩ := h
        rw [← hu, List.getElem?_append_left hlt] at HX; exact HX
      · obtain ⟨u, hu⟩ := h
        rw [← hu, List.getElem?_append_left (List.getElem?_eq_some_iff.1 HX).1]; exact HX
    rw [List.getElem?_map, Hn, HDe]; rfl
  iunfold ownStepGhost
  isplitl [Hg]
  · iexact Hg
  · iexact Hr

/-- (D19i part 1) **Raising the floor** to `applying` -- the committed log handed out,
`delivered` -- with nothing unpersisted: the client (`node.go`, when the application's `Advance`
is handed over) gets the storage's floor witness, the application's right to compact and snapshot
up to it, and the node is marked raised (`RNState.flw`) until `Advance` moves `applied` there.
(2026-10-28, stage U4a) And the storage's terms of a prefix `D` of `delivered` (`storTermsAt`):
with no snapshot pending the storage holds the log, whose terms after its boundary are
`delivered`'s (`ownStepGhost_dlv_terms`); with one restored since, the record of the storage's terms
(`StorTermsOk`) is of `delivered` (`SdtTie`). -/
theorem ownRawNode_raise_floor (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState)
    (Hunp0 : rs.unpersisted = [])
    -- (D22 S-d3a) no snapshot lent (the storage is the application's then); since D22 S-d4 item 3
    -- a snapshot restored since the last `Ready` may be pending (`StorExtOk`)
    (Hsl : rs.slent = none) (D : List EntryM) (HD : D <+: rs.delivered) :
    ⊢ ownRawNode (GF := GF) γ rn id rs ==∗
      ownRawNode γ rn id { rs with flw := true } ∗
      ∃ x : w64, ⌜uint.Z x = (rs.delivered.length : Int)⌝ ∗ storFloor rs.storage x ∗
        storTermsAt rs.storage (D.map (·.Term')) := by
  iintro H
  iNamed H
  icases ownRaftPhysC_log_at cf rnv.raft' id s $$ Hphys with ⟨Hlog, %Hgh0, Hlback⟩
  icases ownRaftLog_fl _ _ $$ Hlog with ⟨%Hflb, Hlog⟩
  have Hlnt : s.logst.lent = false := by rw [Hgh0.1.2.1, Hloan.1, Hsl]; rfl
  imod ownRaftLog_raise_floor s.log s.logst s.logst.applying ⟨Hflb.1, Int.le_refl _⟩
    (Hunp ▸ Hunp0) Hlnt $$ Hlog with ⟨Hlog, Hfw⟩
  have HDl : (rs.delivered.length : Int) = uint.Z s.logst.applying := by
    have := uint_Z_nonneg s.logst.applying; rw [Hdlen]; omega
  icases ownStepGhost_dlv_terms γ _ cf id s rs.delivered HDl Hflb.2.1 $$ Hdeliv Hghost
    with ⟨%Hag, Hghost⟩
  imod ownRaftLog_terms s.log { s.logst with fl := s.logst.applying } (D.map (·.Term'))
    (rs.delivered.map (·.Term')) (Hunp ▸ Hunp0) Hlnt
    (by simp only [List.length_map]; have := HD.length_le; omega)
    (List.IsPrefix.map _ HD) (by simp only [List.length_map]; exact HDl)
    (fun _ => Hag) (fun h => Hsdt h) $$ Hlog with ⟨Hlog, Ht⟩
  ihave Hphys := Hlback $$ %_ Hlog %(LogGhOk.of_fields Hgh0 rfl rfl rfl rfl rfl)
    %(fun _ => logLast_le_of_fields rfl rfl rfl)
  ihave Hghost := ownStepGhost_congr γ _ cf id (s := s)
    (s' := { s with logst := { s.logst with fl := s.logst.applying } }) rfl rfl rfl rfl $$ Hghost
  imodintro
  isplitr [Hfw Ht]
  · iapply ownRawNode_intro γ rn id { rs with flw := true }
      { s with logst := { s.logst with fl := s.logst.applying } } cf fp rnv sv hprev steps Hwf Hin
      Hasync Hdlen Hunp Hsnap
      (stepsOk_mono s _ rs.steps rfl ⟨rfl, rfl⟩ (Int.le_refl _) rfl (Int.le_refl _) Hstok)
      Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb
      ⟨fun h => by simp at h, Hrnfl.2⟩
      ⟨Hloan.1, Hloan.2.1, (fun l (h : rs.slent = some l) => by rw [Hsl] at h; cases h)⟩
      Hsdt $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstrecs Hloanc Hsloc
  iexists s.logst.applying
  isplitr
  · ipureintro; exact HDl.symm
  rw [Hstor]
  isplitl [Hfw]
  · iexact Hfw
  · iexact Ht

/-- (2026-10-26, D22 J2, R-loc) **A lent snapshot is local to the node**: after the `Ready` that
lent it (`psnap` cleared), the pending snapshot is the loan's (`LoanOk`), whose receiver-local fact
the node keeps (`Hsloc`). -/
theorem ownRawNode_loanLoc (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (l : SnapLoan)
    (Hl : rs.slent = some l) (Hp : rs.psnap = false) :
    ownRawNode (GF := GF) γ rn id rs ⊢ snapLocal γ id l.snap.Metadata'.Index' := by
  iintro H
  iNamed H
  rcases (Hloan.2.2 l Hl).2.1 with h | ⟨s2, -, -, h⟩
  · rw [show l.snap.Metadata'.Index' = (snapId l.snap).index' from rfl]
    iapply (snapLocOk_some γ id (snapId l.snap)).1
    rw [← h]; iexact Hsloc
  · rw [Hp] at h; cases h

end rawnode

end EtcdGrove
end Perennial

-- Projection lemmas, `@[simp, word_unfold]` (ProjSimps.lean). (2026-10-16, stage R5: the
-- hard and soft state records are `InvRaftPhys.lean`'s, their projection lemmas still here.)
proj_simps Perennial.EtcdGrove.hsAbs Perennial.EtcdGrove.nodeHardstate Perennial.EtcdGrove.nodeSoftstate
proj_simps Perennial.EtcdGrove.appendAckM Perennial.EtcdGrove.applyAckM
