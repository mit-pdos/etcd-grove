/-
Port of `election_proof/inv_rawnode.v` (at 857d09190).

**The `RawNode`, and what `Ready`/`Advance` need of the log (2026-10-05)**

`ownRawNode cfg rn id s rs` is the one predicate for a `RawNode` (`rawnode.go`): the
struct, the `raft` it points to at the physical state `s` (`ownRaftPhys`), and the
RawNode's own state `rs` (`RNState`) -- the previous `SoftState`/`HardState` it
compares against, and the local messages it will step on `Advance`. Records, not Goose
types, index it (notes/raft-replication-model.md, "Public representation predicates").

Scope: `asyncStorageWrites = false` (a conjunct, like `ownRaftPhys`'s
`checkQuorum = false`). With synchronous storage writes `Ready`'s `acceptReady` queues
the self-addressed responses of `msgsAfterAppend`, a `MsgStorageAppendResp` and a
`MsgStorageApplyResp` into `stepsOnAdvance`, and `Advance` steps them.

The log-side notions `Ready`/`Advance` are specified with -- the next unstable entries,
the committed entries to apply, `acceptUnstable`, `stableTo` -- are pure functions of
`LogState` in `InvReadylog.lean`.

Lean notes: the Rocq records `hardstate.t`, `softstate.t`, `rnstate.t` and the
inductive `pending.t` are `HardSt`, `SoftSt`, `RNState`, `Pending` (`HardSt`/`SoftSt`
after the Go fields `prevHardSt`/`prevSoftSt`: `SoftState` is the Goose type of
`go_etcd_io.raft.v3`, opened here); the constructors `pending.self`,
`pending.append_ack`, `pending.apply_ack` are `Pending.self`, `.appendAck`,
`.applyAck`. `hs_abs`, `hs_empty_abs`, `node_hardstate`, `node_softstate`,
`hardstate_val`, `softstate_val`, `append_ack_msg`, `apply_ack_msg`, `pending_rel`,
`pending_own`, `own_RawNode` are `hsAbs`, `hsEmptyAbs`, `nodeHardstate`,
`nodeSoftstate`, `hardstateVal`, `softstateVal`, `appendAckMsg`, `applyAckMsg`,
`pendingRel`, `pendingOwn`, `ownRawNode`; the `EqDecision` instances are `deriving
DecidableEq`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvReadylog

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

- `self a`: a self-addressed response from `msgsAfterAppend` (the candidate's own vote,
  the leader's own `MsgAppResp`), abstracted as `a`;
- `appendAck t last`: `MsgStorageAppendResp` at term `t` acknowledging the log up to
  `last` (queued when there were unstable entries);
- `applyAck ents`: `MsgStorageApplyResp` carrying the committed entries handed out for
  applying. -/
inductive Pending [FfiSyntax] where
  | self (a : Option Msg)
  | appendAck (term : w64) (last : entryID)
  | applyAck (ents : List raftpb.Entry)

structure RNState [FfiSyntax] where
  /-- `*rn.prevSoftSt` -/
  soft : SoftSt
  /-- `rn.prevHardSt` -/
  hard : HardSt
  /-- `rn.stepsOnAdvance` -/
  steps : List Pending

section defs
variable [FfiSyntax]

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

end defs

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The physical message queued for a pending step. -/
def pendingRel (id : w64) (m : raftpb.Message) (p : Pending) : IProp GF :=
  match p with
  | .self a => iprop(msgAbs m a ∗ ⌜m.To' = id⌝)
  | .appendAck t e => iprop(⌜m = appendAckMsg id t e⌝)
  | .applyAck ents => iprop(∃ sl, ⌜m = applyAckMsg id sl⌝ ∗ sl ↦*□ ents)

instance pendingRel_pers (id : w64) (m : raftpb.Message) (p : Pending) :
    Persistent (pendingRel (GF := GF) id m p) := by
  cases p <;> unfold pendingRel <;> infer_instance

/-- What a pending step owns: the capacity of a `MsgStorageApplyResp`'s `Entries` --
`Ready`'s `CommittedEntries` slice, which `Step`'s spec asks to own and which `Ready`
therefore keeps for the node rather than handing to the application. -/
def pendingOwn (m : raftpb.Message) (p : Pending) : IProp GF :=
  match p with
  | .applyAck _ => ownSliceCap raftpb.Entry m.Entries' (DFrac.own 1)
  | _ => iprop(True)

variable (cfg : GSet w64)

/-! ## The one predicate for a `RawNode` -/

def ownRawNode (rn : Loc) (id : w64) (s : NState) (rs : RNState) : IProp GF :=
  iprop(∃ (rnv : RawNode) (sv : SoftState) (steps : List raftpb.Message),
  "Hrn" ∷ rn ↦ rnv ∗
  "Hphys" ∷ ownRaftPhys cfg rnv.raft' id s ∗
  -- scope: synchronous storage writes (`Config.AsyncStorageWrites` unset); `NewRawNode`
  -- copies the `Config` field
  "%Hasync" ∷ ⌜rnv.asyncStorageWrites' = false⌝ ∗
  -- `prevSoftSt`: a pointer to a `SoftState` nobody writes (it is either `NewRawNode`'s
  -- or a `Ready.SoftState`), held read-only
  "#Hsoft" ∷ rnv.prevSoftSt' ↦□ sv ∗
  "%Hsoftv" ∷ ⌜sv = softstateVal rs.soft⌝ ∗
  "%Hhard" ∷ ⌜rnv.prevHardSt' = hardstateVal rs.hard⌝ ∗
  "Hsteps" ∷ rnv.stepsOnAdvance' ↦* steps ∗
  "Hsteps_cap" ∷ ownSliceCap raftpb.Message rnv.stepsOnAdvance' (DFrac.own 1) ∗
  "#Hpend" ∷ ([∗list] _k ↦ m;p ∈ steps;rs.steps, pendingRel id m p) ∗
  "Hpown" ∷ ([∗list] _k ↦ m;p ∈ steps;rs.steps, pendingOwn m p))

/-- The raft struct, for a `raft` method called on `rn.raft` -- in particular `Step`,
which is legal between `Ready` and `Advance`. -/
theorem ownRawNode_raft (rn : Loc) (id : w64) (s : NState) (rs : RNState) :
    ⊢ ownRawNode (GF := GF) cfg rn id s rs -∗
      ∃ r, ownRaftPhys cfg r id s ∗
           (∀ s', ownRaftPhys cfg r id s' -∗ ownRawNode cfg rn id s' rs) := by
  iintro H
  unfold ownRawNode
  icases H with ⟨%rnv, %sv, %steps, H⟩
  iNamed H
  iexists rnv.raft'
  iframe Hphys
  iintro %s' Hphys
  iexists rnv, sv, steps
  simp only [named]
  iframe Hrn Hphys Hsoft Hsteps Hsteps_cap Hpend Hpown
  ipureintro
  exact ⟨Hasync, Hsoftv, Hhard⟩

/-- The storage handshake, at the RawNode: the `Storage` the log owns, for the
application to append the entries the last `Ready` handed out (`ownRaftLog_persist`,
`InvRaftlog.lean`). -/
theorem ownRawNode_persist (rn : Loc) (id : w64) (s : NState) (rs : RNState) :
    ⊢ ownRawNode (GF := GF) cfg rn id s rs -∗
      ∃ (st : Storage) (sprev : entryID) (stored : List raftpb.Entry) (ss : entryID),
        isStorage st ∗ ownStorage st sprev stored ss ∗
        (ownStorage st sprev (storApp sprev stored s.logst.unpersisted) ss -∗
         ownRawNode cfg rn id
           { s with logst := { s.logst with unpersisted := [] } } rs) := by
  iintro H
  icases ownRawNode_raft cfg rn id s rs $$ H with ⟨%r, Hphys, Hback⟩
  icases ownRaftPhys_log_at cfg r id s $$ Hphys with ⟨Hlog, Hlback⟩
  icases ownRaftLog_persist s.log s.logst $$ Hlog with
    ⟨%st, %sprev, %stored, %ss, #Hst, HSt, Hclose⟩
  iexists st, sprev, stored, ss
  iframe Hst HSt
  iintro HSt
  iapply Hback
  iapply Hlback
  iapply Hclose $$ HSt

end proof

end EtcdGrove
end Perennial
