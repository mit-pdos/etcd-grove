/-
Port of `election_proof/inv_raft_phys.v` (at 857d09190): physical ownership of the raft
struct.

## Physical ownership of the raft struct

`ownRaftPhys cfg r id s` is full ownership of the `raft` struct at `r` and of
everything hanging off it, in a state described by the physical abstract state
`s : NState` (`Defs.lean`).

**This is the only ownership predicate for the raft struct, and every Go-level spec is
stated on it.** If a function cannot be specified this way, the fix is to make `NState`
more precise and this predicate with it -- not to add a variant. See `NState` for the
three variants this replaced on 2026-09-22 and notes/decisions.md, "Three layers", for
why.

There is no `γ`: this predicate says nothing about ghost state. The connection to the
protocol is `NStateRel` (`Defs.lean`), and `Step`'s spec is the only one that mentions
both.

Lean notes:
* Rocq's `Context (cfg : gset w64)` is an explicit section variable, so `ownRaftPhys`
  and every lemma about it take `cfg` as their first explicit argument (as in Rocq
  once the section is closed): `ownRaftPhys cfg r id s`. The reconfiguration section
  has no such variable and takes `cfg0 cfg` explicitly, as in Rocq.
* The seal (Rocq `seal`/`unseal`) is Perennial's Lean pattern
  (`Perennial/Golang/Defn/PostLang.lean`): `ownRaftPhysDef`, an `@[irreducible] def
  ownRaftPhys` equal to it, and an unseal lemma. The unseal lemma is `private`, as
  Rocq's is `Local`, and so is `ownRaftPhysDef` itself: an `@[irreducible]` def can
  still be `unfold`ed by its equation lemma, but outside this file what comes out is a
  private name that cannot be unfolded further. Rocq's `iNamed_phys` is a local macro
  (`ownRaftPhys_open`, `iunfold`, `icases`, `iNamed`).
* The Rocq `Local Ltac`s: `reseal` is a local macro that takes the target state
  explicitly (Rocq reads it off the goal) and closes the pure premises of
  `ownRaftPhys_intro` with `assumption`/`rfl`; `load_proof`/`store_proof` are written
  out in each proof (`wp_apply wp_load_access`/`wp_store_access`, the Rocq local
  lemmas, then `reseal`); `split_field_proof` is a local macro taking the `icases`
  pattern that names the field `Hx` and the remaining fields `Hrest`.
* Field-access lemmas are named `raft.wp_load_<field>` / `raft.wp_store_<field>` (Rocq
  `wp_raft_load_<field>` / `wp_raft_store_<field>`), and the accessors
  `ownRaftPhys_<x>` (Rocq `own_raft_phys_<x>`). They are stated at exactly the
  expressions `wp_auto` leaves in front of a raft field access in Perennial's Lean
  port: `App (Val (GoInstruction (GoLoad t))) (Val #(r.[raft, go!"f"]))` and
  `App (Val (GoInstruction (GoStore t))) (Val (PairV #(r.[raft, go!"f"]) #v))` (Rocq
  `![t] #(r.[raft.raft.t, "f"])` and `GoStore t (#(r.[raft.raft.t, "f"]), #v)%V`).
  Go types are the Lean descriptors: `raft.StateType` is `StateType.ty`,
  `go.PointerType raft.raftLog` is `go.GoType.PointerType raftLog.ty`, etc.
* `msg_abs`, `abs_list`, `outbox_rel`, `send_no_snap` are `msgAbs`, `absList`,
  `outboxRel`, `send_no_snap`; Rocq `omap (λ a, a) as_` is `as_.filterMap id`.
  `state_w64`, `send_msgs`, `own_tracker`, `own_raftLog`, `own_Progress`, `is_Logger`,
  `own_ReadOnly`, `own_raft_misc` are `stateW64`, `sendMsgs`, `ownTracker`,
  `ownRaftLog`, `ownProgress`, `isLogger`, `ownReadOnly`, `ownRaftMisc`; `trk.mk v p q`
  is `⟨v, p, q⟩ : Trk`.
* Rocq's local `wp_load_access`/`wp_store_access` are kept (private), stated as
  Hoare triples so that `wp_apply` uses them; the field `AccessStrict` instances are
  the generated ones. `split_field_proof` unseals only the struct points-to, with
  `typedPointsto_unseal_eq`.
* `ownRaftPhys_reconfig`'s and `ownRaftPhys_retrack`'s new states are written
  `{ s with progress := prs', prvals := pvs' }` etc., Rocq's chains of setters (the
  same value).
* The Rocq `wp_raft_log` tactic is the macro `wp_raft_log` at the end of this file
  (checked on a copy of `becomeCandidate`'s `Infof` call; not used anywhere yet).
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftlog
public import Proof.go_etcd_io.raft.v3.InvTracker
public import Proof.go_etcd_io.raft.v3.InvTrackerC
public import Proof.go_etcd_io.raft.v3.InvLogger
public import Proof.go_etcd_io.raft.v3.InvMisc

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-! ## The abstract outbox of the two queues

`msgAbs m a`: the queued physical message `m` contributes `a` to the abstract outbox --
`none` for a type the model does not describe (`mtypeOf = none`: `MsgHup`,
`MsgCheckQuorum`, ...), else `absMsg ty m ents` where `ents` is what `m.Entries` points
to, held read-only. The points-to is what makes the abstraction a function of the heap
rather than of `m` alone: `m.Entries` is a slice (notes/raft-replication-model.md,
"Abstract messages").

A `MsgSnap` is abstracted by `absSnap m sv voters` instead (since 2026-10-02), the
snapshot's metadata and voters -- **read through the heap** (since 2026-10-03), like
`App`'s entries: `sv` is what `m.Snapshot` points to and `voters` what `sv`'s
`ConfState.Voters` slice holds, both read-only. `send` takes these points-tos for a
`MsgSnap` (its `Hsnap`); `maybeSendSnapshot` persists the local `snapshot` variable
whose address it queues (nobody writes it again) and has the voters from
`raftLog.snapshot` (`isStorage`'s `HSnapshot`, or `ownSnap` for a pending snapshot).
The receiving side, `Step`'s `Hsnap`, holds the same points-tos.

`outboxRel o msgs msgsAA`: the abstract outbox `o` is, up to permutation, what the two
queues contribute. Persistent. -/
def msgAbs (m : raftpb.Message) (a : Option Msg) : IProp GF :=
  iprop(⌜mtypeOf m.Type' = none ∧ a = none⌝ ∨
    (∃ ty ents ctx, ⌜mtypeOf m.Type' = some ty ∧ ty ≠ .snap ∧ a = some (absMsg ty m ents ctx)⌝ ∗
                m.Entries' ↦*□ ents ∗ m.Context' ↦*□ ctx) ∨
    (∃ (sv : raftpb.Snapshot) (voters : List w64),
       ⌜mtypeOf m.Type' = some .snap ∧ a = some (absSnap m sv voters)⌝ ∗
       m.Snapshot' ↦□ sv ∗
       sv.Metadata'.ConfState'.Voters' ↦*□ voters))

/-- `send`'s `Hsnap` precondition for a message that is not a `MsgSnap`: vacuous. -/
theorem send_no_snap (m : raftpb.Message) (P : IProp GF) (Hne : m.Type' ≠ MsgSnap) :
    ⊢ □ (⌜m.Type' = MsgSnap⌝ -∗ P) := by
  imodintro
  iintro %H
  exact absurd H Hne

def absList (as_ : List (Option Msg)) : List Msg := as_.filterMap id

def outboxRel (o : List Msg) (msgs msgsAA : List raftpb.Message) : IProp GF :=
  iprop(∃ (as1 as2 : List (Option Msg)),
    ⌜o ≡ₚ absList as1 ++ absList as2⌝ ∗
    ([∗list] _k ↦ m;a ∈ msgs;as1, msgAbs m a) ∗
    ([∗list] _k ↦ m;a ∈ msgsAA;as2, msgAbs m a))

instance msgAbs_pers (m : raftpb.Message) (a : Option Msg) :
    Persistent (msgAbs (GF := GF) m a) := by
  unfold msgAbs; infer_instance

instance outboxRel_pers (o : List Msg) (msgs msgsAA : List raftpb.Message) :
    Persistent (outboxRel (GF := GF) o msgs msgsAA) := by
  unfold outboxRel; infer_instance

theorem outboxRel_nil : ⊢ outboxRel (GF := GF) [] [] [] := by
  unfold outboxRel
  iexists [], []
  isplitr
  · ipureintro; rfl
  isplitr
  · iapply (BigSepL2.bigSepL2_nil (Φ := fun _ m a => msgAbs (GF := GF) m a)).2; iempintro
  · iapply (BigSepL2.bigSepL2_nil (Φ := fun _ m a => msgAbs (GF := GF) m a)).2; iempintro

theorem outboxRel_perm (o o' : List Msg) (msgs msgsAA : List raftpb.Message) (Hp : o' ≡ₚ o) :
    ⊢ outboxRel (GF := GF) o msgs msgsAA -∗ outboxRel o' msgs msgsAA := by
  unfold outboxRel
  iintro ⟨%as1, %as2, %Ho, H1, H2⟩
  iexists as1, as2
  iframe H1 H2
  ipureintro; exact Hp.trans Ho

/-- A message of `r.msgsAfterAppend` at a node `id` of term `t` (2026-10-10). `send`
queues only responses there (`MsgAppResp`, `MsgVoteResp`, `MsgPreVoteResp`), and
stamps them `From: id`. A self-addressed one is what `acceptReady` queues for
`RawNode.Advance` to step, so it carries what `Step`'s spec asks of it: a nonzero
`Term`, no `Entries` and no `Context` (`nil`), a `MsgAppResp` that does not reject; and
a term no later than the node's -- one later for a `MsgPreVoteResp`, which a
pre-campaign sends at the next term -- which bounds how far stepping it can move the
node's term. The term bound holds at every later term too (`AAMsgOk.mono`): the node's
term never moves back (`raft.wp_store_Term`). -/
def AAMsgOk (id t : w64) (m : raftpb.Message) : Prop :=
  (m.Type' = MsgAppResp ∨ m.Type' = MsgVoteResp ∨ m.Type' = MsgPreVoteResp) ∧
  m.From' = id ∧
  (m.To' = id →
    m.Term' ≠ W64 0 ∧ m.Entries' = slice.nil ∧ m.Context' = slice.nil ∧
    (m.Type' = MsgAppResp → m.Reject' = false) ∧
    uint.Z m.Term' ≤ uint.Z t + (if m.Type' = MsgPreVoteResp then 1 else 0))

theorem AAMsgOk.mono {id t t' : w64} {m : raftpb.Message} (Ht : uint.Z t ≤ uint.Z t')
    (H : AAMsgOk id t m) : AAMsgOk id t' m := by
  obtain ⟨Hty, Hfr, Hself⟩ := H
  refine ⟨Hty, Hfr, fun Hto => ?_⟩
  obtain ⟨H1, H2, H3, H4, H5⟩ := Hself Hto
  exact ⟨H1, H2, H3, H4, by omega⟩

/-- A queued message's term (2026-10-10): with pre-vote off, at most the node's. `send`
stamps the node's term into every message but a forwarded proposal (`Term = 0`) and a
vote message, whose term the caller sets (`SendOk`): a vote request or response of the
node's term, or (with pre-vote on) a pre-vote at the next term or a pre-vote response
granting a candidate's. A receiver thus knows a message from the outbox is from a term
no later than its sender's (`RawNode.readyWithoutAccept`'s `Hmsgs_term`). The bound holds
at every later term too (`OutTermOk.mono`). And (2026-10-10) with pre-vote off no queued
message is a pre-vote response: `RawNode.Advance` then never steps one, so it keeps the
node's term (the budget `node.go`'s ticks spend). -/
def OutTermOk (pv : Bool) (t : w64) (m : raftpb.Message) : Prop :=
  pv = false → uint.Z m.Term' ≤ uint.Z t ∧ m.Type' ≠ MsgPreVoteResp

theorem OutTermOk.mono {pv : Bool} {t t' : w64} {m : raftpb.Message}
    (Ht : uint.Z t ≤ uint.Z t') (H : OutTermOk pv t m) : OutTermOk pv t' m :=
  fun Hpv => ⟨Int.le_trans (H Hpv).1 Ht, (H Hpv).2⟩

/-! ### The raft struct's points-to, with `id` and `logger` shared (2026-10-10)

`raftOwn l v` is the struct points-to `l ↦ v` with the two fields nobody writes after
`newRaft` -- `id` and `logger` -- persistent (`↦□`) and every other field owned. `node.go`'s
`Tick` reads `n.rn.raft.logger` and `n.rn.raft.id` (its warning when the tick channel is
full) concurrently with the `run` goroutine, which owns the raft struct; with the two fields
persistent, `ownRaftPhys` can hand out a copy (`ownRaftPhys_shared`). The `AccessStrict`
instances below let the field lemmas use `raftOwn` as they used `l ↦ v`; `raftOwn_of_pts`
makes it from the points-to `newRaft` allocates. -/
def raftOwn (l : Loc) (v : raft) : IProp GF :=
  iprop(
"#H_id" ∷ l.[raft, go!"id"] ↦□ v.id' ∗
    "H_Term" ∷ l.[raft, go!"Term"] ↦ v.Term' ∗
    "H_Vote" ∷ l.[raft, go!"Vote"] ↦ v.Vote' ∗
    "H_readStates" ∷ l.[raft, go!"readStates"] ↦ v.readStates' ∗
    "H_raftLog" ∷ l.[raft, go!"raftLog"] ↦ v.raftLog' ∗
    "H_maxMsgSize" ∷ l.[raft, go!"maxMsgSize"] ↦ v.maxMsgSize' ∗
    "H_maxUncommittedSize" ∷ l.[raft, go!"maxUncommittedSize"] ↦ v.maxUncommittedSize' ∗
    "H_trk" ∷ l.[raft, go!"trk"] ↦ v.trk' ∗
    "H_state" ∷ l.[raft, go!"state"] ↦ v.state' ∗
    "H_isLearner" ∷ l.[raft, go!"isLearner"] ↦ v.isLearner' ∗
    "H_msgs" ∷ l.[raft, go!"msgs"] ↦ v.msgs' ∗
    "H_msgsAfterAppend" ∷ l.[raft, go!"msgsAfterAppend"] ↦ v.msgsAfterAppend' ∗
    "H_lead" ∷ l.[raft, go!"lead"] ↦ v.lead' ∗
    "H_leadTransferee" ∷ l.[raft, go!"leadTransferee"] ↦ v.leadTransferee' ∗
    "H_pendingConfIndex" ∷ l.[raft, go!"pendingConfIndex"] ↦ v.pendingConfIndex' ∗
    "H_disableConfChangeValidation" ∷ l.[raft, go!"disableConfChangeValidation"] ↦ v.disableConfChangeValidation' ∗
    "H_uncommittedSize" ∷ l.[raft, go!"uncommittedSize"] ↦ v.uncommittedSize' ∗
    "H_readOnly" ∷ l.[raft, go!"readOnly"] ↦ v.readOnly' ∗
    "H_electionElapsed" ∷ l.[raft, go!"electionElapsed"] ↦ v.electionElapsed' ∗
    "H_heartbeatElapsed" ∷ l.[raft, go!"heartbeatElapsed"] ↦ v.heartbeatElapsed' ∗
    "H_checkQuorum" ∷ l.[raft, go!"checkQuorum"] ↦ v.checkQuorum' ∗
    "H_preVote" ∷ l.[raft, go!"preVote"] ↦ v.preVote' ∗
    "H_heartbeatTimeout" ∷ l.[raft, go!"heartbeatTimeout"] ↦ v.heartbeatTimeout' ∗
    "H_electionTimeout" ∷ l.[raft, go!"electionTimeout"] ↦ v.electionTimeout' ∗
    "H_randomizedElectionTimeout" ∷ l.[raft, go!"randomizedElectionTimeout"] ↦ v.randomizedElectionTimeout' ∗
    "H_disableProposalForwarding" ∷ l.[raft, go!"disableProposalForwarding"] ↦ v.disableProposalForwarding' ∗
    "H_stepDownOnRemoval" ∷ l.[raft, go!"stepDownOnRemoval"] ↦ v.stepDownOnRemoval' ∗
    "H_tick" ∷ l.[raft, go!"tick"] ↦ v.tick' ∗
    "H_step" ∷ l.[raft, go!"step"] ↦ v.step' ∗
    "#H_logger" ∷ l.[raft, go!"logger"] ↦□ v.logger' ∗
    "H_pendingReadIndexMessages" ∷ l.[raft, go!"pendingReadIndexMessages"] ↦ v.pendingReadIndexMessages' ∗
    "H_traceLogger" ∷ l.[raft, go!"traceLogger"] ↦ v.traceLogger')


theorem raftOwn_of_pts (l : Loc) (v : raft) :
    ⊢ (l ↦ v : IProp GF) ==∗ raftOwn l v := by
  iintro Hl
  rw [typedPointsto_unseal_eq l v]
  icases Hl with ⟨Hf, -⟩
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hf
  ipersist id
  ipersist logger
  imodintro
  unfold raftOwn
  simp only [named]
  iframe
  try iframe #

theorem raftOwn_id (l : Loc) (v : raft) :
    ⊢ raftOwn (GF := GF) l v -∗ l.[raft, go!"id"] ↦□ v.id' := by
  iintro H; unfold raftOwn; iNamed H; iexact H_id

theorem raftOwn_logger (l : Loc) (v : raft) :
    ⊢ raftOwn (GF := GF) l v -∗ l.[raft, go!"logger"] ↦□ v.logger' := by
  iintro H; unfold raftOwn; iNamed H; iexact H_logger

/-- Take field `f` out of `raftOwn` and put back any value: a load or a store. -/
local macro "raftOwn_access " f:ident : tactic =>
  `(tactic| (constructor
             unfold raftOwn
             iintro H
             iNamed H
             isplitl [$f:ident]
             · iexact $f:ident
             iintro $f:ident
             simp only [named]
             iframe
             try iframe #))

theorem raftOwn_access_load_Term (l : Loc) (v : raft) :
    AccessStrict (PROP := IProp GF) (l.[raft, go!"Term"] ↦ v.Term') (l.[raft, go!"Term"] ↦ v.Term')
      (raftOwn l v) (raftOwn l v) := by
  raftOwn_access H_Term

theorem raftOwn_access_store_Term (l : Loc) (v : raft) (x : w64) :
    AccessStrict (PROP := IProp GF) (l.[raft, go!"Term"] ↦ v.Term') (l.[raft, go!"Term"] ↦ x)
      (raftOwn l v) (raftOwn l { v with Term' := x }) := by
  raftOwn_access H_Term

theorem raftOwn_access_load_Vote (l : Loc) (v : raft) :
    AccessStrict (PROP := IProp GF) (l.[raft, go!"Vote"] ↦ v.Vote') (l.[raft, go!"Vote"] ↦ v.Vote')
      (raftOwn l v) (raftOwn l v) := by
  raftOwn_access H_Vote

theorem raftOwn_access_store_Vote (l : Loc) (v : raft) (x : w64) :
    AccessStrict (PROP := IProp GF) (l.[raft, go!"Vote"] ↦ v.Vote') (l.[raft, go!"Vote"] ↦ x)
      (raftOwn l v) (raftOwn l { v with Vote' := x }) := by
  raftOwn_access H_Vote

theorem raftOwn_access_load_readStates (l : Loc) (v : raft) :
    AccessStrict (PROP := IProp GF) (l.[raft, go!"readStates"] ↦ v.readStates') (l.[raft, go!"readStates"] ↦ v.readStates')
      (raftOwn l v) (raftOwn l v) := by
  raftOwn_access H_readStates

theorem raftOwn_access_store_readStates (l : Loc) (v : raft) (x : GoSlice) :
    AccessStrict (PROP := IProp GF) (l.[raft, go!"readStates"] ↦ v.readStates') (l.[raft, go!"readStates"] ↦ x)
      (raftOwn l v) (raftOwn l { v with readStates' := x }) := by
  raftOwn_access H_readStates

theorem raftOwn_access_load_raftLog (l : Loc) (v : raft) :
    AccessStrict (PROP := IProp GF) (l.[raft, go!"raftLog"] ↦ v.raftLog') (l.[raft, go!"raftLog"] ↦ v.raftLog')
      (raftOwn l v) (raftOwn l v) := by
  raftOwn_access H_raftLog

theorem raftOwn_access_store_raftLog (l : Loc) (v : raft) (x : Loc) :
    AccessStrict (PROP := IProp GF) (l.[raft, go!"raftLog"] ↦ v.raftLog') (l.[raft, go!"raftLog"] ↦ x)
      (raftOwn l v) (raftOwn l { v with raftLog' := x }) := by
  raftOwn_access H_raftLog

theorem raftOwn_access_load_maxMsgSize (l : Loc) (v : raft) :
    AccessStrict (PROP := IProp GF) (l.[raft, go!"maxMsgSize"] ↦ v.maxMsgSize') (l.[raft, go!"maxMsgSize"] ↦ v.maxMsgSize')
      (raftOwn l v) (raftOwn l v) := by
  raftOwn_access H_maxMsgSize

theorem raftOwn_access_store_maxMsgSize (l : Loc) (v : raft) (x : entryEncodingSize) :
    AccessStrict (PROP := IProp GF) (l.[raft, go!"maxMsgSize"] ↦ v.maxMsgSize') (l.[raft, go!"maxMsgSize"] ↦ x)
      (raftOwn l v) (raftOwn l { v with maxMsgSize' := x }) := by
  raftOwn_access H_maxMsgSize

theorem raftOwn_access_load_maxUncommittedSize (l : Loc) (v : raft) :
    AccessStrict (PROP := IProp GF) (l.[raft, go!"maxUncommittedSize"] ↦ v.maxUncommittedSize') (l.[raft, go!"maxUncommittedSize"] ↦ v.maxUncommittedSize')
      (raftOwn l v) (raftOwn l v) := by
  raftOwn_access H_maxUncommittedSize

theorem raftOwn_access_store_maxUncommittedSize (l : Loc) (v : raft) (x : entryPayloadSize) :
    AccessStrict (PROP := IProp GF) (l.[raft, go!"maxUncommittedSize"] ↦ v.maxUncommittedSize') (l.[raft, go!"maxUncommittedSize"] ↦ x)
      (raftOwn l v) (raftOwn l { v with maxUncommittedSize' := x }) := by
  raftOwn_access H_maxUncommittedSize

theorem raftOwn_access_load_trk (l : Loc) (v : raft) :
    AccessStrict (PROP := IProp GF) (l.[raft, go!"trk"] ↦ v.trk') (l.[raft, go!"trk"] ↦ v.trk')
      (raftOwn l v) (raftOwn l v) := by
  raftOwn_access H_trk

theorem raftOwn_access_store_trk (l : Loc) (v : raft) (x : _root_.Perennial.go_etcd_io.raft.v3.tracker.ProgressTracker) :
    AccessStrict (PROP := IProp GF) (l.[raft, go!"trk"] ↦ v.trk') (l.[raft, go!"trk"] ↦ x)
      (raftOwn l v) (raftOwn l { v with trk' := x }) := by
  raftOwn_access H_trk

theorem raftOwn_access_load_state (l : Loc) (v : raft) :
    AccessStrict (PROP := IProp GF) (l.[raft, go!"state"] ↦ v.state') (l.[raft, go!"state"] ↦ v.state')
      (raftOwn l v) (raftOwn l v) := by
  raftOwn_access H_state

theorem raftOwn_access_store_state (l : Loc) (v : raft) (x : StateType) :
    AccessStrict (PROP := IProp GF) (l.[raft, go!"state"] ↦ v.state') (l.[raft, go!"state"] ↦ x)
      (raftOwn l v) (raftOwn l { v with state' := x }) := by
  raftOwn_access H_state

theorem raftOwn_access_load_isLearner (l : Loc) (v : raft) :
    AccessStrict (PROP := IProp GF) (l.[raft, go!"isLearner"] ↦ v.isLearner') (l.[raft, go!"isLearner"] ↦ v.isLearner')
      (raftOwn l v) (raftOwn l v) := by
  raftOwn_access H_isLearner

theorem raftOwn_access_store_isLearner (l : Loc) (v : raft) (x : Bool) :
    AccessStrict (PROP := IProp GF) (l.[raft, go!"isLearner"] ↦ v.isLearner') (l.[raft, go!"isLearner"] ↦ x)
      (raftOwn l v) (raftOwn l { v with isLearner' := x }) := by
  raftOwn_access H_isLearner

theorem raftOwn_access_load_msgs (l : Loc) (v : raft) :
    AccessStrict (PROP := IProp GF) (l.[raft, go!"msgs"] ↦ v.msgs') (l.[raft, go!"msgs"] ↦ v.msgs')
      (raftOwn l v) (raftOwn l v) := by
  raftOwn_access H_msgs

theorem raftOwn_access_store_msgs (l : Loc) (v : raft) (x : GoSlice) :
    AccessStrict (PROP := IProp GF) (l.[raft, go!"msgs"] ↦ v.msgs') (l.[raft, go!"msgs"] ↦ x)
      (raftOwn l v) (raftOwn l { v with msgs' := x }) := by
  raftOwn_access H_msgs

theorem raftOwn_access_load_msgsAfterAppend (l : Loc) (v : raft) :
    AccessStrict (PROP := IProp GF) (l.[raft, go!"msgsAfterAppend"] ↦ v.msgsAfterAppend') (l.[raft, go!"msgsAfterAppend"] ↦ v.msgsAfterAppend')
      (raftOwn l v) (raftOwn l v) := by
  raftOwn_access H_msgsAfterAppend

theorem raftOwn_access_store_msgsAfterAppend (l : Loc) (v : raft) (x : GoSlice) :
    AccessStrict (PROP := IProp GF) (l.[raft, go!"msgsAfterAppend"] ↦ v.msgsAfterAppend') (l.[raft, go!"msgsAfterAppend"] ↦ x)
      (raftOwn l v) (raftOwn l { v with msgsAfterAppend' := x }) := by
  raftOwn_access H_msgsAfterAppend

theorem raftOwn_access_load_lead (l : Loc) (v : raft) :
    AccessStrict (PROP := IProp GF) (l.[raft, go!"lead"] ↦ v.lead') (l.[raft, go!"lead"] ↦ v.lead')
      (raftOwn l v) (raftOwn l v) := by
  raftOwn_access H_lead

theorem raftOwn_access_store_lead (l : Loc) (v : raft) (x : w64) :
    AccessStrict (PROP := IProp GF) (l.[raft, go!"lead"] ↦ v.lead') (l.[raft, go!"lead"] ↦ x)
      (raftOwn l v) (raftOwn l { v with lead' := x }) := by
  raftOwn_access H_lead

theorem raftOwn_access_load_leadTransferee (l : Loc) (v : raft) :
    AccessStrict (PROP := IProp GF) (l.[raft, go!"leadTransferee"] ↦ v.leadTransferee') (l.[raft, go!"leadTransferee"] ↦ v.leadTransferee')
      (raftOwn l v) (raftOwn l v) := by
  raftOwn_access H_leadTransferee

theorem raftOwn_access_store_leadTransferee (l : Loc) (v : raft) (x : w64) :
    AccessStrict (PROP := IProp GF) (l.[raft, go!"leadTransferee"] ↦ v.leadTransferee') (l.[raft, go!"leadTransferee"] ↦ x)
      (raftOwn l v) (raftOwn l { v with leadTransferee' := x }) := by
  raftOwn_access H_leadTransferee

theorem raftOwn_access_load_pendingConfIndex (l : Loc) (v : raft) :
    AccessStrict (PROP := IProp GF) (l.[raft, go!"pendingConfIndex"] ↦ v.pendingConfIndex') (l.[raft, go!"pendingConfIndex"] ↦ v.pendingConfIndex')
      (raftOwn l v) (raftOwn l v) := by
  raftOwn_access H_pendingConfIndex

theorem raftOwn_access_store_pendingConfIndex (l : Loc) (v : raft) (x : w64) :
    AccessStrict (PROP := IProp GF) (l.[raft, go!"pendingConfIndex"] ↦ v.pendingConfIndex') (l.[raft, go!"pendingConfIndex"] ↦ x)
      (raftOwn l v) (raftOwn l { v with pendingConfIndex' := x }) := by
  raftOwn_access H_pendingConfIndex

theorem raftOwn_access_load_disableConfChangeValidation (l : Loc) (v : raft) :
    AccessStrict (PROP := IProp GF) (l.[raft, go!"disableConfChangeValidation"] ↦ v.disableConfChangeValidation') (l.[raft, go!"disableConfChangeValidation"] ↦ v.disableConfChangeValidation')
      (raftOwn l v) (raftOwn l v) := by
  raftOwn_access H_disableConfChangeValidation

theorem raftOwn_access_store_disableConfChangeValidation (l : Loc) (v : raft) (x : Bool) :
    AccessStrict (PROP := IProp GF) (l.[raft, go!"disableConfChangeValidation"] ↦ v.disableConfChangeValidation') (l.[raft, go!"disableConfChangeValidation"] ↦ x)
      (raftOwn l v) (raftOwn l { v with disableConfChangeValidation' := x }) := by
  raftOwn_access H_disableConfChangeValidation

theorem raftOwn_access_load_uncommittedSize (l : Loc) (v : raft) :
    AccessStrict (PROP := IProp GF) (l.[raft, go!"uncommittedSize"] ↦ v.uncommittedSize') (l.[raft, go!"uncommittedSize"] ↦ v.uncommittedSize')
      (raftOwn l v) (raftOwn l v) := by
  raftOwn_access H_uncommittedSize

theorem raftOwn_access_store_uncommittedSize (l : Loc) (v : raft) (x : entryPayloadSize) :
    AccessStrict (PROP := IProp GF) (l.[raft, go!"uncommittedSize"] ↦ v.uncommittedSize') (l.[raft, go!"uncommittedSize"] ↦ x)
      (raftOwn l v) (raftOwn l { v with uncommittedSize' := x }) := by
  raftOwn_access H_uncommittedSize

theorem raftOwn_access_load_readOnly (l : Loc) (v : raft) :
    AccessStrict (PROP := IProp GF) (l.[raft, go!"readOnly"] ↦ v.readOnly') (l.[raft, go!"readOnly"] ↦ v.readOnly')
      (raftOwn l v) (raftOwn l v) := by
  raftOwn_access H_readOnly

theorem raftOwn_access_store_readOnly (l : Loc) (v : raft) (x : Loc) :
    AccessStrict (PROP := IProp GF) (l.[raft, go!"readOnly"] ↦ v.readOnly') (l.[raft, go!"readOnly"] ↦ x)
      (raftOwn l v) (raftOwn l { v with readOnly' := x }) := by
  raftOwn_access H_readOnly

theorem raftOwn_access_load_electionElapsed (l : Loc) (v : raft) :
    AccessStrict (PROP := IProp GF) (l.[raft, go!"electionElapsed"] ↦ v.electionElapsed') (l.[raft, go!"electionElapsed"] ↦ v.electionElapsed')
      (raftOwn l v) (raftOwn l v) := by
  raftOwn_access H_electionElapsed

theorem raftOwn_access_store_electionElapsed (l : Loc) (v : raft) (x : w64) :
    AccessStrict (PROP := IProp GF) (l.[raft, go!"electionElapsed"] ↦ v.electionElapsed') (l.[raft, go!"electionElapsed"] ↦ x)
      (raftOwn l v) (raftOwn l { v with electionElapsed' := x }) := by
  raftOwn_access H_electionElapsed

theorem raftOwn_access_load_heartbeatElapsed (l : Loc) (v : raft) :
    AccessStrict (PROP := IProp GF) (l.[raft, go!"heartbeatElapsed"] ↦ v.heartbeatElapsed') (l.[raft, go!"heartbeatElapsed"] ↦ v.heartbeatElapsed')
      (raftOwn l v) (raftOwn l v) := by
  raftOwn_access H_heartbeatElapsed

theorem raftOwn_access_store_heartbeatElapsed (l : Loc) (v : raft) (x : w64) :
    AccessStrict (PROP := IProp GF) (l.[raft, go!"heartbeatElapsed"] ↦ v.heartbeatElapsed') (l.[raft, go!"heartbeatElapsed"] ↦ x)
      (raftOwn l v) (raftOwn l { v with heartbeatElapsed' := x }) := by
  raftOwn_access H_heartbeatElapsed

theorem raftOwn_access_load_checkQuorum (l : Loc) (v : raft) :
    AccessStrict (PROP := IProp GF) (l.[raft, go!"checkQuorum"] ↦ v.checkQuorum') (l.[raft, go!"checkQuorum"] ↦ v.checkQuorum')
      (raftOwn l v) (raftOwn l v) := by
  raftOwn_access H_checkQuorum

theorem raftOwn_access_store_checkQuorum (l : Loc) (v : raft) (x : Bool) :
    AccessStrict (PROP := IProp GF) (l.[raft, go!"checkQuorum"] ↦ v.checkQuorum') (l.[raft, go!"checkQuorum"] ↦ x)
      (raftOwn l v) (raftOwn l { v with checkQuorum' := x }) := by
  raftOwn_access H_checkQuorum

theorem raftOwn_access_load_preVote (l : Loc) (v : raft) :
    AccessStrict (PROP := IProp GF) (l.[raft, go!"preVote"] ↦ v.preVote') (l.[raft, go!"preVote"] ↦ v.preVote')
      (raftOwn l v) (raftOwn l v) := by
  raftOwn_access H_preVote

theorem raftOwn_access_store_preVote (l : Loc) (v : raft) (x : Bool) :
    AccessStrict (PROP := IProp GF) (l.[raft, go!"preVote"] ↦ v.preVote') (l.[raft, go!"preVote"] ↦ x)
      (raftOwn l v) (raftOwn l { v with preVote' := x }) := by
  raftOwn_access H_preVote

theorem raftOwn_access_load_heartbeatTimeout (l : Loc) (v : raft) :
    AccessStrict (PROP := IProp GF) (l.[raft, go!"heartbeatTimeout"] ↦ v.heartbeatTimeout') (l.[raft, go!"heartbeatTimeout"] ↦ v.heartbeatTimeout')
      (raftOwn l v) (raftOwn l v) := by
  raftOwn_access H_heartbeatTimeout

theorem raftOwn_access_store_heartbeatTimeout (l : Loc) (v : raft) (x : w64) :
    AccessStrict (PROP := IProp GF) (l.[raft, go!"heartbeatTimeout"] ↦ v.heartbeatTimeout') (l.[raft, go!"heartbeatTimeout"] ↦ x)
      (raftOwn l v) (raftOwn l { v with heartbeatTimeout' := x }) := by
  raftOwn_access H_heartbeatTimeout

theorem raftOwn_access_load_electionTimeout (l : Loc) (v : raft) :
    AccessStrict (PROP := IProp GF) (l.[raft, go!"electionTimeout"] ↦ v.electionTimeout') (l.[raft, go!"electionTimeout"] ↦ v.electionTimeout')
      (raftOwn l v) (raftOwn l v) := by
  raftOwn_access H_electionTimeout

theorem raftOwn_access_store_electionTimeout (l : Loc) (v : raft) (x : w64) :
    AccessStrict (PROP := IProp GF) (l.[raft, go!"electionTimeout"] ↦ v.electionTimeout') (l.[raft, go!"electionTimeout"] ↦ x)
      (raftOwn l v) (raftOwn l { v with electionTimeout' := x }) := by
  raftOwn_access H_electionTimeout

theorem raftOwn_access_load_randomizedElectionTimeout (l : Loc) (v : raft) :
    AccessStrict (PROP := IProp GF) (l.[raft, go!"randomizedElectionTimeout"] ↦ v.randomizedElectionTimeout') (l.[raft, go!"randomizedElectionTimeout"] ↦ v.randomizedElectionTimeout')
      (raftOwn l v) (raftOwn l v) := by
  raftOwn_access H_randomizedElectionTimeout

theorem raftOwn_access_store_randomizedElectionTimeout (l : Loc) (v : raft) (x : w64) :
    AccessStrict (PROP := IProp GF) (l.[raft, go!"randomizedElectionTimeout"] ↦ v.randomizedElectionTimeout') (l.[raft, go!"randomizedElectionTimeout"] ↦ x)
      (raftOwn l v) (raftOwn l { v with randomizedElectionTimeout' := x }) := by
  raftOwn_access H_randomizedElectionTimeout

theorem raftOwn_access_load_disableProposalForwarding (l : Loc) (v : raft) :
    AccessStrict (PROP := IProp GF) (l.[raft, go!"disableProposalForwarding"] ↦ v.disableProposalForwarding') (l.[raft, go!"disableProposalForwarding"] ↦ v.disableProposalForwarding')
      (raftOwn l v) (raftOwn l v) := by
  raftOwn_access H_disableProposalForwarding

theorem raftOwn_access_store_disableProposalForwarding (l : Loc) (v : raft) (x : Bool) :
    AccessStrict (PROP := IProp GF) (l.[raft, go!"disableProposalForwarding"] ↦ v.disableProposalForwarding') (l.[raft, go!"disableProposalForwarding"] ↦ x)
      (raftOwn l v) (raftOwn l { v with disableProposalForwarding' := x }) := by
  raftOwn_access H_disableProposalForwarding

theorem raftOwn_access_load_stepDownOnRemoval (l : Loc) (v : raft) :
    AccessStrict (PROP := IProp GF) (l.[raft, go!"stepDownOnRemoval"] ↦ v.stepDownOnRemoval') (l.[raft, go!"stepDownOnRemoval"] ↦ v.stepDownOnRemoval')
      (raftOwn l v) (raftOwn l v) := by
  raftOwn_access H_stepDownOnRemoval

theorem raftOwn_access_store_stepDownOnRemoval (l : Loc) (v : raft) (x : Bool) :
    AccessStrict (PROP := IProp GF) (l.[raft, go!"stepDownOnRemoval"] ↦ v.stepDownOnRemoval') (l.[raft, go!"stepDownOnRemoval"] ↦ x)
      (raftOwn l v) (raftOwn l { v with stepDownOnRemoval' := x }) := by
  raftOwn_access H_stepDownOnRemoval

theorem raftOwn_access_load_tick (l : Loc) (v : raft) :
    AccessStrict (PROP := IProp GF) (l.[raft, go!"tick"] ↦ v.tick') (l.[raft, go!"tick"] ↦ v.tick')
      (raftOwn l v) (raftOwn l v) := by
  raftOwn_access H_tick

theorem raftOwn_access_store_tick (l : Loc) (v : raft) (x : GoFunc) :
    AccessStrict (PROP := IProp GF) (l.[raft, go!"tick"] ↦ v.tick') (l.[raft, go!"tick"] ↦ x)
      (raftOwn l v) (raftOwn l { v with tick' := x }) := by
  raftOwn_access H_tick

theorem raftOwn_access_load_step (l : Loc) (v : raft) :
    AccessStrict (PROP := IProp GF) (l.[raft, go!"step"] ↦ v.step') (l.[raft, go!"step"] ↦ v.step')
      (raftOwn l v) (raftOwn l v) := by
  raftOwn_access H_step

theorem raftOwn_access_store_step (l : Loc) (v : raft) (x : stepFunc) :
    AccessStrict (PROP := IProp GF) (l.[raft, go!"step"] ↦ v.step') (l.[raft, go!"step"] ↦ x)
      (raftOwn l v) (raftOwn l { v with step' := x }) := by
  raftOwn_access H_step

theorem raftOwn_access_load_pendingReadIndexMessages (l : Loc) (v : raft) :
    AccessStrict (PROP := IProp GF) (l.[raft, go!"pendingReadIndexMessages"] ↦ v.pendingReadIndexMessages') (l.[raft, go!"pendingReadIndexMessages"] ↦ v.pendingReadIndexMessages')
      (raftOwn l v) (raftOwn l v) := by
  raftOwn_access H_pendingReadIndexMessages

theorem raftOwn_access_store_pendingReadIndexMessages (l : Loc) (v : raft) (x : GoSlice) :
    AccessStrict (PROP := IProp GF) (l.[raft, go!"pendingReadIndexMessages"] ↦ v.pendingReadIndexMessages') (l.[raft, go!"pendingReadIndexMessages"] ↦ x)
      (raftOwn l v) (raftOwn l { v with pendingReadIndexMessages' := x }) := by
  raftOwn_access H_pendingReadIndexMessages

theorem raftOwn_access_load_traceLogger (l : Loc) (v : raft) :
    AccessStrict (PROP := IProp GF) (l.[raft, go!"traceLogger"] ↦ v.traceLogger') (l.[raft, go!"traceLogger"] ↦ v.traceLogger')
      (raftOwn l v) (raftOwn l v) := by
  raftOwn_access H_traceLogger

theorem raftOwn_access_store_traceLogger (l : Loc) (v : raft) (x : TraceLogger) :
    AccessStrict (PROP := IProp GF) (l.[raft, go!"traceLogger"] ↦ v.traceLogger') (l.[raft, go!"traceLogger"] ↦ x)
      (raftOwn l v) (raftOwn l { v with traceLogger' := x }) := by
  raftOwn_access H_traceLogger

/-- What a new log state `ls'` must keep of `NGhost.unst` (2026-10-10): if some unstable
entry had not been handed out, some still has not (or a snapshot is pending). Every
change of the log but `acceptReady`'s (and `stableTo`'s, which `Step` takes only with
`unst` off) keeps it. -/
def LogGhOk (s : NState) (ls' : LogState) : Prop :=
  s.gh.unst = true → nextUnstable ls' ≠ [] ∨ ls'.snap ≠ none

theorem LogGhOk.of_fields {s : NState} {ls' : LogState} (H : LogGhOk s s.logst)
    (hu : ls'.uents = s.logst.uents) (hi : ls'.inprogress = s.logst.inprogress)
    (hp : ls'.prev.index' = s.logst.prev.index') (hs : ls'.sents.length = s.logst.sents.length)
    (hsn : ls'.snap = s.logst.snap) : LogGhOk s ls' := by
  unfold LogGhOk nextUnstable logOffset at *
  rw [hu, hi, hp, hs, hsn]; exact H

theorem LogGhOk.append {s : NState} (ents : List raftpb.Entry) (H : LogGhOk s s.logst) :
    LogGhOk s (logAppend s.logst ents) := by
  intro h
  rcases H h with H | H
  · left
    unfold nextUnstable logOffset logAppend at *
    simp only at *
    intro Hn
    apply H
    have Hk : (uint.Z s.logst.inprogress - (uint.Z s.logst.prev.index' +
        (s.logst.sents.length : Int) + 1)).toNat ≤ s.logst.uents.length := by
      rcases Nat.lt_or_ge s.logst.uents.length (uint.Z s.logst.inprogress -
          (uint.Z s.logst.prev.index' + (s.logst.sents.length : Int) + 1)).toNat with Hc | Hc
      · exact absurd (List.drop_eq_nil_of_le (Nat.le_of_lt Hc)) H
      · exact Hc
    rw [List.drop_append_of_le_length Hk] at Hn
    exact (List.append_eq_nil_iff.mp Hn).1
  · right; exact H

/-- `truncateAndAppend` of a non-empty batch at or below the end of the log leaves the
batch's entries still to be handed out (`offsetInProgress` goes back to the batch's
start at most). -/
theorem nextUnstable_truncateAppend_ne (ls : LogState) (ents : List raftpb.Entry)
    (e0 : raftpb.Entry) (He0 : ents[0]? = some e0)
    (Hlo : uint.Z ls.prev.index' + (ls.sents.length : Int) + 1 ≤ uint.Z ls.inprogress)
    (Hhi : uint.Z ls.inprogress ≤ uint.Z ls.prev.index' + (ls.sents.length : Int)
      + (ls.uents.length : Int) + 1)
    (Hf : uint.Z ls.prev.index' < uint.Z e0.Index')
    (Hfle : uint.Z e0.Index' ≤ uint.Z ls.prev.index' + (ls.sents.length : Int)
      + (ls.uents.length : Int) + 1) :
    nextUnstable (logTruncateAppend ls ents) ≠ [] := by
  obtain ⟨e0', rest, rfl⟩ : ∃ e r, ents = e :: r := by
    cases ents with
    | nil => simp at He0
    | cons e r => exact ⟨e, r, rfl⟩
  simp only [List.getElem?_cons_zero, Option.some.injEq] at He0
  subst He0
  unfold nextUnstable logOffset logTruncateAppend logTruncInprogress
  simp only [List.length_take]
  intro Hn
  have Hd : ∀ (A : List raftpb.Entry) (d : Nat), d ≤ A.length →
      (A ++ e0' :: rest).drop d ≠ [] := by
    intro A d hd h
    rw [List.drop_append_of_le_length hd] at h
    simp at h
  revert Hn
  apply Hd
  simp only [List.length_take]
  split <;> (try split) <;> omega

theorem LogGhOk.of_snap {s : NState} {ls' : LogState} (h : ls'.snap ≠ none) :
    LogGhOk s ls' := fun _ => .inr h

theorem LogGhOk.of_off {s : NState} {ls' : LogState} (h : s.gh.unst = false) :
    LogGhOk s ls' := fun h' => absurd (h.symm.trans h') (by decide)

-- The (fixed) set of voters. `ownRaftPhys` mentions it because `ownTracker` does: now
-- that the tracker is a real definition rather than an opaque axiom, it pins the
-- progress map's domain and the configuration's voter set to `cfg`.
variable (cfg : GSet w64)

/-- Rocq `own_raft_phys_def`: the body of `ownRaftPhys` (see the file header), over any
tracker predicate `T` and voter set `V` (2026-10-13, reconfiguration stage A1): `ownRaftPhys
cfg` is it at `ownTracker cfg` and `cfg` (`ownRaftPhysDef`), `ownRaftPhysC c` at
`ownTrackerC c` and `c.voters`. -/
private def ownRaftPhysG (T : tracker.ProgressTracker → Trk → IProp GF) (V : GSet w64)
    (r : Loc) (id : w64) (s : NState) : IProp GF :=
  iprop(∃ (rv : raft) (msgs msgsAA : List raftpb.Message) (lok : GoInterfaceOk),
  -- the struct, `id` and `logger` shared (2026-10-10, `raftOwn`)
  "Hr" ∷ raftOwn r rv ∗

  -- the abstraction relation
  "%Hid" ∷ ⌜rv.id' = id⌝ ∗
  "%Hterm" ∷ ⌜rv.Term' = s.term⌝ ∗
  "%Hvote" ∷ ⌜rv.Vote' = s.vote⌝ ∗
  "%Hlead" ∷ ⌜rv.lead' = s.lead⌝ ∗
  "%Hstate" ∷ ⌜rv.state' = stateW64 s.role⌝ ∗
  -- `r.step`. Not a function of the role: `becomeFollower` assigns it before `reset`
  -- runs, and `newRaft` starts with it nil. That the two agree is `NStateWf`, which
  -- `Step` carries.
  "%Hstepfn" ∷ ⌜rv.step' = s.stepfn⌝ ∗
  -- `r.tick`, once a `becomeX` set it (2026-10-09): one of the two tick functions
  -- (`TickFnOk`), not tied to the role (`becomeFollower` assigns it after `reset`)
  "%Htick" ∷ ⌜s.ticking = true → TickFnOk r rv.tick'⌝ ∗

  -- the vote tally, the progress map and the rest of the heap the tracker points at.
  -- The tracker's own bytes are covered by `Hr` above, since `trk` is embedded by
  -- value; this is only what hangs off it. Indexed by `s.progress` and `s.prvals`:
  -- that is what lets a proof know *which* `Progress` a peer has, and what it holds,
  -- after a call it made with the struct sealed. (Until 2026-09-29 the values were
  -- existential, and a proof that needed one across a call took the tracker out of
  -- the predicate on loan, `nstate.lent`.) (From 2026-09-22 to 2026-09-23 a second,
  -- persistent copy of the progress map's points-to sat here, beside the one inside
  -- `ownTracker`; indexing `ownTracker` by the map made it redundant.)
  "Htrk" ∷ T rv.trk' ⟨s.votes, s.progress, s.prvals⟩ ∗

  -- the log, at the state `s` records (`NState.logst`). Never on loan: what
  -- `raftLog.slice` returns is read-only and the caller's for good. (Until 2026-09-28
  -- the log's state was quantified here, and the log went on loan with the tracker;
  -- until 2026-09-29 a slice `raftLog.slice` lent out was recorded in `logst.page`.)
  "%Hlogp" ∷ ⌜rv.raftLog' = s.log⌝ ∗
  "Hlog" ∷ ownRaftLog rv.raftLog' s.logst ∗

  -- outgoing messages. `send` routes vote/append *responses* to `msgsAfterAppend`
  -- and everything else to `msgs`; the model has a single outbox, so the
  -- abstraction is of the two together.
  --
  -- Two deliberate choices here. `filterMap` (Rocq `omap`): a message type the model
  -- does not describe (notably the `MsgAppResp` that `appendEntry` queues) simply
  -- drops out, rather than making the abstract outbox undefined. `≡ₚ`: appending to
  -- `msgs` does not append to the concatenation when `msgsAA` is non-empty, so
  -- equality would not survive a `send`; permutation is also all the model needs,
  -- since it cares which messages are out and not in what order.
  "Hmsgs" ∷ rv.msgs' ↦* msgs ∗
  "Hmsgs_cap" ∷ ownSliceCap raftpb.Message rv.msgs' (DFrac.own 1) ∗
  "HmsgsAA" ∷ rv.msgsAfterAppend' ↦* msgsAA ∗
  "HmsgsAA_cap" ∷ ownSliceCap raftpb.Message rv.msgsAfterAppend' (DFrac.own 1) ∗
  "#Houtbox" ∷ outboxRel s.outbox msgs msgsAA ∗
  -- what `send` puts in `msgsAfterAppend` (2026-10-10): responses from the node, the
  -- self-addressed ones steppable by `RawNode.Advance` (`AAMsgOk`)
  "%HmsgsAA_ok" ∷ ⌜∀ m ∈ msgsAA, AAMsgOk id s.term m⌝ ∗
  -- the queued messages' terms (2026-10-10): with pre-vote off, at most the node's
  "%Hout_term" ∷ ⌜∀ m ∈ msgs ++ msgsAA, OutTermOk s.prevote s.term m⌝ ∗
  -- the ghost lower bounds for `node.go` (2026-10-10, `NGhost`)
  "%Hgh_out" ∷ ⌜s.gh.outlb ≤ msgs.length + msgsAA.length⌝ ∗
  "%Hgh_unst" ∷ ⌜s.gh.unst = true → nextUnstable s.logst ≠ [] ∨ s.logst.snap ≠ none⌝ ∗
  -- only a voter leaves the follower role (2026-10-13, reconfiguration stage L): a learner
  -- never campaigns (`promotable`), so the role stores of `becomeCandidate`,
  -- `becomePreCandidate` and `becomeLeader` (`raft.wp_store_state`) are at a voter
  "%Hvoter" ∷ ⌜s.role ≠ .follower → id ∈ V⌝ ∗

  -- `r.preVote`, recorded (since 2026-10-04; until then a scope conjunct pinned it to
  -- `false`). Never written after `newRaft`.
  "%Hprevote" ∷ ⌜rv.preVote' = s.prevote⌝ ∗

  -- scope assumptions
  -- `Config.DisableProposalForwarding` is `false` (`newRaft`'s premise): a follower
  -- forwards a proposal to the leader it knows. Never written after `newRaft`. Added
  -- 2026-10-02.
  "%HpropForward" ∷ ⌜rv.disableProposalForwarding' = false⌝ ∗
  -- `Config.DisableConfChangeValidation` is `false` (`newRaft`'s premise, 2026-10-13):
  -- `stepLeader` refuses a conf change while one is pending or the configuration is not
  -- as the change expects. Never written after `newRaft`.
  "%HnoCCV" ∷ ⌜rv.disableConfChangeValidation' = false⌝ ∗
  "%HnoCheckQuorum" ∷ ⌜rv.checkQuorum' = false⌝ ∗
  -- `r.isLearner` (2026-10-13; until then a scope conjunct pinned it to `false`), recorded
  "%HnoLearner" ∷ ⌜rv.isLearner' = s.isLearner⌝ ∗
  -- `r.leadTransferee` (2026-10-13; until then a scope conjunct pinned it to `0`): never
  -- the node itself (`MsgTransferLeader` to self is ignored), so a `MsgTimeoutNow` to it
  -- is never self-addressed
  "%HnoTransfer" ∷ ⌜rv.leadTransferee' = s.lt ∧ s.lt ≠ id⌝ ∗
  -- `r.pendingConfIndex` (2026-10-13, reconfiguration stage D), recorded
  "%Hpci" ∷ ⌜rv.pendingConfIndex' = s.pci⌝ ∗
  "%Hid_nz" ∷ ⌜id ≠ W64 0⌝ ∗
  -- `Config.validate` requires `ElectionTick > HeartbeatTick > 0` and `newRaft`
  -- copies it, so this is an invariant of every struct raft builds. It is needed
  -- because `resetRandomizedElectionTimeout` passes the field to `crypto/rand.Int`,
  -- which panics on a non-positive bound -- see
  -- `spec_raft__resetRandomizedElectionTimeout.v`. Never written on the election path.
  -- Added 2026-09-20.
  "%HelectionTimeout" ∷ ⌜0 < sint.Z rv.electionTimeout'⌝ ∗

  -- logging, tracing, and everything else
  "%Hlok" ∷ ⌜rv.logger' = interface.ok lok⌝ ∗
  "#Hlogger" ∷ isLogger lok ∗
  "Hmisc" ∷ ownRaftMisc rv.readStates' rv.readOnly' rv.pendingReadIndexMessages' s.rd)

/-- The body of `ownRaftPhys`: `ownRaftPhysG` at the simple configuration's tracker. -/
private def ownRaftPhysDef (r : Loc) (id : w64) (s : NState) : IProp GF :=
  ownRaftPhysG (ownTracker cfg) cfg r id s

/-- Physical ownership of the raft struct (see the file header).

Sealed: outside this file `ownRaftPhys` cannot be unfolded, so a program proof that
reaches into the representation does not compile. Every access goes through the
interface below. -/
@[irreducible, no_expose] def ownRaftPhys (r : Loc) (id : w64) (s : NState) : IProp GF :=
  ownRaftPhysDef cfg r id s

private theorem ownRaftPhys_unseal (r : Loc) (id : w64) (s : NState) :
    ownRaftPhys (GF := GF) cfg r id s = ownRaftPhysDef cfg r id s := by
  with_unfolding_all rfl

/-- Open the predicate, in this file only. -/
private theorem ownRaftPhys_open (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhys (GF := GF) cfg r id s -∗ ownRaftPhysDef cfg r id s := by
  rw [ownRaftPhys_unseal]; iintro H; iexact H

/-- Re-sealing `ownRaftPhys` after a proof has taken it apart.

In Rocq, `iFrame "∗#%"` against the unfolded predicate costs ~17s per use (2026-09-17
measurement): `iFrame "%"` alone tries every pure fact in the Coq context against
every one of the conjuncts. This lemma makes a re-seal a single `iapply` with named
hypotheses and pure side goals:

    iapply ownRaftPhys_intro … $$ Hr Hlogger Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc Houtbox

The pure premises are in the order the conjuncts appear in the predicate. `r ↦ rv` is
the first spatial argument **on purpose**: it is what fixes `rv`, at the struct value
the heap holds *now*. If another argument came first, `rv` would be fixed from it --
at whatever struct value that hypothesis was stated -- and after any field write the
heap's `r ↦ { rv with … }` would then fail to match. -/
theorem ownRaftPhys_intro (r : Loc) (id : w64) (s : NState) (rv : raft)
    (msgs msgsAA : List raftpb.Message) (lok : GoInterfaceOk) :
    rv.id' = id →
    rv.Term' = s.term →
    rv.Vote' = s.vote →
    rv.lead' = s.lead →
    rv.state' = stateW64 s.role →
    rv.step' = s.stepfn →
    rv.preVote' = s.prevote →
    rv.disableProposalForwarding' = false →
    rv.disableConfChangeValidation' = false →
    rv.checkQuorum' = false →
    rv.isLearner' = s.isLearner →
    rv.leadTransferee' = s.lt ∧ s.lt ≠ id →
    rv.pendingConfIndex' = s.pci →
    id ≠ W64 0 →
    0 < sint.Z rv.electionTimeout' →
    rv.logger' = interface.ok lok →
    rv.raftLog' = s.log →
    (s.ticking = true → TickFnOk r rv.tick') →
    (∀ m ∈ msgsAA, AAMsgOk id s.term m) →
    (∀ m ∈ msgs ++ msgsAA, OutTermOk s.prevote s.term m) →
    s.gh.outlb ≤ msgs.length + msgsAA.length →
    (s.gh.unst = true → nextUnstable s.logst ≠ [] ∨ s.logst.snap ≠ none) →
    (s.role ≠ .follower → id ∈ cfg) →
    ⊢ raftOwn (GF := GF) r rv -∗
      isLogger lok -∗
      ownTracker cfg rv.trk' ⟨s.votes, s.progress, s.prvals⟩ -∗
      ownRaftLog rv.raftLog' s.logst -∗
      rv.msgs' ↦* msgs -∗
      ownSliceCap raftpb.Message rv.msgs' (DFrac.own 1) -∗
      rv.msgsAfterAppend' ↦* msgsAA -∗
      ownSliceCap raftpb.Message rv.msgsAfterAppend' (DFrac.own 1) -∗
      ownRaftMisc rv.readStates' rv.readOnly' rv.pendingReadIndexMessages' s.rd -∗
      outboxRel s.outbox msgs msgsAA -∗
      ownRaftPhys cfg r id s := by
  intro Hid Hterm Hvote Hlead Hstate Hstepfn Hprevote HpropForward HnoCCV HnoCheckQuorum
    HnoLearner HnoTransfer Hpci Hid_nz HelectionTimeout Hlok Hlogp Htick HmsgsAA_ok Hout_term
    Hgh_out Hgh_unst Hvoter
  iintro Hr #Hlogger Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc #Houtbox
  rw [ownRaftPhys_unseal]; unfold ownRaftPhysDef ownRaftPhysG
  iexists rv, msgs, msgsAA, lok
  simp only [named]
  iframe Hr Hlogger Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc Houtbox
  ipureintro
  exact ⟨Hid, Hterm, Hvote, Hlead, Hstate, Hstepfn, Htick, Hlogp, HmsgsAA_ok, Hout_term,
    Hgh_out, Hgh_unst, Hvoter, Hprevote,
    HpropForward, HnoCCV, HnoCheckQuorum, HnoLearner, HnoTransfer, Hpci, Hid_nz, HelectionTimeout, Hlok⟩

/-! ### At any configuration (2026-10-13, reconfiguration stage A1)

`ownRaftPhysC c r id s` is `ownRaftPhys` with the tracker at the configuration `c : CfgM`
(`ownTrackerC c`, `InvTrackerC.lean`: joint, with learners and staged learners, `AutoLeave`)
and the voter set of `Hvoter` the voters of both halves (`c.voters`). Sealed the same way.
`ownRaftPhys cfg` is the special case at `CfgM.simple cfg (domSet s.progress \ cfg)`
(`ownRaftPhys_toC`, `ownRaftPhysC_toPhys`, below the accessors), so every spec stated on
`ownRaftPhys` keeps its statement; a function whose behaviour depends on the configuration
gets a spec on `ownRaftPhysC` (stage A2). Accessors so far: `ownRaftPhysC_tracker`,
`ownRaftPhysC_reconfig`, `ownRaftPhysC_voter`, `ownRaftPhysC_progress_dom`; the field
lemmas are `ownRaftPhys`'s (through the equivalence when the configuration is simple; at a
joint one they are to be restated, A2). -/

/-- Physical ownership of the raft struct at the configuration `c`. -/
@[irreducible, no_expose] def ownRaftPhysC (c : CfgM) (r : Loc) (id : w64) (s : NState) :
    IProp GF :=
  ownRaftPhysG (ownTrackerC c) c.voters r id s

private theorem ownRaftPhysC_unseal (c : CfgM) (r : Loc) (id : w64) (s : NState) :
    ownRaftPhysC (GF := GF) c r id s = ownRaftPhysG (ownTrackerC c) c.voters r id s := by
  with_unfolding_all rfl

private theorem ownRaftPhysC_open (c : CfgM) (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhysC (GF := GF) c r id s -∗ ownRaftPhysG (ownTrackerC c) c.voters r id s := by
  rw [ownRaftPhysC_unseal]; iintro H; iexact H

/-- Sealing `ownRaftPhysC`, as `ownRaftPhys_intro` (the same premises, the voter premise at
`c.voters`, the tracker as `ownTrackerC c`). -/
theorem ownRaftPhysC_intro (c : CfgM) (r : Loc) (id : w64) (s : NState) (rv : raft)
    (msgs msgsAA : List raftpb.Message) (lok : GoInterfaceOk) :
    rv.id' = id →
    rv.Term' = s.term →
    rv.Vote' = s.vote →
    rv.lead' = s.lead →
    rv.state' = stateW64 s.role →
    rv.step' = s.stepfn →
    rv.preVote' = s.prevote →
    rv.disableProposalForwarding' = false →
    rv.disableConfChangeValidation' = false →
    rv.checkQuorum' = false →
    rv.isLearner' = s.isLearner →
    rv.leadTransferee' = s.lt ∧ s.lt ≠ id →
    rv.pendingConfIndex' = s.pci →
    id ≠ W64 0 →
    0 < sint.Z rv.electionTimeout' →
    rv.logger' = interface.ok lok →
    rv.raftLog' = s.log →
    (s.ticking = true → TickFnOk r rv.tick') →
    (∀ m ∈ msgsAA, AAMsgOk id s.term m) →
    (∀ m ∈ msgs ++ msgsAA, OutTermOk s.prevote s.term m) →
    s.gh.outlb ≤ msgs.length + msgsAA.length →
    (s.gh.unst = true → nextUnstable s.logst ≠ [] ∨ s.logst.snap ≠ none) →
    (s.role ≠ .follower → id ∈ c.voters) →
    ⊢ raftOwn (GF := GF) r rv -∗
      isLogger lok -∗
      ownTrackerC c rv.trk' ⟨s.votes, s.progress, s.prvals⟩ -∗
      ownRaftLog rv.raftLog' s.logst -∗
      rv.msgs' ↦* msgs -∗
      ownSliceCap raftpb.Message rv.msgs' (DFrac.own 1) -∗
      rv.msgsAfterAppend' ↦* msgsAA -∗
      ownSliceCap raftpb.Message rv.msgsAfterAppend' (DFrac.own 1) -∗
      ownRaftMisc rv.readStates' rv.readOnly' rv.pendingReadIndexMessages' s.rd -∗
      outboxRel s.outbox msgs msgsAA -∗
      ownRaftPhysC c r id s := by
  intro Hid Hterm Hvote Hlead Hstate Hstepfn Hprevote HpropForward HnoCCV HnoCheckQuorum
    HnoLearner HnoTransfer Hpci Hid_nz HelectionTimeout Hlok Hlogp Htick HmsgsAA_ok Hout_term
    Hgh_out Hgh_unst Hvoter
  iintro Hr #Hlogger Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc #Houtbox
  rw [ownRaftPhysC_unseal]; unfold ownRaftPhysG
  iexists rv, msgs, msgsAA, lok
  simp only [named]
  iframe Hr Hlogger Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc Houtbox
  ipureintro
  exact ⟨Hid, Hterm, Hvote, Hlead, Hstate, Hstepfn, Htick, Hlogp, HmsgsAA_ok, Hout_term,
    Hgh_out, Hgh_unst, Hvoter, Hprevote,
    HpropForward, HnoCCV, HnoCheckQuorum, HnoLearner, HnoTransfer, Hpci, Hid_nz, HelectionTimeout, Hlok⟩
end proof

set_option hygiene false in
/-- Rocq `iNamed_phys`: open `ownRaftPhys` in the hypothesis `H` and name its
conjuncts (`rv`, `msgs`, `msgsAA`, `lok`, `Hr`, `Hid`, ...). In this file only. -/
local macro "iNamed_phys " H:ident : tactic =>
  `(tactic| (ihave $H:ident := ownRaftPhys_open _ _ _ _ $$ $H:ident;
             iunfold ownRaftPhysDef at $H:ident;
             iunfold ownRaftPhysG at $H:ident;
             icases $H:ident with ⟨%rv, %msgs, %msgsAA, %lok, $H:ident⟩;
             iNamed $H:ident))

set_option hygiene false in
/-- The pure premises of `ownRaftPhys_intro` after a field access: each is a
hypothesis of the opened predicate up to computation, or holds by computation. -/
local macro "phys_pure" : tactic =>
  `(tactic| first | assumption | rfl | exact Htick | exact Hout_term | exact Hgh_out | exact Hgh_unst | exact Hvoter | exact ⟨rfl, fun h => Hid_nz h.symm⟩ | exact ⟨rfl, Hx⟩)

set_option hygiene false in
/-- Rocq `reseal`: re-seal at the state `s'` the goal names, given explicitly because
otherwise `ownRaftPhys_intro`'s `s` is fixed by `Htrk` -- at the state *before* the
access -- and the conclusion no longer matches. -/
local macro "reseal " s:term:max : tactic =>
  `(tactic| (iapply ownRaftPhys_intro _ _ _ $s _ msgs msgsAA lok
                (by phys_pure) (by phys_pure) (by phys_pure) (by phys_pure) (by phys_pure)
                (by phys_pure) (by phys_pure) (by phys_pure) (by phys_pure) (by phys_pure)
                (by phys_pure) (by phys_pure) (by phys_pure) (by phys_pure) (by phys_pure)
                (by phys_pure) (by phys_pure) (by phys_pure) (by phys_pure) (by phys_pure)
                (by phys_pure) (by phys_pure) (by phys_pure)
                $$ Hr Hlogger Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc Houtbox))

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

-- The (fixed) set of voters.
variable (cfg : GSet w64)

/-- The progress map in `s` is the tracker's, and so tracks every voter (and the
learners: since 2026-10-13 its domain is no longer `cfg`). Read out without consuming
anything. -/
theorem ownRaftPhys_progress_dom (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhys (GF := GF) cfg r id s -∗
      ⌜cfg ⊆ domSet s.progress⌝ ∗ ownRaftPhys cfg r id s := by
  iintro H
  iNamed_phys H
  icases ownTracker_progress_map cfg _ _ $$ Htrk with ⟨#Hprs, %Hdom, Htrk⟩
  isplitr
  · ipureintro; exact Hdom
  reseal s

/-- The progress map tracks at most `2^62` ids (2026-10-13): read out without consuming
anything. -/
theorem ownRaftPhys_progress_size (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhys (GF := GF) cfg r id s -∗
      ⌜(GMap.size s.progress : Int) ≤ 2 ^ 62⌝ ∗ ownRaftPhys cfg r id s := by
  iintro H
  iNamed_phys H
  icases ownTracker_size_prs cfg _ _ $$ Htrk with ⟨%Hsz, Htrk⟩
  isplitr
  · ipureintro; exact Hsz
  reseal s

/-- The leader-transfer target is never the node itself (2026-10-13): read out without
consuming anything. -/
theorem ownRaftPhys_lt_ne (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhys (GF := GF) cfg r id s -∗ ⌜s.lt ≠ id⌝ ∗ ownRaftPhys cfg r id s := by
  iintro H
  iNamed_phys H
  isplitr
  · ipureintro; exact HnoTransfer.2
  reseal s

/-- Only a voter is out of the follower role (2026-10-13): read out without consuming
anything. -/
theorem ownRaftPhys_voter (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhys (GF := GF) cfg r id s -∗
      ⌜s.role ≠ .follower → id ∈ cfg⌝ ∗ ownRaftPhys cfg r id s := by
  iintro H
  iNamed_phys H
  isplitr
  · ipureintro; exact Hvoter
  reseal s

/-- Changing only the outbox, up to permutation. -/
theorem ownRaftPhys_outbox (r : Loc) (id : w64) (s : NState) (o : List Msg) :
    o ≡ₚ s.outbox →
    ⊢ ownRaftPhys (GF := GF) cfg r id s -∗ ownRaftPhys cfg r id { s with outbox := o } := by
  intro Ho
  iintro H
  iNamed_phys H
  ihave #Houtbox' := outboxRel_perm _ o _ _ Ho $$ Houtbox
  iapply ownRaftPhys_intro _ _ _ { s with outbox := o } _ msgs msgsAA lok
    Hid Hterm Hvote Hlead Hstate Hstepfn Hprevote HpropForward HnoCCV HnoCheckQuorum HnoLearner
    HnoTransfer Hpci Hid_nz HelectionTimeout Hlok Hlogp Htick HmsgsAA_ok Hout_term Hgh_out Hgh_unst Hvoter
    $$ Hr Hlogger Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc Houtbox'

/-- Sending nothing, in both directions: an exit that sends nothing proves a
postcondition stated at `sendMsgs s ms` with `ms = []`, and a `send` of a message the
model does not see comes back at `sendMsgs s []`. -/
theorem ownRaftPhys_send_nil (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhys (GF := GF) cfg r id s -∗ ownRaftPhys cfg r id (sendMsgs s []) := by
  have H : sendMsgs s [] = s := by cases s; simp [sendMsgs]
  rw [H]; iintro H; iexact H

theorem ownRaftPhys_unsend (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhys (GF := GF) cfg r id (sendMsgs s []) -∗ ownRaftPhys cfg r id s := by
  have H : sendMsgs s [] = s := by cases s; simp [sendMsgs]
  rw [H]; iintro H; iexact H

/-! ## The interface: field lemmas and accessors

**Program proofs do not unfold `ownRaftPhys`.** Every access to the raft struct goes
through one of the lemmas below, so that the struct's representation -- `r ↦ rv`, the
abstraction relation, the scope assumptions -- is written down, and relied on, in this
file alone. Changing the representation then means re-proving this section, not the
program proofs. (Decided 2026-09-24; notes/decisions.md, "Program proofs do not unfold
`own_raft_phys`".)

`wp_auto` is *not* used for these accesses. Its field automation builds on full
ownership of the struct, `r ↦ rv`, which is exactly the representation this predicate
hides: with `ownRaftPhys` sealed, `wp_auto` stops in front of a load or store of a raft
field, and the proof continues with the lemma for that field, named explicitly:
`wp_apply raft.wp_load_Term $$ Hphys as Hphys`. There is deliberately no tactic that
searches the lemmas for the one that applies: each failed `wp_apply` walks the whole
program, and a proof that names its lemma says which field it touches.

There are three kinds.

- **Scalar fields**, one Hoare triple per load and per store, stated at the expression
  `wp_auto` leaves behind: `App (Val (GoInstruction (GoLoad t))) (Val #(r.[raft, f]))`
  and `App (Val (GoInstruction (GoStore t))) (Val (PairV #(r.[raft, f]) #v))`. A field
  `NState` tracks is loaded at its abstract value and a store updates `s`; a field
  pinned by a scope assumption is loaded at the pinned value and has no store (or only
  a store of that value); a field the abstraction does not track is loaded at an
  unknown value and stored freely. If a proof needs to know more about one of the
  latter -- that two loads agree, say -- the rule is the usual one: add it to `NState`.
- **Heap hanging off a field**: the tracker, the log, the two message queues, the
  `readOnly` object. An *accessor* hands out the field's points-to and the object's own
  predicate, together with a wand that takes them back -- possibly changed -- and gives
  `ownRaftPhys` at the correspondingly changed state. What the object is then used for
  (a map lookup in `trk.Progress`, `raftLog` methods, `append` on a queue) is the
  object's business, specified by its own predicate, so no operation on it is
  duplicated here.

Nothing is ever lent out of the predicate: an accessor's wand is the only way to hold
part of the struct across a step, and a call on the struct needs the predicate whole.
(Until 2026-09-29 there were loans, `own_raft_phys_lend` / `own_raft_phys_unlend`,
which moved the tracker's heap out of the predicate for the length of a function body;
`nstate.lent`.) -/

private theorem wp_load_access {V : Type} {t : go.GoType} [ZeroVal V]
    [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V t]
    (l : Loc) (v : V) (P : IProp GF) (h : AccessStrict (l ↦ v) (l ↦ v) P P) :
    {{ P }} (App (Val (GoInstruction (GoLoad t))) (Val #l)) {{ RET #v; P }} := by
  iintro %Φ HP HΦ
  icases h.access_strict $$ HP with ⟨Hl, Hback⟩
  iapply IntoValTyped.wp_load (t := t) l (DFrac.own 1) v $$ Hl
  inext
  iintro Hl
  iapply HΦ
  iapply Hback $$ Hl

private theorem wp_store_access {V : Type} {t : go.GoType} [ZeroVal V]
    [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V t]
    (l : Loc) (v w : V) (P P' : IProp GF) (h : AccessStrict (l ↦ v) (l ↦ w) P P') :
    {{ P }} (App (Val (GoInstruction (GoStore t))) (Val (PairV #l #w))) {{ RET #(); P' }} := by
  iintro %Φ HP HΦ
  icases h.access_strict $$ HP with ⟨Hl, Hback⟩
  iapply IntoValTyped.wp_store (t := t) l v w $$ Hl
  inext
  iintro Hl
  iapply HΦ
  iapply Hback $$ Hl

/-- A load from a persistent points-to (`raftOwn`'s `id` and `logger`, 2026-10-10). -/
theorem wp_load_pers {V : Type} {t : go.GoType} [ZeroVal V]
    [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V t] (l : Loc) (v : V) :
    {{ (l ↦□ v : IProp GF) }} (App (Val (GoInstruction (GoLoad t))) (Val #l))
    {{ RET #v; True }} := by
  iintro %Φ #Hl HΦ
  iapply IntoValTyped.wp_load (t := t) l DFrac.discard v $$ Hl
  inext
  iintro -
  iapply HΦ
  itrivial

/-! ### Loads of fields `NState` tracks, and of the pinned ones -/

theorem raft.wp_load_id (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoLoad go.uint64))) (Val #(r.[raft, go!"id"])))
    {{ RET #id; ownRaftPhys cfg r id s }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  ihave #Hfid := raftOwn_id _ _ $$ Hr
  wp_apply wp_load_pers _ rv.id' $$ Hfid
  rw [Hid]; iapply HΦ; reseal s

theorem raft.wp_load_Term (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoLoad go.uint64))) (Val #(r.[raft, go!"Term"])))
    {{ RET #s.term; ownRaftPhys cfg r id s }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_load_access _ rv.Term' _ (raftOwn_access_load_Term _ _) $$ Hr as Hr
  rw [Hterm]; iapply HΦ; reseal s

theorem raft.wp_load_Vote (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoLoad go.uint64))) (Val #(r.[raft, go!"Vote"])))
    {{ RET #s.vote; ownRaftPhys cfg r id s }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_load_access _ rv.Vote' _ (raftOwn_access_load_Vote _ _) $$ Hr as Hr
  rw [Hvote]; iapply HΦ; reseal s

theorem raft.wp_load_lead (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoLoad go.uint64))) (Val #(r.[raft, go!"lead"])))
    {{ RET #s.lead; ownRaftPhys cfg r id s }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_load_access _ rv.lead' _ (raftOwn_access_load_lead _ _) $$ Hr as Hr
  rw [Hlead]; iapply HΦ; reseal s

theorem raft.wp_load_state (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoLoad StateType.ty))) (Val #(r.[raft, go!"state"])))
    {{ RET #(stateW64 s.role); ownRaftPhys cfg r id s }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_load_access _ rv.state' _ (raftOwn_access_load_state _ _) $$ Hr as Hr
  rw [Hstate]; iapply HΦ; reseal s

theorem raft.wp_load_step (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoLoad stepFunc.ty))) (Val #(r.[raft, go!"step"])))
    {{ RET #s.stepfn; ownRaftPhys cfg r id s }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_load_access _ rv.step' _ (raftOwn_access_load_step _ _) $$ Hr as Hr
  rw [Hstepfn]; iapply HΦ; reseal s

/-- The log's *location*. Its contents are `ownRaftPhys_log_at`'s. -/
theorem raft.wp_load_raftLog (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoLoad (go.GoType.PointerType raftLog.ty))))
        (Val #(r.[raft, go!"raftLog"])))
    {{ RET #s.log; ownRaftPhys cfg r id s }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_load_access _ rv.raftLog' _ (raftOwn_access_load_raftLog _ _) $$ Hr as Hr
  rw [show (#rv.raftLog' : val) = #s.log by rw [Hlogp]]; iapply HΦ; reseal s

theorem raft.wp_load_logger (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoLoad Logger.ty))) (Val #(r.[raft, go!"logger"])))
    {{ (lok : GoInterfaceOk), RET #(interface.ok lok);
        ownRaftPhys cfg r id s ∗ isLogger lok }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  ihave #Hflg := raftOwn_logger _ _ $$ Hr
  wp_apply wp_load_pers _ rv.logger' $$ Hflg
  rw [Hlok]; iapply HΦ
  isplitl
  · reseal s
  · iexact Hlogger

/-- The two fields shared with other goroutines (2026-10-10, `raftOwn`): `node.go`'s
`Tick` reads `r.logger` and `r.id` while `run` owns the struct. -/
theorem ownRaftPhys_shared (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhys (GF := GF) cfg r id s -∗
      ∃ lok : GoInterfaceOk, r.[raft, go!"id"] ↦□ id ∗
        r.[raft, go!"logger"] ↦□ (interface.ok lok : GoInterface) ∗ isLogger lok ∗
        ownRaftPhys cfg r id s := by
  iintro H
  iNamed_phys H
  ihave #Hfid := raftOwn_id _ _ $$ Hr
  ihave #Hflg := raftOwn_logger _ _ $$ Hr
  ihave #Hfid' : r.[raft, go!"id"] ↦□ id $$ [Hfid]
  · rw [← Hid]; iexact Hfid
  ihave #Hflg' : r.[raft, go!"logger"] ↦□ (interface.ok lok : GoInterface) $$ [Hflg]
  · rw [← Hlok]; iexact Hflg
  iexists lok
  iframe Hfid' Hflg' Hlogger
  reseal s

theorem raft.wp_load_checkQuorum (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoLoad go.bool))) (Val #(r.[raft, go!"checkQuorum"])))
    {{ RET #false; ownRaftPhys cfg r id s }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_load_access _ rv.checkQuorum' _ (raftOwn_access_load_checkQuorum _ _) $$ Hr as Hr
  rw [HnoCheckQuorum]; iapply HΦ; reseal s

theorem raft.wp_load_preVote (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoLoad go.bool))) (Val #(r.[raft, go!"preVote"])))
    {{ RET #s.prevote; ownRaftPhys cfg r id s }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_load_access _ rv.preVote' _ (raftOwn_access_load_preVote _ _) $$ Hr as Hr
  rw [Hprevote]; iapply HΦ; reseal s

theorem raft.wp_load_disableProposalForwarding (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoLoad go.bool)))
        (Val #(r.[raft, go!"disableProposalForwarding"])))
    {{ RET #false; ownRaftPhys cfg r id s }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_load_access _ rv.disableProposalForwarding' _ (raftOwn_access_load_disableProposalForwarding _ _) $$ Hr as Hr
  rw [HpropForward]; iapply HΦ; reseal s

/-- `false` (2026-10-13): `ownRaftPhys`'s scope conjunct. -/
theorem raft.wp_load_disableConfChangeValidation (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoLoad go.bool)))
        (Val #(r.[raft, go!"disableConfChangeValidation"])))
    {{ RET #false; ownRaftPhys cfg r id s }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_load_access _ rv.disableConfChangeValidation' _ (raftOwn_access_load_disableConfChangeValidation _ _) $$ Hr as Hr
  rw [HnoCCV]; iapply HΦ; reseal s

theorem raft.wp_load_isLearner (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoLoad go.bool))) (Val #(r.[raft, go!"isLearner"])))
    {{ RET #s.isLearner; ownRaftPhys cfg r id s }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_load_access _ rv.isLearner' _ (raftOwn_access_load_isLearner _ _) $$ Hr as Hr
  rw [HnoLearner]; iapply HΦ; reseal s

theorem raft.wp_load_leadTransferee (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoLoad go.uint64))) (Val #(r.[raft, go!"leadTransferee"])))
    {{ RET #s.lt; ownRaftPhys cfg r id s }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_load_access _ rv.leadTransferee' _ (raftOwn_access_load_leadTransferee _ _) $$ Hr as Hr
  rw [HnoTransfer.1]; iapply HΦ; reseal s

/-! ### Loads of fields the abstraction does not track -/

theorem raft.wp_load_electionTimeout (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoLoad go.int))) (Val #(r.[raft, go!"electionTimeout"])))
    {{ (v : w64), RET #v; ownRaftPhys cfg r id s ∗ ⌜0 < sint.Z v⌝ }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_load_access _ rv.electionTimeout' _ (raftOwn_access_load_electionTimeout _ _) $$ Hr as Hr
  iapply HΦ
  isplitl
  · reseal s
  · ipureintro; exact HelectionTimeout

theorem raft.wp_load_electionElapsed (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoLoad go.int))) (Val #(r.[raft, go!"electionElapsed"])))
    {{ (v : w64), RET #v; ownRaftPhys cfg r id s }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_load_access _ rv.electionElapsed' _ (raftOwn_access_load_electionElapsed _ _) $$ Hr as Hr
  iapply HΦ; reseal s

theorem raft.wp_load_heartbeatElapsed (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoLoad go.int))) (Val #(r.[raft, go!"heartbeatElapsed"])))
    {{ (v : w64), RET #v; ownRaftPhys cfg r id s }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_load_access _ rv.heartbeatElapsed' _ (raftOwn_access_load_heartbeatElapsed _ _) $$ Hr as Hr
  iapply HΦ; reseal s

theorem raft.wp_load_heartbeatTimeout (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoLoad go.int))) (Val #(r.[raft, go!"heartbeatTimeout"])))
    {{ (v : w64), RET #v; ownRaftPhys cfg r id s }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_load_access _ rv.heartbeatTimeout' _ (raftOwn_access_load_heartbeatTimeout _ _) $$ Hr as Hr
  iapply HΦ; reseal s

theorem raft.wp_load_randomizedElectionTimeout (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoLoad go.int)))
        (Val #(r.[raft, go!"randomizedElectionTimeout"])))
    {{ (v : w64), RET #v; ownRaftPhys cfg r id s }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_load_access _ rv.randomizedElectionTimeout' _ (raftOwn_access_load_randomizedElectionTimeout _ _) $$ Hr as Hr
  iapply HΦ; reseal s

theorem raft.wp_load_pendingConfIndex (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoLoad go.uint64))) (Val #(r.[raft, go!"pendingConfIndex"])))
    {{ RET #s.pci; ownRaftPhys cfg r id s }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_load_access _ rv.pendingConfIndex' _ (raftOwn_access_load_pendingConfIndex _ _) $$ Hr as Hr
  rw [Hpci]; iapply HΦ; reseal s

theorem raft.wp_load_uncommittedSize (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoLoad entryPayloadSize.ty)))
        (Val #(r.[raft, go!"uncommittedSize"])))
    {{ (v : entryPayloadSize), RET #v; ownRaftPhys cfg r id s }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_load_access _ rv.uncommittedSize' _ (raftOwn_access_load_uncommittedSize _ _) $$ Hr as Hr
  iapply HΦ; reseal s

theorem raft.wp_load_maxUncommittedSize (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoLoad entryPayloadSize.ty)))
        (Val #(r.[raft, go!"maxUncommittedSize"])))
    {{ (v : entryPayloadSize), RET #v; ownRaftPhys cfg r id s }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_load_access _ rv.maxUncommittedSize' _ (raftOwn_access_load_maxUncommittedSize _ _) $$ Hr as Hr
  iapply HΦ; reseal s

theorem raft.wp_load_maxMsgSize (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoLoad entryEncodingSize.ty)))
        (Val #(r.[raft, go!"maxMsgSize"])))
    {{ (v : entryEncodingSize), RET #v; ownRaftPhys cfg r id s }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_load_access _ rv.maxMsgSize' _ (raftOwn_access_load_maxMsgSize _ _) $$ Hr as Hr
  iapply HΦ; reseal s

/-! ### Stores to fields `NState` tracks -/

/-- The term never moves back (2026-10-10): `msgsAfterAppend`'s term bounds
(`AAMsgOk`) are relative to it. -/
theorem raft.wp_store_Term (r : Loc) (id : w64) (s : NState) (v : w64)
    (Hle : uint.Z s.term ≤ uint.Z v) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoStore go.uint64))) (Val (PairV #(r.[raft, go!"Term"]) #v)))
    {{ RET #(); ownRaftPhys cfg r id { s with term := v } }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_store_access _ rv.Term' v _ _ (raftOwn_access_store_Term _ _ _) $$ Hr as Hr
  have HmsgsAA_ok' : ∀ m ∈ msgsAA, AAMsgOk id v m :=
    fun m Hm => (HmsgsAA_ok m Hm).mono Hle
  have Hout_term' : ∀ m ∈ msgs ++ msgsAA, OutTermOk s.prevote v m :=
    fun m Hm => (Hout_term m Hm).mono Hle
  iapply HΦ
  iapply ownRaftPhys_intro _ _ _ { s with term := v } _ msgs msgsAA lok
    (by phys_pure) (by phys_pure) (by phys_pure) (by phys_pure) (by phys_pure)
    (by phys_pure) (by phys_pure) (by phys_pure) (by phys_pure) (by phys_pure)
    (by phys_pure) (by phys_pure) (by phys_pure) (by phys_pure) (by phys_pure)
    (by phys_pure) (by phys_pure) (by phys_pure) HmsgsAA_ok' Hout_term' Hgh_out Hgh_unst Hvoter
    $$ Hr Hlogger Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc Houtbox

theorem raft.wp_store_Vote (r : Loc) (id : w64) (s : NState) (v : w64) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoStore go.uint64))) (Val (PairV #(r.[raft, go!"Vote"]) #v)))
    {{ RET #(); ownRaftPhys cfg r id { s with vote := v } }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_store_access _ rv.Vote' v _ _ (raftOwn_access_store_Vote _ _ _) $$ Hr as Hr
  iapply HΦ; reseal { s with vote := v }

theorem raft.wp_store_lead (r : Loc) (id : w64) (s : NState) (v : w64) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoStore go.uint64))) (Val (PairV #(r.[raft, go!"lead"]) #v)))
    {{ RET #(); ownRaftPhys cfg r id { s with lead := v } }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_store_access _ rv.lead' v _ _ (raftOwn_access_store_lead _ _ _) $$ Hr as Hr
  iapply HΦ; reseal { s with lead := v }

/-- Stated at `stateW64 ro`, so the caller names the role; the Go code stores the
constant (`StateFollower` = `W64 0`), which unifies with `stateW64 .follower` by
computation. -/
theorem raft.wp_store_state (r : Loc) (id : w64) (s : NState) (ro : PRole)
    (Hro : ro ≠ .follower → id ∈ cfg) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoStore StateType.ty)))
        (Val (PairV #(r.[raft, go!"state"]) #(stateW64 ro))))
    {{ RET #(); ownRaftPhys cfg r id { s with role := ro } }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_store_access _ rv.state' (stateW64 ro) _ _ (raftOwn_access_store_state _ _ _) $$ Hr as Hr
  have Hvoter' : ({ s with role := ro } : NState).role ≠ .follower → id ∈ cfg := Hro
  iapply HΦ
  iapply ownRaftPhys_intro _ _ _ { s with role := ro } _ msgs msgsAA lok
    (by phys_pure) (by phys_pure) (by phys_pure) (by phys_pure) (by phys_pure)
    (by phys_pure) (by phys_pure) (by phys_pure) (by phys_pure) (by phys_pure)
    (by phys_pure) (by phys_pure) (by phys_pure) (by phys_pure) (by phys_pure)
    (by phys_pure) (by phys_pure) (by phys_pure) (by phys_pure) (by phys_pure)
    (by phys_pure) (by phys_pure) Hvoter'
    $$ Hr Hlogger Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc Houtbox

theorem raft.wp_store_step (r : Loc) (id : w64) (s : NState) (f : GoFunc) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoStore stepFunc.ty))) (Val (PairV #(r.[raft, go!"step"]) #f)))
    {{ RET #(); ownRaftPhys cfg r id { s with stepfn := f } }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_store_access _ rv.step' f _ _ (raftOwn_access_store_step _ _ _) $$ Hr as Hr
  iapply HΦ; reseal { s with stepfn := f }

/-! ### Stores to fields the abstraction does not track, and the pinned one -/

/-- `r.tick = f`, for one of the two tick functions: `r.tick` is set from now on. -/
theorem raft.wp_store_tick (r : Loc) (id : w64) (s : NState) (f : GoFunc)
    (Hf : TickFnOk r f) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoStore (go.GoType.FunctionType (go.signature.Signature [] false [])))))
        (Val (PairV #(r.[raft, go!"tick"]) #f)))
    {{ RET #(); ownRaftPhys cfg r id { s with ticking := true } }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_store_access _ rv.tick' f _ _ (raftOwn_access_store_tick _ _ _) $$ Hr as Hr
  iapply HΦ
  iapply ownRaftPhys_intro _ _ _ { s with ticking := true } _ msgs msgsAA lok
    (by phys_pure) (by phys_pure) (by phys_pure) (by phys_pure) (by phys_pure)
    (by phys_pure) (by phys_pure) (by phys_pure) (by phys_pure) (by phys_pure)
    (by phys_pure) (by phys_pure) (by phys_pure) (by phys_pure) (by phys_pure)
    (by phys_pure) (by phys_pure) (fun _ => Hf) (by phys_pure) (by phys_pure) Hgh_out Hgh_unst Hvoter
    $$ Hr Hlogger Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc Houtbox

/-- `r.tick`, once set: one of the two tick functions. -/
theorem raft.wp_load_tick (r : Loc) (id : w64) (s : NState) (Ht : s.ticking = true) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoLoad (go.GoType.FunctionType (go.signature.Signature [] false [])))))
        (Val #(r.[raft, go!"tick"])))
    {{ (f : GoFunc), RET #f; ownRaftPhys cfg r id s ∗ ⌜TickFnOk r f⌝ }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_load_access _ rv.tick' _ (raftOwn_access_load_tick _ _) $$ Hr as Hr
  iapply HΦ
  isplitl
  · reseal s
  ipureintro; exact Htick Ht

theorem raft.wp_store_electionElapsed (r : Loc) (id : w64) (s : NState) (v : w64) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoStore go.int)))
        (Val (PairV #(r.[raft, go!"electionElapsed"]) #v)))
    {{ RET #(); ownRaftPhys cfg r id s }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_store_access _ rv.electionElapsed' v _ _ (raftOwn_access_store_electionElapsed _ _ _) $$ Hr as Hr
  iapply HΦ; reseal s

theorem raft.wp_store_heartbeatElapsed (r : Loc) (id : w64) (s : NState) (v : w64) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoStore go.int)))
        (Val (PairV #(r.[raft, go!"heartbeatElapsed"]) #v)))
    {{ RET #(); ownRaftPhys cfg r id s }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_store_access _ rv.heartbeatElapsed' v _ _ (raftOwn_access_store_heartbeatElapsed _ _ _) $$ Hr as Hr
  iapply HΦ; reseal s

theorem raft.wp_store_randomizedElectionTimeout (r : Loc) (id : w64) (s : NState) (v : w64) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoStore go.int)))
        (Val (PairV #(r.[raft, go!"randomizedElectionTimeout"]) #v)))
    {{ RET #(); ownRaftPhys cfg r id s }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_store_access _ rv.randomizedElectionTimeout' v _ _ (raftOwn_access_store_randomizedElectionTimeout _ _ _) $$ Hr as Hr
  iapply HΦ; reseal s

theorem raft.wp_store_pendingConfIndex (r : Loc) (id : w64) (s : NState) (v : w64) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoStore go.uint64)))
        (Val (PairV #(r.[raft, go!"pendingConfIndex"]) #v)))
    {{ RET #(); ownRaftPhys cfg r id { s with pci := v } }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_store_access _ rv.pendingConfIndex' v _ _ (raftOwn_access_store_pendingConfIndex _ _ _) $$ Hr as Hr
  iapply HΦ; reseal { s with pci := v }

theorem raft.wp_store_uncommittedSize (r : Loc) (id : w64) (s : NState) (v : entryPayloadSize) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoStore entryPayloadSize.ty)))
        (Val (PairV #(r.[raft, go!"uncommittedSize"]) #v)))
    {{ RET #(); ownRaftPhys cfg r id s }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_store_access _ rv.uncommittedSize' v _ _ (raftOwn_access_store_uncommittedSize _ _ _) $$ Hr as Hr
  iapply HΦ; reseal s

/-- `switchToConfig` stores `ok && pr.IsLearner` (any value since 2026-10-13, recorded in
`NState.isLearner`; until then only `false`). -/
theorem raft.wp_store_isLearner (r : Loc) (id : w64) (s : NState) (b : Bool) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoStore go.bool)))
        (Val (PairV #(r.[raft, go!"isLearner"]) #b)))
    {{ RET #(); ownRaftPhys cfg r id { s with isLearner := b } }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_store_access _ rv.isLearner' b _ _ (raftOwn_access_store_isLearner _ _ _) $$ Hr as Hr
  iapply HΦ; reseal { s with isLearner := b }

/-- `None` (`W64 0`, `abortLeaderTransfer`). -/
theorem raft.wp_store_leadTransferee (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoStore go.uint64)))
        (Val (PairV #(r.[raft, go!"leadTransferee"]) #(W64 0))))
    {{ RET #(); ownRaftPhys cfg r id { s with lt := W64 0 } }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_store_access _ rv.leadTransferee' (W64 0) _ _ (raftOwn_access_store_leadTransferee _ _ _) $$ Hr as Hr
  iapply HΦ; reseal { s with lt := W64 0 }

/-- Another node (2026-10-13, `stepLeader`'s `MsgTransferLeader`). -/
theorem raft.wp_store_leadTransferee_to (r : Loc) (id : w64) (s : NState) (x : w64)
    (Hx : x ≠ id) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoStore go.uint64)))
        (Val (PairV #(r.[raft, go!"leadTransferee"]) #x)))
    {{ RET #(); ownRaftPhys cfg r id { s with lt := x } }} := by
  iintro %Φ H HΦ
  iNamed_phys H
  wp_apply wp_store_access _ rv.leadTransferee' x _ _ (raftOwn_access_store_leadTransferee _ _ _) $$ Hr as Hr
  iapply HΦ; reseal { s with lt := x }

/-- Two states that are equal: for a state reached by a run of field stores and the
name a spec gives it (`becomeFollower s t l`, say). Proving the `=` with `rfl` is
cheap; leaving it to unification inside `iframe` can run for minutes (in Rocq;
notes/gotchas.md). -/
theorem ownRaftPhys_eq (r : Loc) (id : w64) (s1 s2 : NState) :
    s1 = s2 → ⊢ ownRaftPhys (GF := GF) cfg r id s1 -∗ ownRaftPhys cfg r id s2 := by
  intro H; subst H; iintro H; iexact H

end proof

/-! ### Accessors -/

set_option hygiene false in
/-- Rocq `split_field_proof`: one field of the struct points-to, with a wand taking
back *any* value. The generated `AccessStrict` store instance fixes the new value when
it is applied, which is too early for a value a later call produces (see
notes/gotchas.md); these unseal `l ↦ rv` instead. The pattern names the field `Hx` by
position and keeps every later field in one hypothesis `Hrest` (in Rocq, framing the 33
field points-tos one by one cost ~40s per lemma, this ~6s; 2026-09-24). -/
local macro "split_field_proof " f:ident : tactic =>
  `(tactic| (unfold raftOwn
             iintro Hf
             iNamed Hf
             iframe $f:ident
             iintro %x $f:ident
             simp only [named]
             iframe
             try iframe #))

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

private theorem raft_split_trk (l : Loc) (rv : raft) :
    ⊢ raftOwn (GF := GF) l rv -∗
      l.[raft, go!"trk"] ↦ rv.trk' ∗
      (∀ x, l.[raft, go!"trk"] ↦ x -∗ raftOwn l { rv with trk' := x }) := by
  split_field_proof H_trk

private theorem raft_split_msgs (l : Loc) (rv : raft) :
    ⊢ raftOwn (GF := GF) l rv -∗
      l.[raft, go!"msgs"] ↦ rv.msgs' ∗
      (∀ x, l.[raft, go!"msgs"] ↦ x -∗ raftOwn l { rv with msgs' := x }) := by
  split_field_proof H_msgs

private theorem raft_split_msgsAA (l : Loc) (rv : raft) :
    ⊢ raftOwn (GF := GF) l rv -∗
      l.[raft, go!"msgsAfterAppend"] ↦ rv.msgsAfterAppend' ∗
      (∀ x, l.[raft, go!"msgsAfterAppend"] ↦ x -∗ raftOwn l { rv with msgsAfterAppend' := x }) := by
  split_field_proof H_msgsAfterAppend

/-- The fields `RawNode.Ready`/`HasReady` touch, out of the struct at once (2026-10-05).
`readyWithoutAccept` sets `rd.Messages := r.msgs` and appends `r.msgsAfterAppend`'s
outgoing messages to it -- *in place*, into `r.msgs`' spare capacity -- and only
`acceptReady` then sets both queues to `nil`; in between it reads `r.id`, `r.Term`,
`r.raftLog` and the log. The struct is not `ownRaftPhys` in between (the queue's slack
belongs to `rd.Messages`, and a `send` would overwrite it), so the whole of `Ready` is
proved with the struct open through this accessor: the scalar fields it reads, the two
queues with their contents and capacity, the log, and a wand that takes them back with
any queues, any abstract outbox they relate to, and the log at any state. `readStates`
goes back at any value (2026-10-13: `acceptReady` sets it to `nil`). -/
private theorem raft_split_view (l : Loc) (rv : raft) :
    ⊢ raftOwn (GF := GF) l rv -∗
      l.[raft, go!"id"] ↦□ rv.id' ∗
      l.[raft, go!"Term"] ↦ rv.Term' ∗
      l.[raft, go!"Vote"] ↦ rv.Vote' ∗
      l.[raft, go!"readStates"] ↦ rv.readStates' ∗
      l.[raft, go!"raftLog"] ↦ rv.raftLog' ∗
      l.[raft, go!"state"] ↦ rv.state' ∗
      l.[raft, go!"msgs"] ↦ rv.msgs' ∗
      l.[raft, go!"msgsAfterAppend"] ↦ rv.msgsAfterAppend' ∗
      l.[raft, go!"lead"] ↦ rv.lead' ∗
      (∀ x y z, l.[raft, go!"Term"] ↦ rv.Term' -∗
              l.[raft, go!"Vote"] ↦ rv.Vote' -∗
              l.[raft, go!"readStates"] ↦ z -∗
              l.[raft, go!"raftLog"] ↦ rv.raftLog' -∗
              l.[raft, go!"state"] ↦ rv.state' -∗
              l.[raft, go!"msgs"] ↦ x -∗
              l.[raft, go!"msgsAfterAppend"] ↦ y -∗
              l.[raft, go!"lead"] ↦ rv.lead' -∗
              raftOwn l { rv with msgs' := x, msgsAfterAppend' := y, readStates' := z }) := by
  unfold raftOwn
  iintro Hf
  iNamed Hf
  iframe H_id H_Term H_Vote H_readStates H_raftLog H_state H_msgs H_msgsAfterAppend H_lead
  iintro %x %y %z H_Term H_Vote H_readStates H_raftLog H_state H_msgs H_msgsAfterAppend H_lead
  simp only [named]
  iframe
  try iframe #

/-- The three read-index fields (2026-10-12): `ownRaftPhys_misc`. -/
private theorem raft_split_misc (l : Loc) (rv : raft) :
    ⊢ raftOwn (GF := GF) l rv -∗
      l.[raft, go!"readStates"] ↦ rv.readStates' ∗
      l.[raft, go!"readOnly"] ↦ rv.readOnly' ∗
      l.[raft, go!"pendingReadIndexMessages"] ↦ rv.pendingReadIndexMessages' ∗
      (∀ x y z, l.[raft, go!"readStates"] ↦ x -∗
              l.[raft, go!"readOnly"] ↦ y -∗
              l.[raft, go!"pendingReadIndexMessages"] ↦ z -∗
              raftOwn l { rv with readStates' := x, readOnly' := y,
                                  pendingReadIndexMessages' := z }) := by
  unfold raftOwn
  iintro Hf
  iNamed Hf
  iframe H_readStates H_readOnly H_pendingReadIndexMessages
  iintro %x %y %z H_readStates H_readOnly H_pendingReadIndexMessages
  simp only [named]
  iframe
  try iframe #

private theorem raft_split_readOnly (l : Loc) (rv : raft) :
    ⊢ raftOwn (GF := GF) l rv -∗
      l.[raft, go!"readOnly"] ↦ rv.readOnly' ∗
      (∀ x, l.[raft, go!"readOnly"] ↦ x -∗ raftOwn l { rv with readOnly' := x }) := by
  split_field_proof H_readOnly

/-- Two fields at once, `raftLog` (read-only here) and `trk`: for
`ownRaftPhys_retrack`. -/
private theorem raft_split_raftLog_trk (l : Loc) (rv : raft) :
    ⊢ raftOwn (GF := GF) l rv -∗
      l.[raft, go!"raftLog"] ↦ rv.raftLog' ∗
      l.[raft, go!"trk"] ↦ rv.trk' ∗
      (∀ x, l.[raft, go!"raftLog"] ↦ rv.raftLog' -∗
            l.[raft, go!"trk"] ↦ x -∗ raftOwn l { rv with trk' := x }) := by
  unfold raftOwn
  iintro Hf
  iNamed Hf
  iframe H_raftLog H_trk
  iintro %x H_raftLog H_trk
  simp only [named]
  iframe
  try iframe #

/-- Two fields at once, `trk` and `readOnly`: for `ownRaftPhys_readOnly_trk`
(2026-10-13). -/
private theorem raft_split_trk_readOnly (l : Loc) (rv : raft) :
    ⊢ raftOwn (GF := GF) l rv -∗
      l.[raft, go!"trk"] ↦ rv.trk' ∗
      l.[raft, go!"readOnly"] ↦ rv.readOnly' ∗
      (∀ x y, l.[raft, go!"trk"] ↦ x -∗
            l.[raft, go!"readOnly"] ↦ y -∗ raftOwn l { rv with trk' := x, readOnly' := y }) := by
  unfold raftOwn
  iintro Hf
  iNamed Hf
  iframe H_trk H_readOnly
  iintro %x %y H_trk H_readOnly
  simp only [named]
  iframe
  try iframe #

-- The (fixed) set of voters.
variable (cfg : GSet w64)

/-- The tracker, as the tracker's own specs take it: the embedded struct's points-to
and `ownTracker`. The wand takes it back at any tracker value and vote tally, and at
the same progress map and `Progress` values (`NState.progress` is stable: nothing on
the election path inserts into the map). A map lookup `r.trk.Progress[i]` is done on
what this hands out, with `ownTracker_progress_map` / `wp_tracker_progress_lookup`; a
function that changes a `Progress` uses `ownRaftPhys_tracker_prvals`. -/
theorem ownRaftPhys_tracker (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhys (GF := GF) cfg r id s -∗
      ∃ tv, r.[raft, go!"trk"] ↦ tv ∗
        ownTracker cfg tv ⟨s.votes, s.progress, s.prvals⟩ ∗
        (∀ tv' votes', r.[raft, go!"trk"] ↦ tv' -∗
           ownTracker cfg tv' ⟨votes', s.progress, s.prvals⟩ -∗
           ownRaftPhys cfg r id { s with votes := votes' }) := by
  iintro H
  iNamed_phys H
  icases raft_split_trk r rv $$ Hr with ⟨Hf, Hback⟩
  iexists rv.trk'
  iframe Hf Htrk
  iintro %tv' %votes' Hf Htrk
  ihave Hr := Hback $$ %tv' Hf
  reseal { s with votes := votes' }

/-- The same, put back at the same tally: the wand gives `ownRaftPhys` at `s` itself
rather than at `{ s with votes := s.votes }`, so a read-only use (a map lookup,
`JointConfig.IDs`), or a split and re-seal repeated inside a `Visit` closure, does not
pile up setters. -/
theorem ownRaftPhys_tracker_same (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhys (GF := GF) cfg r id s -∗
      ∃ tv, r.[raft, go!"trk"] ↦ tv ∗
        ownTracker cfg tv ⟨s.votes, s.progress, s.prvals⟩ ∗
        (∀ tvx, r.[raft, go!"trk"] ↦ tvx -∗
           ownTracker cfg tvx ⟨s.votes, s.progress, s.prvals⟩ -∗
           ownRaftPhys cfg r id s) := by
  iintro Hphys
  icases ownRaftPhys_tracker cfg r id s $$ Hphys with ⟨%tv, Htrkf, Htrk, Hback⟩
  iexists tv
  iframe Htrkf Htrk
  iintro %tvx Htrkf Htrk
  ihave Hphys := Hback $$ %tvx %s.votes Htrkf Htrk
  iapply ownRaftPhys_eq cfg r id _ _ (by cases s; rfl) $$ Hphys

/-- The tracker, put back with new `Progress` values (at the same tally): for a
function that writes a `Progress` -- `reset`'s `Visit` closure, `becomeLeader`'s
`RecentActive` and `BecomeReplicate`, `SentEntries`. -/
theorem ownRaftPhys_tracker_prvals (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhys (GF := GF) cfg r id s -∗
      ∃ tv, r.[raft, go!"trk"] ↦ tv ∗
        ownTracker cfg tv ⟨s.votes, s.progress, s.prvals⟩ ∗
        (∀ tv' pvs', r.[raft, go!"trk"] ↦ tv' -∗
           ownTracker cfg tv' ⟨s.votes, s.progress, pvs'⟩ -∗
           ownRaftPhys cfg r id { s with prvals := pvs' }) := by
  iintro H
  iNamed_phys H
  icases raft_split_trk r rv $$ Hr with ⟨Hf, Hback⟩
  iexists rv.trk'
  iframe Hf Htrk
  iintro %tv' %pvs' Hf Htrk
  ihave Hr := Hback $$ %tv' Hf
  reseal { s with prvals := pvs' }

/-- One peer's `Progress`, borrowed out of the struct by its key at the value
`NState.prvals` records, and given back at that value -- for a read (`IsPaused`, field
loads, `Inflights.Full`). The lookup of `r.trk.Progress[to]` itself goes through
`ownRaftPhys_tracker_same`: it reads the tracker field. The two lookups are premises
inside the logic, so that `s` is fixed by the struct hypothesis the lemma is applied
to, not by the lookups' types: `icases ownRaftPhys_pr … $$ Hphys %Hlk %Hv with …`. -/
theorem ownRaftPhys_pr (r : Loc) (id : w64) (s : NState) (to : w64) (pr : Loc)
    (p : Progress) :
    ⊢ ownRaftPhys (GF := GF) cfg r id s -∗
      ⌜s.progress !! to = some pr⌝ -∗
      ⌜s.prvals !! to = some p⌝ -∗
      ownProgress pr p ∗ (ownProgress pr p -∗ ownRaftPhys cfg r id s) := by
  iintro Hphys %Hlk %Hv
  icases ownRaftPhys_tracker_same cfg r id s $$ Hphys with ⟨%tv, Htrkf, Htrk, Hback⟩
  icases ownTracker_lookup_same cfg tv ⟨s.votes, s.progress, s.prvals⟩ to pr Hlk $$ Htrk
    with ⟨%p', %Hv', Hp, Hpb⟩
  have Heq : p = p' := Option.some.inj (Hv.symm.trans Hv')
  subst Heq
  iframe Hp
  iintro Hp
  ihave Htrk := Hpb $$ Hp
  iapply Hback $$ Htrkf Htrk

/-- The same, given back at new values, which the state then records -- for a write
(`SentEntries`). -/
theorem ownRaftPhys_pr_upd (r : Loc) (id : w64) (s : NState) (to : w64) (pr : Loc)
    (p : Progress) :
    ⊢ ownRaftPhys (GF := GF) cfg r id s -∗
      ⌜s.progress !! to = some pr⌝ -∗
      ⌜s.prvals !! to = some p⌝ -∗
      ownProgress pr p ∗
      (∀ p', ownProgress pr p' -∗ ⌜p'.learner = p.learner⌝ -∗
         ownRaftPhys cfg r id { s with prvals := <[to := p']> s.prvals }) := by
  iintro Hphys %Hlk %Hv
  icases ownRaftPhys_tracker_prvals cfg r id s $$ Hphys with ⟨%tv, Htrkf, Htrk, Hback⟩
  icases ownTracker_lookup cfg tv ⟨s.votes, s.progress, s.prvals⟩ to pr Hlk $$ Htrk
    with ⟨%p', %Hv', Hp, Hpb⟩
  have Heq : p = p' := Option.some.inj (Hv.symm.trans Hv')
  subst Heq
  iframe Hp
  iintro %p'' Hp %Hl
  ihave Htrk := Hpb $$ %p'' Hp %Hl
  iapply Hback $$ Htrkf Htrk

/-- A write that does not need to know the value it overwrites (`SentCommit`). -/
theorem ownRaftPhys_pr_any (r : Loc) (id : w64) (s : NState) (to : w64) (pr : Loc) :
    ⊢ ownRaftPhys (GF := GF) cfg r id s -∗
      ⌜s.progress !! to = some pr⌝ -∗
      ∃ p, ownProgress pr p ∗
      (∀ p', ownProgress pr p' -∗ ⌜p'.learner = p.learner⌝ -∗
         ownRaftPhys cfg r id { s with prvals := <[to := p']> s.prvals }) := by
  iintro Hphys %Hlk
  icases ownRaftPhys_tracker_prvals cfg r id s $$ Hphys with ⟨%tv, Htrkf, Htrk, Hback⟩
  icases ownTracker_lookup cfg tv ⟨s.votes, s.progress, s.prvals⟩ to pr Hlk $$ Htrk
    with ⟨%p', %Hv', Hp, Hpb⟩
  iexists p'
  iframe Hp
  iintro %p'' Hp %Hl
  ihave Htrk := Hpb $$ %p'' Hp %Hl
  iapply Hback $$ Htrkf Htrk

/-- The log, at the state `s` records, put back at any state. This is the accessor for
a function that changes the log (`appendEntry`'s `append`, `loadState`'s `committed`,
`newRaft`'s `appliedTo`). -/
theorem ownRaftPhys_log_at (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhys (GF := GF) cfg r id s -∗
      ownRaftLog s.log s.logst ∗ ⌜LogGhOk s s.logst⌝ ∗
      (∀ ls', ownRaftLog s.log ls' -∗ ⌜LogGhOk s ls'⌝ -∗
        ownRaftPhys cfg r id { s with logst := ls' }) := by
  iintro H
  iNamed_phys H
  ihave Hlog : ownRaftLog (GF := GF) s.log s.logst $$ [Hlog]
  · rw [← Hlogp]; iexact Hlog
  iframe Hlog
  isplitr
  · ipureintro; exact Hgh_unst
  iintro %ls' Hlog %Hgh_unst'
  ihave Hlog : ownRaftLog (GF := GF) rv.raftLog' ls' $$ [Hlog]
  · rw [Hlogp]; iexact Hlog
  iapply ownRaftPhys_intro _ _ _ { s with logst := ls' } _ msgs msgsAA lok
    Hid Hterm Hvote Hlead Hstate Hstepfn Hprevote HpropForward HnoCCV HnoCheckQuorum HnoLearner
    HnoTransfer Hpci Hid_nz HelectionTimeout Hlok Hlogp Htick HmsgsAA_ok Hout_term Hgh_out
    Hgh_unst' Hvoter
    $$ Hr Hlogger Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc Houtbox

/-- The log at the state `s` records, put back at that same state: for a read through
`ownRaftLog` (a `raftLog` method that keeps its state, a field load through
`ownRaftLog_struct`). The wand gives `ownRaftPhys` at `s` itself, so no
`ownRaftPhys_eq` is needed afterwards. -/
theorem ownRaftPhys_log_same (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhys (GF := GF) cfg r id s -∗
      ownRaftLog s.log s.logst ∗
      (ownRaftLog s.log s.logst -∗ ownRaftPhys cfg r id s) := by
  iintro H
  icases ownRaftPhys_log_at cfg r id s $$ H with ⟨Hlog, %Hgh, Hback⟩
  iframe Hlog
  iintro Hlog
  ihave H := Hback $$ %s.logst Hlog %Hgh
  iapply ownRaftPhys_eq cfg r id _ _ (by cases s; rfl) $$ H

/-- The ghost flag `unst` holds of the log (2026-10-10, `NGhost`), read out. -/
theorem ownRaftPhys_gh (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhys (GF := GF) cfg r id s -∗ ⌜LogGhOk s s.logst⌝ ∗ ownRaftPhys cfg r id s := by
  iintro H
  icases ownRaftPhys_log_at cfg r id s $$ H with ⟨Hlog, %Hgh, Hback⟩
  isplitr
  · ipureintro; exact Hgh
  ihave H := Hback $$ %s.logst Hlog %Hgh
  iapply ownRaftPhys_eq cfg r id _ _ (by cases s; rfl) $$ H

/-- `r.msgs`, append-only: a message `m'` appended joins the abstract outbox (at the
end, up to permutation -- see `Houtbox`) as whatever `msgAbs` says it contributes:
nothing for a type the model does not describe, else its abstraction, given
`m'.Entries ↦*□ ents`. -/
theorem ownRaftPhys_msgs (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhys (GF := GF) cfg r id s -∗
      ∃ sl ms, r.[raft, go!"msgs"] ↦ sl ∗ sl ↦* ms ∗
        ownSliceCap raftpb.Message sl (DFrac.own 1) ∗
        (∀ sl' m' a, r.[raft, go!"msgs"] ↦ sl' -∗ sl' ↦* (ms ++ [m']) -∗
           ownSliceCap raftpb.Message sl' (DFrac.own 1) -∗
           msgAbs m' a -∗
           ⌜OutTermOk s.prevote s.term m'⌝ -∗
           ownRaftPhys cfg r id { s with outbox := s.outbox ++ absList [a] }) := by
  iintro H
  iNamed_phys H
  icases raft_split_msgs r rv $$ Hr with ⟨Hf, Hback⟩
  iexists rv.msgs', msgs
  iframe Hf Hmsgs Hmsgs_cap
  iintro %sl' %m' %a Hf Hmsgs Hmsgs_cap #Ha %Hot
  have Hout_term' : ∀ m ∈ (msgs ++ [m']) ++ msgsAA, OutTermOk s.prevote s.term m := by
    intro m Hm
    simp only [List.mem_append, List.mem_singleton] at Hm
    rcases Hm with (Hm | rfl) | Hm
    · exact Hout_term m (List.mem_append_left _ Hm)
    · exact Hot
    · exact Hout_term m (List.mem_append_right _ Hm)
  ihave Hr := Hback $$ %sl' Hf
  iunfold outboxRel at Houtbox
  icases Houtbox with ⟨%as1, %as2, %Ho, #H1, #H2⟩
  ihave #Houtbox : outboxRel (GF := GF) (s.outbox ++ absList [a]) (msgs ++ [m']) msgsAA $$ []
  · unfold outboxRel
    iexists as1 ++ [a], as2
    isplitr
    · ipureintro
      simp only [absList, List.filterMap_append, List.append_assoc] at Ho ⊢
      refine (Ho.append_right _).trans ?_
      simp only [List.append_assoc]
      exact List.Perm.append_left _ List.perm_append_comm
    isplitr
    · iapply (BigSepL2.bigSepL2_snoc (Φ := fun _ m a => msgAbs (GF := GF) m a)).2
      iframe H1 Ha
    · iexact H2
  iapply ownRaftPhys_intro _ _ _ { s with outbox := s.outbox ++ absList [a] }
      { rv with msgs' := sl' } (msgs ++ [m']) msgsAA lok
    Hid Hterm Hvote Hlead Hstate Hstepfn Hprevote HpropForward HnoCCV HnoCheckQuorum HnoLearner
    HnoTransfer Hpci Hid_nz HelectionTimeout Hlok Hlogp Htick HmsgsAA_ok Hout_term'
    (by simp only [List.length_append, List.length_singleton]; omega) Hgh_unst Hvoter
    $$ Hr Hlogger Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc Houtbox

/-- `r.msgsAfterAppend`, likewise. -/
theorem ownRaftPhys_msgsAA (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhys (GF := GF) cfg r id s -∗
      ∃ sl ms, r.[raft, go!"msgsAfterAppend"] ↦ sl ∗ sl ↦* ms ∗
        ownSliceCap raftpb.Message sl (DFrac.own 1) ∗
        (∀ sl' m' a, r.[raft, go!"msgsAfterAppend"] ↦ sl' -∗
           sl' ↦* (ms ++ [m']) -∗
           ownSliceCap raftpb.Message sl' (DFrac.own 1) -∗
           msgAbs m' a -∗
           ⌜AAMsgOk id s.term m'⌝ -∗
           ⌜OutTermOk s.prevote s.term m'⌝ -∗
           ownRaftPhys cfg r id { s with outbox := s.outbox ++ absList [a] }) := by
  iintro H
  iNamed_phys H
  icases raft_split_msgsAA r rv $$ Hr with ⟨Hf, Hback⟩
  iexists rv.msgsAfterAppend', msgsAA
  iframe Hf HmsgsAA HmsgsAA_cap
  iintro %sl' %m' %a Hf HmsgsAA HmsgsAA_cap #Ha %Hok %Hot
  have Hout_term' : ∀ m ∈ msgs ++ (msgsAA ++ [m']), OutTermOk s.prevote s.term m := by
    intro m Hm
    simp only [List.mem_append, List.mem_singleton] at Hm
    rcases Hm with Hm | Hm | rfl
    · exact Hout_term m (List.mem_append_left _ Hm)
    · exact Hout_term m (List.mem_append_right _ Hm)
    · exact Hot
  have HmsgsAA_ok' : ∀ m ∈ msgsAA ++ [m'], AAMsgOk id s.term m := by
    intro m Hm
    rcases List.mem_append.1 Hm with Hm | Hm
    · exact HmsgsAA_ok m Hm
    · rw [List.mem_singleton.1 Hm]; exact Hok
  ihave Hr := Hback $$ %sl' Hf
  iunfold outboxRel at Houtbox
  icases Houtbox with ⟨%as1, %as2, %Ho, #H1, #H2⟩
  ihave #Houtbox : outboxRel (GF := GF) (s.outbox ++ absList [a]) msgs (msgsAA ++ [m']) $$ []
  · unfold outboxRel
    iexists as1, as2 ++ [a]
    isplitr
    · ipureintro
      simp only [absList, List.filterMap_append, List.append_assoc] at Ho ⊢
      simpa [List.append_assoc] using Ho.append_right (List.filterMap _root_.id [a])
    isplitr
    · iexact H1
    · iapply (BigSepL2.bigSepL2_snoc (Φ := fun _ m a => msgAbs (GF := GF) m a)).2
      iframe H2 Ha
  iapply ownRaftPhys_intro _ _ _ { s with outbox := s.outbox ++ absList [a] }
      { rv with msgsAfterAppend' := sl' } msgs (msgsAA ++ [m']) lok
    Hid Hterm Hvote Hlead Hstate Hstepfn Hprevote HpropForward HnoCCV HnoCheckQuorum HnoLearner
    HnoTransfer Hpci Hid_nz HelectionTimeout Hlok Hlogp Htick HmsgsAA_ok' Hout_term'
    (by simp only [List.length_append, List.length_singleton]; omega) Hgh_unst Hvoter
    $$ Hr Hlogger Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc Houtbox

/-- The `readOnly` object (2026-10-12: at `s.rd.ro`, and back at any record, which the state
then records). `reset` replaces it; `bcastHeartbeat` reads its context. -/
theorem ownRaftPhys_readOnly (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhys (GF := GF) cfg r id s -∗
      ∃ (ro : Loc),
        r.[raft, go!"readOnly"] ↦ ro ∗ ownReadOnly ro s.rd.ro ∗
        (∀ (ro' : Loc) (rr' : ReadOnly),
           r.[raft, go!"readOnly"] ↦ ro' -∗ ownReadOnly ro' rr' -∗
           ownRaftPhys cfg r id { s with rd := { s.rd with ro := rr' } }) := by
  iintro H
  iNamed_phys H
  iunfold ownRaftMisc at Hmisc
  iNamed Hmisc
  icases raft_split_readOnly r rv $$ Hr with ⟨Hf, Hback⟩
  iexists rv.readOnly'
  iframe Hf Hro_obj
  iintro %ro' %rr' Hf Hro_obj
  ihave Hr := Hback $$ %ro' Hf
  ihave Hmisc : ownRaftMisc (GF := GF) rv.readStates' ro' rv.pendingReadIndexMessages'
      { s.rd with ro := rr' } $$ [HreadStates HreadStates_cap Hro_obj Hpri Hpri_cap]
  · unfold ownRaftMisc
    simp only [named]
    iframe HreadStates HreadStates_cap Hro_obj Hpri Hpri_cap Hpri_ents
  reseal { s with rd := { s.rd with ro := rr' } }

/-- The tracker and the `readOnly` object together (2026-10-13): `stepLeader`'s
`r.readOnly.maybeAdvance(r.trk.Voters)` lends the tracker's voter map to the read-only
object's method. Back at any tracker value (same tally, progress map and values) and any
read-only record, which the state then records. -/
theorem ownRaftPhys_readOnly_trk (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhys (GF := GF) cfg r id s -∗
      ∃ (tv : tracker.ProgressTracker) (ro : Loc),
        r.[raft, go!"trk"] ↦ tv ∗
        ownTracker cfg tv ⟨s.votes, s.progress, s.prvals⟩ ∗
        r.[raft, go!"readOnly"] ↦ ro ∗ ownReadOnly ro s.rd.ro ∗
        (∀ (tv' : tracker.ProgressTracker) (ro' : Loc) (rr' : ReadOnly),
           r.[raft, go!"trk"] ↦ tv' -∗
           ownTracker cfg tv' ⟨s.votes, s.progress, s.prvals⟩ -∗
           r.[raft, go!"readOnly"] ↦ ro' -∗ ownReadOnly ro' rr' -∗
           ownRaftPhys cfg r id { s with rd := { s.rd with ro := rr' } }) := by
  iintro H
  iNamed_phys H
  iunfold ownRaftMisc at Hmisc
  iNamed Hmisc
  icases raft_split_trk_readOnly r rv $$ Hr with ⟨Hft, Hf, Hback⟩
  iexists rv.trk', rv.readOnly'
  iframe Hft Htrk Hf Hro_obj
  iintro %tv' %ro' %rr' Hft Htrk Hf Hro_obj
  ihave Hr := Hback $$ %tv' %ro' Hft Hf
  ihave Hmisc : ownRaftMisc (GF := GF) rv.readStates' ro' rv.pendingReadIndexMessages'
      { s.rd with ro := rr' } $$ [HreadStates HreadStates_cap Hro_obj Hpri Hpri_cap]
  · unfold ownRaftMisc
    simp only [named]
    iframe HreadStates HreadStates_cap Hro_obj Hpri Hpri_cap Hpri_ents
  iapply ownRaftPhys_intro cfg r id { s with rd := { s.rd with ro := rr' } }
      { rv with trk' := tv', readOnly' := ro' } msgs msgsAA lok
    Hid Hterm Hvote Hlead Hstate Hstepfn Hprevote HpropForward HnoCCV HnoCheckQuorum HnoLearner
    HnoTransfer Hpci Hid_nz HelectionTimeout Hlok Hlogp Htick HmsgsAA_ok Hout_term Hgh_out Hgh_unst Hvoter
    $$ Hr Hlogger Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc Houtbox

/-- The three read-index fields with what hangs off them (2026-10-12), back at any values
and any read state, which the state then records. -/
theorem ownRaftPhys_misc (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhys (GF := GF) cfg r id s -∗
      ∃ (rs : GoSlice) (ro : Loc) (pr : GoSlice),
        r.[raft, go!"readStates"] ↦ rs ∗ r.[raft, go!"readOnly"] ↦ ro ∗
        r.[raft, go!"pendingReadIndexMessages"] ↦ pr ∗
        ownRaftMisc rs ro pr s.rd ∗
        (∀ (rs' : GoSlice) (ro' : Loc) (pr' : GoSlice) (rd' : RdState),
           r.[raft, go!"readStates"] ↦ rs' -∗ r.[raft, go!"readOnly"] ↦ ro' -∗
           r.[raft, go!"pendingReadIndexMessages"] ↦ pr' -∗
           ownRaftMisc rs' ro' pr' rd' -∗
           ownRaftPhys cfg r id { s with rd := rd' }) := by
  iintro H
  iNamed_phys H
  icases raft_split_misc r rv $$ Hr with ⟨Hf1, Hf2, Hf3, Hback⟩
  iexists rv.readStates', rv.readOnly', rv.pendingReadIndexMessages'
  iframe Hf1 Hf2 Hf3 Hmisc
  iintro %rs' %ro' %pr' %rd' Hf1 Hf2 Hf3 Hmisc
  ihave Hr := Hback $$ %rs' %ro' %pr' Hf1 Hf2 Hf3
  reseal { s with rd := rd' }

/-- Rocq `own_raft_phys_view`: the struct open for `RawNode.Ready` (see
`raft_split_view`). Since 2026-10-13 with the `ReadState`s' slice (read-only, and its
capacity), and `Hclose` takes `readStates` back at any slice and any read state that
changes only the `ReadState`s (`acceptReady` sets the field to `nil`). -/
theorem ownRaftPhys_view (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhys (GF := GF) cfg r id s -∗
      iprop(∃ (rs sl1 sl2 : GoSlice) (ms1 ms2 : List raftpb.Message),
        "#Hf_id" ∷ r.[raft, go!"id"] ↦□ id ∗
        "Hf_Term" ∷ r.[raft, go!"Term"] ↦ s.term ∗
        "Hf_Vote" ∷ r.[raft, go!"Vote"] ↦ s.vote ∗
        "Hf_readStates" ∷ r.[raft, go!"readStates"] ↦ rs ∗
        "%Hrs" ∷ ⌜s.rd.states.length = sint.nat rs.len ∧ 0 ≤ sint.Z rs.len⌝ ∗
        "#HreadStates" ∷ rs ↦*□ s.rd.states ∗
        "HreadStates_cap" ∷ ownSliceCap ReadState rs (DFrac.own 1) ∗
        "Hf_raftLog" ∷ r.[raft, go!"raftLog"] ↦ s.log ∗
        "Hf_state" ∷ r.[raft, go!"state"] ↦ stateW64 s.role ∗
        "Hf_lead" ∷ r.[raft, go!"lead"] ↦ s.lead ∗
        "Hf_msgs" ∷ r.[raft, go!"msgs"] ↦ sl1 ∗ "Hmsgs" ∷ sl1 ↦* ms1 ∗
        "Hmsgs_cap" ∷ ownSliceCap raftpb.Message sl1 (DFrac.own 1) ∗
        "Hf_msgsAA" ∷ r.[raft, go!"msgsAfterAppend"] ↦ sl2 ∗ "HmsgsAA" ∷ sl2 ↦* ms2 ∗
        "HmsgsAA_cap" ∷ ownSliceCap raftpb.Message sl2 (DFrac.own 1) ∗
        "#Houtbox" ∷ outboxRel s.outbox ms1 ms2 ∗
        "%HmsgsAA_ok" ∷ ⌜∀ m ∈ ms2, AAMsgOk id s.term m⌝ ∗
        "%Hout_term" ∷ ⌜∀ m ∈ ms1 ++ ms2, OutTermOk s.prevote s.term m⌝ ∗
        "%Hgh_out" ∷ ⌜s.gh.outlb ≤ ms1.length + ms2.length⌝ ∗
        "%Hgh_unst" ∷ ⌜LogGhOk s s.logst⌝ ∗
        "Hlog" ∷ ownRaftLog s.log s.logst ∗
        "Hclose" ∷ (∀ (sl1' sl2' : GoSlice) (ms1' ms2' : List raftpb.Message) (o : List Msg)
                      (ls' : LogState) (g : NGhost) (rs' : GoSlice) (rd' : RdState),
            r.[raft, go!"Term"] ↦ s.term -∗
            r.[raft, go!"Vote"] ↦ s.vote -∗
            r.[raft, go!"readStates"] ↦ rs' -∗
            rs' ↦*□ rd'.states -∗ ownSliceCap ReadState rs' (DFrac.own 1) -∗
            ⌜rd'.ro = s.rd.ro ∧ rd'.pend = s.rd.pend⌝ -∗
            r.[raft, go!"raftLog"] ↦ s.log -∗
            r.[raft, go!"state"] ↦ stateW64 s.role -∗
            r.[raft, go!"lead"] ↦ s.lead -∗
            r.[raft, go!"msgs"] ↦ sl1' -∗ sl1' ↦* ms1' -∗
            ownSliceCap raftpb.Message sl1' (DFrac.own 1) -∗
            r.[raft, go!"msgsAfterAppend"] ↦ sl2' -∗ sl2' ↦* ms2' -∗
            ownSliceCap raftpb.Message sl2' (DFrac.own 1) -∗
            outboxRel o ms1' ms2' -∗
            ⌜∀ m ∈ ms2', AAMsgOk id s.term m⌝ -∗
            ⌜∀ m ∈ ms1' ++ ms2', OutTermOk s.prevote s.term m⌝ -∗
            ⌜g.outlb ≤ ms1'.length + ms2'.length⌝ -∗
            ⌜g.unst = true → nextUnstable ls' ≠ [] ∨ ls'.snap ≠ none⌝ -∗
            ownRaftLog s.log ls' -∗
            ownRaftPhys cfg r id { s with outbox := o, logst := ls', gh := g, rd := rd' })) := by
  iintro H
  iNamed_phys H
  iunfold ownRaftMisc at Hmisc
  iNamed Hmisc
  ihave #HreadStates := HreadStates
  ihave %Hrl := ownSlice_len _ _ _ $$ HreadStates
  icases raft_split_view r rv $$ Hr with
    ⟨Hfid, HfTerm, HfVote, Hfrs, Hflog, Hfst, Hfm, Hfma, Hfld, Hback⟩
  ihave #Hfid : r.[raft, go!"id"] ↦□ id $$ [Hfid]
  · rw [← Hid]; iexact Hfid
  ihave HfTerm : r.[raft, go!"Term"] ↦ s.term $$ [HfTerm]
  · rw [← Hterm]; iexact HfTerm
  ihave HfVote : r.[raft, go!"Vote"] ↦ s.vote $$ [HfVote]
  · rw [← Hvote]; iexact HfVote
  ihave Hflog : r.[raft, go!"raftLog"] ↦ s.log $$ [Hflog]
  · rw [← Hlogp]; iexact Hflog
  ihave Hfst : r.[raft, go!"state"] ↦ stateW64 s.role $$ [Hfst]
  · rw [← Hstate]; iexact Hfst
  ihave Hfld : r.[raft, go!"lead"] ↦ s.lead $$ [Hfld]
  · rw [← Hlead]; iexact Hfld
  ihave Hlog : ownRaftLog (GF := GF) s.log s.logst $$ [Hlog]
  · rw [← Hlogp]; iexact Hlog
  iexists rv.readStates', rv.msgs', rv.msgsAfterAppend', msgs, msgsAA
  simp only [named]
  iframe Hfid HfTerm HfVote Hfrs Hflog Hfst Hfld Hfm Hfma Hmsgs Hmsgs_cap HmsgsAA
    HmsgsAA_cap Houtbox Hlog HreadStates HreadStates_cap
  isplitr
  · ipureintro; exact Hrl
  isplitr
  · ipureintro; exact HmsgsAA_ok
  isplitr
  · ipureintro; exact Hout_term
  isplitr
  · ipureintro; exact Hgh_out
  isplitr
  · ipureintro; exact Hgh_unst
  iintro %sl1' %sl2' %ms1' %ms2' %o %ls' %g %rs' %rd' HfTerm HfVote Hfrs Hrs' Hrs'_cap
    %Hrd' Hflog Hfst Hfld Hfm Hmsgs
    Hmsgs_cap Hfma HmsgsAA HmsgsAA_cap #Houtbox' %HmsgsAA_ok' %Hout_term' %Hg1 %Hg2 Hlog
  ihave Hmisc : ownRaftMisc (GF := GF) rs' rv.readOnly' rv.pendingReadIndexMessages' rd'
      $$ [Hrs' Hrs'_cap Hro_obj Hpri Hpri_cap]
  · unfold ownRaftMisc
    simp only [named]
    rw [Hrd'.1, Hrd'.2]
    iframe Hrs' Hrs'_cap Hro_obj Hpri Hpri_cap Hpri_ents
  ihave HfTerm : r.[raft, go!"Term"] ↦ rv.Term' $$ [HfTerm]
  · rw [Hterm]; iexact HfTerm
  ihave HfVote : r.[raft, go!"Vote"] ↦ rv.Vote' $$ [HfVote]
  · rw [Hvote]; iexact HfVote
  ihave Hflog : r.[raft, go!"raftLog"] ↦ rv.raftLog' $$ [Hflog]
  · rw [Hlogp]; iexact Hflog
  ihave Hfst : r.[raft, go!"state"] ↦ rv.state' $$ [Hfst]
  · rw [Hstate]; iexact Hfst
  ihave Hfld : r.[raft, go!"lead"] ↦ rv.lead' $$ [Hfld]
  · rw [Hlead]; iexact Hfld
  ihave Hlog : ownRaftLog (GF := GF) rv.raftLog' ls' $$ [Hlog]
  · rw [Hlogp]; iexact Hlog
  ihave Hr := Hback $$ %sl1' %sl2' %rs' HfTerm HfVote Hfrs Hflog Hfst Hfm Hfma Hfld
  iapply ownRaftPhys_intro _ _ _ { s with outbox := o, logst := ls', gh := g, rd := rd' }
      { rv with msgs' := sl1', msgsAfterAppend' := sl2', readStates' := rs' } ms1' ms2' lok
    Hid Hterm Hvote Hlead Hstate Hstepfn Hprevote HpropForward HnoCCV HnoCheckQuorum HnoLearner
    HnoTransfer Hpci Hid_nz HelectionTimeout Hlok Hlogp Htick HmsgsAA_ok' Hout_term' Hg1 Hg2 Hvoter
    $$ Hr Hlogger Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc Houtbox'

end proof

/-! ### Reconfiguration

The one accessor that changes `ownRaftPhys`'s `cfg` index: the tracker comes out at
the old configuration and goes back at a new one, with a new progress map
(`NState.progress`). Only `ownTracker` mentions `cfg`, so nothing else is
re-established. `switchToConfig` is the one user (for `newRaft`'s move from the empty
configuration to the persisted one). -/
section reconfig
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem ownRaftPhys_reconfig (cfg0 cfg : GSet w64) (r : Loc) (id : w64) (s : NState)
    (Hv : s.role ≠ .follower → id ∈ cfg) :
    ⊢ ownRaftPhys (GF := GF) cfg0 r id s -∗
      ∃ tv, r.[raft, go!"trk"] ↦ tv ∗
        ownTracker cfg0 tv ⟨s.votes, s.progress, s.prvals⟩ ∗
        (∀ tv' prs' pvs', r.[raft, go!"trk"] ↦ tv' -∗
           ownTracker cfg tv' ⟨s.votes, prs', pvs'⟩ -∗
           ownRaftPhys cfg r id { s with progress := prs', prvals := pvs' }) := by
  iintro H
  iNamed_phys H
  icases raft_split_trk r rv $$ Hr with ⟨Hf, Hback⟩
  iexists rv.trk'
  iframe Hf Htrk
  iintro %tv' %prs' %pvs' Hf Htrk
  ihave Hr := Hback $$ %tv' Hf
  iapply ownRaftPhys_intro cfg r id { s with progress := prs', prvals := pvs' }
      { rv with trk' := tv' } msgs msgsAA lok
    Hid Hterm Hvote Hlead Hstate Hstepfn Hprevote HpropForward HnoCCV HnoCheckQuorum HnoLearner
    HnoTransfer Hpci Hid_nz HelectionTimeout Hlok Hlogp Htick HmsgsAA_ok Hout_term Hgh_out Hgh_unst Hv
    $$ Hr Hlogger Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc Houtbox

/-- The tracker replaced while the log is in use (2026-10-02): `restore` stores a fresh
tracker into `r.trk`, loads it back, calls `r.raftLog.lastIndex()` and only then hands
the new tracker's (empty) voter map to `confchange.Restore` -- so between the store and
that call the struct cannot be re-sealed without losing which tracker value it holds.
This accessor hands out the tracker field and the `raftLog` field (read-only: its value
is `s.log`) together with the log, and takes them back at any tracker -- a new
configuration `cfg`, tally, progress map and values -- and any log state. -/
theorem ownRaftPhys_retrack (cfg0 cfg : GSet w64) (r : Loc) (id : w64) (s : NState)
    (Hv : s.role ≠ .follower → id ∈ cfg) :
    ⊢ ownRaftPhys (GF := GF) cfg0 r id s -∗
      ∃ tv, r.[raft, go!"trk"] ↦ tv ∗
        ownTracker cfg0 tv ⟨s.votes, s.progress, s.prvals⟩ ∗
        r.[raft, go!"raftLog"] ↦ s.log ∗
        ownRaftLog s.log s.logst ∗
        (∀ tv' votes' prs' pvs' ls',
           r.[raft, go!"raftLog"] ↦ s.log -∗
           r.[raft, go!"trk"] ↦ tv' -∗
           ownTracker cfg tv' ⟨votes', prs', pvs'⟩ -∗
           ownRaftLog s.log ls' -∗ ⌜LogGhOk s ls'⌝ -∗
           ownRaftPhys cfg r id
             { s with votes := votes', progress := prs', prvals := pvs', logst := ls' }) := by
  iintro H
  iNamed_phys H
  icases raft_split_raftLog_trk r rv $$ Hr with ⟨Hlf, Hf, Hback⟩
  iexists rv.trk'
  iframe Hf Htrk
  ihave Hlf : r.[raft, go!"raftLog"] ↦ s.log $$ [Hlf]
  · rw [← Hlogp]; iexact Hlf
  ihave Hlog : ownRaftLog (GF := GF) s.log s.logst $$ [Hlog]
  · rw [← Hlogp]; iexact Hlog
  iframe Hlf Hlog
  iintro %tv' %votes' %prs' %pvs' %ls' Hlf Hf Htrk Hlog %Hgh_unst'
  ihave Hlf : r.[raft, go!"raftLog"] ↦ rv.raftLog' $$ [Hlf]
  · rw [Hlogp]; iexact Hlf
  ihave Hlog : ownRaftLog (GF := GF) rv.raftLog' ls' $$ [Hlog]
  · rw [Hlogp]; iexact Hlog
  ihave Hr := Hback $$ %tv' Hlf Hf
  iapply ownRaftPhys_intro cfg r id
      { s with votes := votes', progress := prs', prvals := pvs', logst := ls' }
      { rv with trk' := tv' } msgs msgsAA lok
    Hid Hterm Hvote Hlead Hstate Hstepfn Hprevote HpropForward HnoCCV HnoCheckQuorum HnoLearner
    HnoTransfer Hpci Hid_nz HelectionTimeout Hlok Hlogp Htick HmsgsAA_ok Hout_term Hgh_out
    Hgh_unst' Hv
    $$ Hr Hlogger Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc Houtbox

end reconfig

/-! ### `ownRaftPhysC`: the equivalence with `ownRaftPhys` and the accessors (2026-10-13) -/

set_option hygiene false in
/-- `iNamed_phys` for `ownRaftPhysC`. In this file only. -/
local macro "iNamed_physC " H:ident : tactic =>
  `(tactic| (ihave $H:ident := ownRaftPhysC_open _ _ _ _ $$ $H:ident;
             iunfold ownRaftPhysG at $H:ident;
             icases $H:ident with ⟨%rv, %msgs, %msgsAA, %lok, $H:ident⟩;
             iNamed $H:ident))

set_option hygiene false in
/-- `reseal` for `ownRaftPhysC`, at the configuration `c` and the state `s'`. -/
local macro "resealC " c:term:max s:term:max : tactic =>
  `(tactic| (iapply ownRaftPhysC_intro $c _ _ $s _ msgs msgsAA lok
                (by phys_pure) (by phys_pure) (by phys_pure) (by phys_pure) (by phys_pure)
                (by phys_pure) (by phys_pure) (by phys_pure) (by phys_pure) (by phys_pure)
                (by phys_pure) (by phys_pure) (by phys_pure) (by phys_pure) (by phys_pure)
                (by phys_pure) (by phys_pure) (by phys_pure) (by phys_pure) (by phys_pure)
                (by phys_pure) (by phys_pure) (by phys_pure)
                $$ Hr Hlogger Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc Houtbox))

section physC
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `ownRaftPhys` is `ownRaftPhysC` at its simple configuration: the voters `cfg`, the
learners the other tracked ids. -/
theorem ownRaftPhys_toC (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhys (GF := GF) cfg r id s -∗
      ownRaftPhysC (CfgM.simple cfg (domSet s.progress \ cfg)) r id s := by
  iintro H
  iNamed_phys H
  ihave Htrk := ownTracker_toC _ _ _ $$ Htrk
  iapply ownRaftPhysC_intro (CfgM.simple cfg (domSet s.progress \ cfg)) r id s rv msgs msgsAA lok
    Hid Hterm Hvote Hlead Hstate Hstepfn Hprevote HpropForward HnoCCV HnoCheckQuorum HnoLearner
    HnoTransfer Hpci Hid_nz HelectionTimeout Hlok Hlogp Htick HmsgsAA_ok Hout_term Hgh_out Hgh_unst
    (fun h => by rw [CfgM.voters_simple]; exact Hvoter h)
    $$ Hr Hlogger Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc Houtbox

/-- Back: at a non-joint configuration `ownRaftPhysC` is `ownRaftPhys` at the incoming
voters, the learners the tracked ids outside them. -/
theorem ownRaftPhysC_toPhys (c : CfgM) (r : Loc) (id : w64) (s : NState)
    (ho : c.outgoing = ∅) :
    ⊢ ownRaftPhysC (GF := GF) c r id s -∗
      ownRaftPhys c.incoming r id s ∗ ⌜c.learners = domSet s.progress \ c.incoming⌝ := by
  iintro H
  iNamed_physC H
  icases ownTrackerC_toSimple _ _ _ ho $$ Htrk with ⟨Htrk, %Hl⟩
  isplitl
  · iapply ownRaftPhys_intro c.incoming r id s rv msgs msgsAA lok
      Hid Hterm Hvote Hlead Hstate Hstepfn Hprevote HpropForward HnoCCV HnoCheckQuorum HnoLearner
      HnoTransfer Hpci Hid_nz HelectionTimeout Hlok Hlogp Htick HmsgsAA_ok Hout_term Hgh_out
      Hgh_unst (fun h => by rw [← CfgM.voters_of_out ho]; exact Hvoter h)
      $$ Hr Hlogger Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc Houtbox
  · ipureintro; exact Hl

/-- `ownRaftPhysC_toPhys` at `CfgM.simple`. -/
theorem ownRaftPhysC_simple_toPhys (cfg lrn : GSet w64) (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhysC (GF := GF) (CfgM.simple cfg lrn) r id s -∗
      ownRaftPhys cfg r id s ∗ ⌜lrn = domSet s.progress \ cfg⌝ :=
  ownRaftPhysC_toPhys (CfgM.simple cfg lrn) r id s rfl

/-- The tracker, as the tracker's own specs take it (`ownRaftPhys_tracker` at `c`): given
back at any tracker value and tally, at the same progress map and `Progress` values. -/
theorem ownRaftPhysC_tracker (c : CfgM) (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhysC (GF := GF) c r id s -∗
      ∃ tv, r.[raft, go!"trk"] ↦ tv ∗
        ownTrackerC c tv ⟨s.votes, s.progress, s.prvals⟩ ∗
        (∀ tv' votes', r.[raft, go!"trk"] ↦ tv' -∗
           ownTrackerC c tv' ⟨votes', s.progress, s.prvals⟩ -∗
           ownRaftPhysC c r id { s with votes := votes' }) := by
  iintro H
  iNamed_physC H
  icases raft_split_trk r rv $$ Hr with ⟨Hf, Hback⟩
  iexists rv.trk'
  iframe Hf Htrk
  iintro %tv' %votes' Hf Htrk
  ihave Hr := Hback $$ %tv' Hf
  resealC c { s with votes := votes' }

/-- The tracker, given back with new `Progress` values (`ownRaftPhys_tracker_prvals` at
`c`). -/
theorem ownRaftPhysC_tracker_prvals (c : CfgM) (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhysC (GF := GF) c r id s -∗
      ∃ tv, r.[raft, go!"trk"] ↦ tv ∗
        ownTrackerC c tv ⟨s.votes, s.progress, s.prvals⟩ ∗
        (∀ tv' pvs', r.[raft, go!"trk"] ↦ tv' -∗
           ownTrackerC c tv' ⟨s.votes, s.progress, pvs'⟩ -∗
           ownRaftPhysC c r id { s with prvals := pvs' }) := by
  iintro H
  iNamed_physC H
  icases raft_split_trk r rv $$ Hr with ⟨Hf, Hback⟩
  iexists rv.trk'
  iframe Hf Htrk
  iintro %tv' %pvs' Hf Htrk
  ihave Hr := Hback $$ %tv' Hf
  resealC c { s with prvals := pvs' }

/-- A new configuration (`ownRaftPhys_reconfig` at any configurations): the tracker at `c0`
handed out, taken back at `c` with a new progress map and values -- what `switchToConfig`
does at a joint configuration. The voter premise is for the new configuration. -/
theorem ownRaftPhysC_reconfig (c0 c : CfgM) (r : Loc) (id : w64) (s : NState)
    (Hv : s.role ≠ .follower → id ∈ c.voters) :
    ⊢ ownRaftPhysC (GF := GF) c0 r id s -∗
      ∃ tv, r.[raft, go!"trk"] ↦ tv ∗
        ownTrackerC c0 tv ⟨s.votes, s.progress, s.prvals⟩ ∗
        (∀ tv' prs' pvs', r.[raft, go!"trk"] ↦ tv' -∗
           ownTrackerC c tv' ⟨s.votes, prs', pvs'⟩ -∗
           ownRaftPhysC c r id { s with progress := prs', prvals := pvs' }) := by
  iintro H
  iNamed_physC H
  icases raft_split_trk r rv $$ Hr with ⟨Hf, Hback⟩
  iexists rv.trk'
  iframe Hf Htrk
  iintro %tv' %prs' %pvs' Hf Htrk
  ihave Hr := Hback $$ %tv' Hf
  iapply ownRaftPhysC_intro c r id { s with progress := prs', prvals := pvs' }
      { rv with trk' := tv' } msgs msgsAA lok
    Hid Hterm Hvote Hlead Hstate Hstepfn Hprevote HpropForward HnoCCV HnoCheckQuorum HnoLearner
    HnoTransfer Hpci Hid_nz HelectionTimeout Hlok Hlogp Htick HmsgsAA_ok Hout_term Hgh_out Hgh_unst Hv
    $$ Hr Hlogger Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc Houtbox

/-- Only a voter (of either half) is out of the follower role. -/
theorem ownRaftPhysC_voter (c : CfgM) (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhysC (GF := GF) c r id s -∗
      ⌜s.role ≠ .follower → id ∈ c.voters⌝ ∗ ownRaftPhysC c r id s := by
  iintro H
  iNamed_physC H
  isplitr
  · ipureintro; exact Hvoter
  resealC c s

/-- The progress map tracks exactly the configuration's ids, at most `2^62` of them. -/
theorem ownRaftPhysC_progress_dom (c : CfgM) (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhysC (GF := GF) c r id s -∗
      ⌜domSet s.progress = c.ids ∧ (GMap.size s.progress : Int) ≤ 2 ^ 62⌝ ∗
      ownRaftPhysC c r id s := by
  iintro H
  iNamed_physC H
  icases ownTrackerC_pure _ _ _ $$ Htrk with ⟨%Hp, Htrk⟩
  isplitr
  · ipureintro; exact ⟨Hp.2.1, Hp.2.2.2.1⟩
  resealC c s

end physC

/-! ### `ownRaftPhysC`: the field lemmas and accessors (2026-10-13, reconfiguration stage A2)

`ownRaftPhys`'s interface restated on `ownRaftPhysC c` (the same statements with `ownRaftPhysC c`
for `ownRaftPhys cfg`, `ownTrackerC c` for `ownTracker cfg`, `c.voters` for `cfg` in the voter
premise of `raft.wp_store_stateC`); the names are `ownRaftPhys`'s with a `C`: `raft.wp_load_TermC`,
`ownRaftPhysC_log_at`, ... The proofs are `ownRaftPhys`'s (generated from them by
`iNamed_physC`/`resealC` for `iNamed_phys`/`reseal`: a field access never reads the tracker's
configuration), so the old lemmas keep their own proofs rather than being derived through
`ownRaftPhys_toC` (a derivation per lemma would be longer than the proof). -/

section physCfields
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

variable (c : CfgM)

/-- The leader-transfer target is never the node itself (2026-10-13): read out without
consuming anything. -/
theorem ownRaftPhysC_lt_ne (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhysC (GF := GF) c r id s -∗ ⌜s.lt ≠ id⌝ ∗ ownRaftPhysC c r id s := by
  iintro H
  iNamed_physC H
  isplitr
  · ipureintro; exact HnoTransfer.2
  resealC c s

/-- Changing only the outbox, up to permutation. -/
theorem ownRaftPhysC_outbox (r : Loc) (id : w64) (s : NState) (o : List Msg) :
    o ≡ₚ s.outbox →
    ⊢ ownRaftPhysC (GF := GF) c r id s -∗ ownRaftPhysC c r id { s with outbox := o } := by
  intro Ho
  iintro H
  iNamed_physC H
  ihave #Houtbox' := outboxRel_perm _ o _ _ Ho $$ Houtbox
  iapply ownRaftPhysC_intro c _ _ { s with outbox := o } _ msgs msgsAA lok
    Hid Hterm Hvote Hlead Hstate Hstepfn Hprevote HpropForward HnoCCV HnoCheckQuorum HnoLearner
    HnoTransfer Hpci Hid_nz HelectionTimeout Hlok Hlogp Htick HmsgsAA_ok Hout_term Hgh_out Hgh_unst Hvoter
    $$ Hr Hlogger Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc Houtbox'

/-- Sending nothing, in both directions: an exit that sends nothing proves a
postcondition stated at `sendMsgs s ms` with `ms = []`, and a `send` of a message the
model does not see comes back at `sendMsgs s []`. -/
theorem ownRaftPhysC_send_nil (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhysC (GF := GF) c r id s -∗ ownRaftPhysC c r id (sendMsgs s []) := by
  have H : sendMsgs s [] = s := by cases s; simp [sendMsgs]
  rw [H]; iintro H; iexact H

theorem ownRaftPhysC_unsend (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhysC (GF := GF) c r id (sendMsgs s []) -∗ ownRaftPhysC c r id s := by
  have H : sendMsgs s [] = s := by cases s; simp [sendMsgs]
  rw [H]; iintro H; iexact H

theorem raft.wp_load_idC (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhysC (GF := GF) c r id s }}
      (App (Val (GoInstruction (GoLoad go.uint64))) (Val #(r.[raft, go!"id"])))
    {{ RET #id; ownRaftPhysC c r id s }} := by
  iintro %Φ H HΦ
  iNamed_physC H
  ihave #Hfid := raftOwn_id _ _ $$ Hr
  wp_apply wp_load_pers _ rv.id' $$ Hfid
  rw [Hid]; iapply HΦ; resealC c s

theorem raft.wp_load_TermC (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhysC (GF := GF) c r id s }}
      (App (Val (GoInstruction (GoLoad go.uint64))) (Val #(r.[raft, go!"Term"])))
    {{ RET #s.term; ownRaftPhysC c r id s }} := by
  iintro %Φ H HΦ
  iNamed_physC H
  wp_apply wp_load_access _ rv.Term' _ (raftOwn_access_load_Term _ _) $$ Hr as Hr
  rw [Hterm]; iapply HΦ; resealC c s

theorem raft.wp_load_VoteC (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhysC (GF := GF) c r id s }}
      (App (Val (GoInstruction (GoLoad go.uint64))) (Val #(r.[raft, go!"Vote"])))
    {{ RET #s.vote; ownRaftPhysC c r id s }} := by
  iintro %Φ H HΦ
  iNamed_physC H
  wp_apply wp_load_access _ rv.Vote' _ (raftOwn_access_load_Vote _ _) $$ Hr as Hr
  rw [Hvote]; iapply HΦ; resealC c s

theorem raft.wp_load_leadC (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhysC (GF := GF) c r id s }}
      (App (Val (GoInstruction (GoLoad go.uint64))) (Val #(r.[raft, go!"lead"])))
    {{ RET #s.lead; ownRaftPhysC c r id s }} := by
  iintro %Φ H HΦ
  iNamed_physC H
  wp_apply wp_load_access _ rv.lead' _ (raftOwn_access_load_lead _ _) $$ Hr as Hr
  rw [Hlead]; iapply HΦ; resealC c s

theorem raft.wp_load_stateC (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhysC (GF := GF) c r id s }}
      (App (Val (GoInstruction (GoLoad StateType.ty))) (Val #(r.[raft, go!"state"])))
    {{ RET #(stateW64 s.role); ownRaftPhysC c r id s }} := by
  iintro %Φ H HΦ
  iNamed_physC H
  wp_apply wp_load_access _ rv.state' _ (raftOwn_access_load_state _ _) $$ Hr as Hr
  rw [Hstate]; iapply HΦ; resealC c s

theorem raft.wp_load_stepC (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhysC (GF := GF) c r id s }}
      (App (Val (GoInstruction (GoLoad stepFunc.ty))) (Val #(r.[raft, go!"step"])))
    {{ RET #s.stepfn; ownRaftPhysC c r id s }} := by
  iintro %Φ H HΦ
  iNamed_physC H
  wp_apply wp_load_access _ rv.step' _ (raftOwn_access_load_step _ _) $$ Hr as Hr
  rw [Hstepfn]; iapply HΦ; resealC c s

/-- The log's *location*. Its contents are `ownRaftPhys_log_at`'s. -/
theorem raft.wp_load_raftLogC (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhysC (GF := GF) c r id s }}
      (App (Val (GoInstruction (GoLoad (go.GoType.PointerType raftLog.ty))))
        (Val #(r.[raft, go!"raftLog"])))
    {{ RET #s.log; ownRaftPhysC c r id s }} := by
  iintro %Φ H HΦ
  iNamed_physC H
  wp_apply wp_load_access _ rv.raftLog' _ (raftOwn_access_load_raftLog _ _) $$ Hr as Hr
  rw [show (#rv.raftLog' : val) = #s.log by rw [Hlogp]]; iapply HΦ; resealC c s

theorem raft.wp_load_loggerC (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhysC (GF := GF) c r id s }}
      (App (Val (GoInstruction (GoLoad Logger.ty))) (Val #(r.[raft, go!"logger"])))
    {{ (lok : GoInterfaceOk), RET #(interface.ok lok);
        ownRaftPhysC c r id s ∗ isLogger lok }} := by
  iintro %Φ H HΦ
  iNamed_physC H
  ihave #Hflg := raftOwn_logger _ _ $$ Hr
  wp_apply wp_load_pers _ rv.logger' $$ Hflg
  rw [Hlok]; iapply HΦ
  isplitl
  · resealC c s
  · iexact Hlogger

/-- The two fields shared with other goroutines (2026-10-10, `raftOwn`): `node.go`'s
`Tick` reads `r.logger` and `r.id` while `run` owns the struct. -/
theorem ownRaftPhysC_shared (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhysC (GF := GF) c r id s -∗
      ∃ lok : GoInterfaceOk, r.[raft, go!"id"] ↦□ id ∗
        r.[raft, go!"logger"] ↦□ (interface.ok lok : GoInterface) ∗ isLogger lok ∗
        ownRaftPhysC c r id s := by
  iintro H
  iNamed_physC H
  ihave #Hfid := raftOwn_id _ _ $$ Hr
  ihave #Hflg := raftOwn_logger _ _ $$ Hr
  ihave #Hfid' : r.[raft, go!"id"] ↦□ id $$ [Hfid]
  · rw [← Hid]; iexact Hfid
  ihave #Hflg' : r.[raft, go!"logger"] ↦□ (interface.ok lok : GoInterface) $$ [Hflg]
  · rw [← Hlok]; iexact Hflg
  iexists lok
  iframe Hfid' Hflg' Hlogger
  resealC c s

theorem raft.wp_load_checkQuorumC (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhysC (GF := GF) c r id s }}
      (App (Val (GoInstruction (GoLoad go.bool))) (Val #(r.[raft, go!"checkQuorum"])))
    {{ RET #false; ownRaftPhysC c r id s }} := by
  iintro %Φ H HΦ
  iNamed_physC H
  wp_apply wp_load_access _ rv.checkQuorum' _ (raftOwn_access_load_checkQuorum _ _) $$ Hr as Hr
  rw [HnoCheckQuorum]; iapply HΦ; resealC c s

theorem raft.wp_load_preVoteC (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhysC (GF := GF) c r id s }}
      (App (Val (GoInstruction (GoLoad go.bool))) (Val #(r.[raft, go!"preVote"])))
    {{ RET #s.prevote; ownRaftPhysC c r id s }} := by
  iintro %Φ H HΦ
  iNamed_physC H
  wp_apply wp_load_access _ rv.preVote' _ (raftOwn_access_load_preVote _ _) $$ Hr as Hr
  rw [Hprevote]; iapply HΦ; resealC c s

theorem raft.wp_load_disableProposalForwardingC (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhysC (GF := GF) c r id s }}
      (App (Val (GoInstruction (GoLoad go.bool)))
        (Val #(r.[raft, go!"disableProposalForwarding"])))
    {{ RET #false; ownRaftPhysC c r id s }} := by
  iintro %Φ H HΦ
  iNamed_physC H
  wp_apply wp_load_access _ rv.disableProposalForwarding' _ (raftOwn_access_load_disableProposalForwarding _ _) $$ Hr as Hr
  rw [HpropForward]; iapply HΦ; resealC c s

/-- `false` (2026-10-13): `ownRaftPhysC`'s scope conjunct. -/
theorem raft.wp_load_disableConfChangeValidationC (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhysC (GF := GF) c r id s }}
      (App (Val (GoInstruction (GoLoad go.bool)))
        (Val #(r.[raft, go!"disableConfChangeValidation"])))
    {{ RET #false; ownRaftPhysC c r id s }} := by
  iintro %Φ H HΦ
  iNamed_physC H
  wp_apply wp_load_access _ rv.disableConfChangeValidation' _ (raftOwn_access_load_disableConfChangeValidation _ _) $$ Hr as Hr
  rw [HnoCCV]; iapply HΦ; resealC c s

theorem raft.wp_load_isLearnerC (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhysC (GF := GF) c r id s }}
      (App (Val (GoInstruction (GoLoad go.bool))) (Val #(r.[raft, go!"isLearner"])))
    {{ RET #s.isLearner; ownRaftPhysC c r id s }} := by
  iintro %Φ H HΦ
  iNamed_physC H
  wp_apply wp_load_access _ rv.isLearner' _ (raftOwn_access_load_isLearner _ _) $$ Hr as Hr
  rw [HnoLearner]; iapply HΦ; resealC c s

theorem raft.wp_load_leadTransfereeC (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhysC (GF := GF) c r id s }}
      (App (Val (GoInstruction (GoLoad go.uint64))) (Val #(r.[raft, go!"leadTransferee"])))
    {{ RET #s.lt; ownRaftPhysC c r id s }} := by
  iintro %Φ H HΦ
  iNamed_physC H
  wp_apply wp_load_access _ rv.leadTransferee' _ (raftOwn_access_load_leadTransferee _ _) $$ Hr as Hr
  rw [HnoTransfer.1]; iapply HΦ; resealC c s

theorem raft.wp_load_electionTimeoutC (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhysC (GF := GF) c r id s }}
      (App (Val (GoInstruction (GoLoad go.int))) (Val #(r.[raft, go!"electionTimeout"])))
    {{ (v : w64), RET #v; ownRaftPhysC c r id s ∗ ⌜0 < sint.Z v⌝ }} := by
  iintro %Φ H HΦ
  iNamed_physC H
  wp_apply wp_load_access _ rv.electionTimeout' _ (raftOwn_access_load_electionTimeout _ _) $$ Hr as Hr
  iapply HΦ
  isplitl
  · resealC c s
  · ipureintro; exact HelectionTimeout

theorem raft.wp_load_electionElapsedC (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhysC (GF := GF) c r id s }}
      (App (Val (GoInstruction (GoLoad go.int))) (Val #(r.[raft, go!"electionElapsed"])))
    {{ (v : w64), RET #v; ownRaftPhysC c r id s }} := by
  iintro %Φ H HΦ
  iNamed_physC H
  wp_apply wp_load_access _ rv.electionElapsed' _ (raftOwn_access_load_electionElapsed _ _) $$ Hr as Hr
  iapply HΦ; resealC c s

theorem raft.wp_load_heartbeatElapsedC (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhysC (GF := GF) c r id s }}
      (App (Val (GoInstruction (GoLoad go.int))) (Val #(r.[raft, go!"heartbeatElapsed"])))
    {{ (v : w64), RET #v; ownRaftPhysC c r id s }} := by
  iintro %Φ H HΦ
  iNamed_physC H
  wp_apply wp_load_access _ rv.heartbeatElapsed' _ (raftOwn_access_load_heartbeatElapsed _ _) $$ Hr as Hr
  iapply HΦ; resealC c s

theorem raft.wp_load_heartbeatTimeoutC (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhysC (GF := GF) c r id s }}
      (App (Val (GoInstruction (GoLoad go.int))) (Val #(r.[raft, go!"heartbeatTimeout"])))
    {{ (v : w64), RET #v; ownRaftPhysC c r id s }} := by
  iintro %Φ H HΦ
  iNamed_physC H
  wp_apply wp_load_access _ rv.heartbeatTimeout' _ (raftOwn_access_load_heartbeatTimeout _ _) $$ Hr as Hr
  iapply HΦ; resealC c s

theorem raft.wp_load_randomizedElectionTimeoutC (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhysC (GF := GF) c r id s }}
      (App (Val (GoInstruction (GoLoad go.int)))
        (Val #(r.[raft, go!"randomizedElectionTimeout"])))
    {{ (v : w64), RET #v; ownRaftPhysC c r id s }} := by
  iintro %Φ H HΦ
  iNamed_physC H
  wp_apply wp_load_access _ rv.randomizedElectionTimeout' _ (raftOwn_access_load_randomizedElectionTimeout _ _) $$ Hr as Hr
  iapply HΦ; resealC c s

theorem raft.wp_load_pendingConfIndexC (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhysC (GF := GF) c r id s }}
      (App (Val (GoInstruction (GoLoad go.uint64))) (Val #(r.[raft, go!"pendingConfIndex"])))
    {{ RET #s.pci; ownRaftPhysC c r id s }} := by
  iintro %Φ H HΦ
  iNamed_physC H
  wp_apply wp_load_access _ rv.pendingConfIndex' _ (raftOwn_access_load_pendingConfIndex _ _) $$ Hr as Hr
  rw [Hpci]; iapply HΦ; resealC c s

theorem raft.wp_load_uncommittedSizeC (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhysC (GF := GF) c r id s }}
      (App (Val (GoInstruction (GoLoad entryPayloadSize.ty)))
        (Val #(r.[raft, go!"uncommittedSize"])))
    {{ (v : entryPayloadSize), RET #v; ownRaftPhysC c r id s }} := by
  iintro %Φ H HΦ
  iNamed_physC H
  wp_apply wp_load_access _ rv.uncommittedSize' _ (raftOwn_access_load_uncommittedSize _ _) $$ Hr as Hr
  iapply HΦ; resealC c s

theorem raft.wp_load_maxUncommittedSizeC (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhysC (GF := GF) c r id s }}
      (App (Val (GoInstruction (GoLoad entryPayloadSize.ty)))
        (Val #(r.[raft, go!"maxUncommittedSize"])))
    {{ (v : entryPayloadSize), RET #v; ownRaftPhysC c r id s }} := by
  iintro %Φ H HΦ
  iNamed_physC H
  wp_apply wp_load_access _ rv.maxUncommittedSize' _ (raftOwn_access_load_maxUncommittedSize _ _) $$ Hr as Hr
  iapply HΦ; resealC c s

theorem raft.wp_load_maxMsgSizeC (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhysC (GF := GF) c r id s }}
      (App (Val (GoInstruction (GoLoad entryEncodingSize.ty)))
        (Val #(r.[raft, go!"maxMsgSize"])))
    {{ (v : entryEncodingSize), RET #v; ownRaftPhysC c r id s }} := by
  iintro %Φ H HΦ
  iNamed_physC H
  wp_apply wp_load_access _ rv.maxMsgSize' _ (raftOwn_access_load_maxMsgSize _ _) $$ Hr as Hr
  iapply HΦ; resealC c s

/-- The term never moves back (2026-10-10): `msgsAfterAppend`'s term bounds
(`AAMsgOk`) are relative to it. -/
theorem raft.wp_store_TermC (r : Loc) (id : w64) (s : NState) (v : w64)
    (Hle : uint.Z s.term ≤ uint.Z v) :
    {{ ownRaftPhysC (GF := GF) c r id s }}
      (App (Val (GoInstruction (GoStore go.uint64))) (Val (PairV #(r.[raft, go!"Term"]) #v)))
    {{ RET #(); ownRaftPhysC c r id { s with term := v } }} := by
  iintro %Φ H HΦ
  iNamed_physC H
  wp_apply wp_store_access _ rv.Term' v _ _ (raftOwn_access_store_Term _ _ _) $$ Hr as Hr
  have HmsgsAA_ok' : ∀ m ∈ msgsAA, AAMsgOk id v m :=
    fun m Hm => (HmsgsAA_ok m Hm).mono Hle
  have Hout_term' : ∀ m ∈ msgs ++ msgsAA, OutTermOk s.prevote v m :=
    fun m Hm => (Hout_term m Hm).mono Hle
  iapply HΦ
  iapply ownRaftPhysC_intro c _ _ { s with term := v } _ msgs msgsAA lok
    (by phys_pure) (by phys_pure) (by phys_pure) (by phys_pure) (by phys_pure)
    (by phys_pure) (by phys_pure) (by phys_pure) (by phys_pure) (by phys_pure)
    (by phys_pure) (by phys_pure) (by phys_pure) (by phys_pure) (by phys_pure)
    (by phys_pure) (by phys_pure) (by phys_pure) HmsgsAA_ok' Hout_term' Hgh_out Hgh_unst Hvoter
    $$ Hr Hlogger Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc Houtbox

theorem raft.wp_store_VoteC (r : Loc) (id : w64) (s : NState) (v : w64) :
    {{ ownRaftPhysC (GF := GF) c r id s }}
      (App (Val (GoInstruction (GoStore go.uint64))) (Val (PairV #(r.[raft, go!"Vote"]) #v)))
    {{ RET #(); ownRaftPhysC c r id { s with vote := v } }} := by
  iintro %Φ H HΦ
  iNamed_physC H
  wp_apply wp_store_access _ rv.Vote' v _ _ (raftOwn_access_store_Vote _ _ _) $$ Hr as Hr
  iapply HΦ; resealC c { s with vote := v }

theorem raft.wp_store_leadC (r : Loc) (id : w64) (s : NState) (v : w64) :
    {{ ownRaftPhysC (GF := GF) c r id s }}
      (App (Val (GoInstruction (GoStore go.uint64))) (Val (PairV #(r.[raft, go!"lead"]) #v)))
    {{ RET #(); ownRaftPhysC c r id { s with lead := v } }} := by
  iintro %Φ H HΦ
  iNamed_physC H
  wp_apply wp_store_access _ rv.lead' v _ _ (raftOwn_access_store_lead _ _ _) $$ Hr as Hr
  iapply HΦ; resealC c { s with lead := v }

/-- Stated at `stateW64 ro`, so the caller names the role; the Go code stores the
constant (`StateFollower` = `W64 0`), which unifies with `stateW64 .follower` by
computation. -/
theorem raft.wp_store_stateC (r : Loc) (id : w64) (s : NState) (ro : PRole)
    (Hro : ro ≠ .follower → id ∈ c.voters) :
    {{ ownRaftPhysC (GF := GF) c r id s }}
      (App (Val (GoInstruction (GoStore StateType.ty)))
        (Val (PairV #(r.[raft, go!"state"]) #(stateW64 ro))))
    {{ RET #(); ownRaftPhysC c r id { s with role := ro } }} := by
  iintro %Φ H HΦ
  iNamed_physC H
  wp_apply wp_store_access _ rv.state' (stateW64 ro) _ _ (raftOwn_access_store_state _ _ _) $$ Hr as Hr
  have Hvoter' : ({ s with role := ro } : NState).role ≠ .follower → id ∈ c.voters := Hro
  iapply HΦ
  iapply ownRaftPhysC_intro c _ _ { s with role := ro } _ msgs msgsAA lok
    (by phys_pure) (by phys_pure) (by phys_pure) (by phys_pure) (by phys_pure)
    (by phys_pure) (by phys_pure) (by phys_pure) (by phys_pure) (by phys_pure)
    (by phys_pure) (by phys_pure) (by phys_pure) (by phys_pure) (by phys_pure)
    (by phys_pure) (by phys_pure) (by phys_pure) (by phys_pure) (by phys_pure)
    (by phys_pure) (by phys_pure) Hvoter'
    $$ Hr Hlogger Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc Houtbox

theorem raft.wp_store_stepC (r : Loc) (id : w64) (s : NState) (f : GoFunc) :
    {{ ownRaftPhysC (GF := GF) c r id s }}
      (App (Val (GoInstruction (GoStore stepFunc.ty))) (Val (PairV #(r.[raft, go!"step"]) #f)))
    {{ RET #(); ownRaftPhysC c r id { s with stepfn := f } }} := by
  iintro %Φ H HΦ
  iNamed_physC H
  wp_apply wp_store_access _ rv.step' f _ _ (raftOwn_access_store_step _ _ _) $$ Hr as Hr
  iapply HΦ; resealC c { s with stepfn := f }

/-- `r.tick = f`, for one of the two tick functions: `r.tick` is set from now on. -/
theorem raft.wp_store_tickC (r : Loc) (id : w64) (s : NState) (f : GoFunc)
    (Hf : TickFnOk r f) :
    {{ ownRaftPhysC (GF := GF) c r id s }}
      (App (Val (GoInstruction (GoStore (go.GoType.FunctionType (go.signature.Signature [] false [])))))
        (Val (PairV #(r.[raft, go!"tick"]) #f)))
    {{ RET #(); ownRaftPhysC c r id { s with ticking := true } }} := by
  iintro %Φ H HΦ
  iNamed_physC H
  wp_apply wp_store_access _ rv.tick' f _ _ (raftOwn_access_store_tick _ _ _) $$ Hr as Hr
  iapply HΦ
  iapply ownRaftPhysC_intro c _ _ { s with ticking := true } _ msgs msgsAA lok
    (by phys_pure) (by phys_pure) (by phys_pure) (by phys_pure) (by phys_pure)
    (by phys_pure) (by phys_pure) (by phys_pure) (by phys_pure) (by phys_pure)
    (by phys_pure) (by phys_pure) (by phys_pure) (by phys_pure) (by phys_pure)
    (by phys_pure) (by phys_pure) (fun _ => Hf) (by phys_pure) (by phys_pure) Hgh_out Hgh_unst Hvoter
    $$ Hr Hlogger Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc Houtbox

/-- `r.tick`, once set: one of the two tick functions. -/
theorem raft.wp_load_tickC (r : Loc) (id : w64) (s : NState) (Ht : s.ticking = true) :
    {{ ownRaftPhysC (GF := GF) c r id s }}
      (App (Val (GoInstruction (GoLoad (go.GoType.FunctionType (go.signature.Signature [] false [])))))
        (Val #(r.[raft, go!"tick"])))
    {{ (f : GoFunc), RET #f; ownRaftPhysC c r id s ∗ ⌜TickFnOk r f⌝ }} := by
  iintro %Φ H HΦ
  iNamed_physC H
  wp_apply wp_load_access _ rv.tick' _ (raftOwn_access_load_tick _ _) $$ Hr as Hr
  iapply HΦ
  isplitl
  · resealC c s
  ipureintro; exact Htick Ht

theorem raft.wp_store_electionElapsedC (r : Loc) (id : w64) (s : NState) (v : w64) :
    {{ ownRaftPhysC (GF := GF) c r id s }}
      (App (Val (GoInstruction (GoStore go.int)))
        (Val (PairV #(r.[raft, go!"electionElapsed"]) #v)))
    {{ RET #(); ownRaftPhysC c r id s }} := by
  iintro %Φ H HΦ
  iNamed_physC H
  wp_apply wp_store_access _ rv.electionElapsed' v _ _ (raftOwn_access_store_electionElapsed _ _ _) $$ Hr as Hr
  iapply HΦ; resealC c s

theorem raft.wp_store_heartbeatElapsedC (r : Loc) (id : w64) (s : NState) (v : w64) :
    {{ ownRaftPhysC (GF := GF) c r id s }}
      (App (Val (GoInstruction (GoStore go.int)))
        (Val (PairV #(r.[raft, go!"heartbeatElapsed"]) #v)))
    {{ RET #(); ownRaftPhysC c r id s }} := by
  iintro %Φ H HΦ
  iNamed_physC H
  wp_apply wp_store_access _ rv.heartbeatElapsed' v _ _ (raftOwn_access_store_heartbeatElapsed _ _ _) $$ Hr as Hr
  iapply HΦ; resealC c s

theorem raft.wp_store_randomizedElectionTimeoutC (r : Loc) (id : w64) (s : NState) (v : w64) :
    {{ ownRaftPhysC (GF := GF) c r id s }}
      (App (Val (GoInstruction (GoStore go.int)))
        (Val (PairV #(r.[raft, go!"randomizedElectionTimeout"]) #v)))
    {{ RET #(); ownRaftPhysC c r id s }} := by
  iintro %Φ H HΦ
  iNamed_physC H
  wp_apply wp_store_access _ rv.randomizedElectionTimeout' v _ _ (raftOwn_access_store_randomizedElectionTimeout _ _ _) $$ Hr as Hr
  iapply HΦ; resealC c s

theorem raft.wp_store_pendingConfIndexC (r : Loc) (id : w64) (s : NState) (v : w64) :
    {{ ownRaftPhysC (GF := GF) c r id s }}
      (App (Val (GoInstruction (GoStore go.uint64)))
        (Val (PairV #(r.[raft, go!"pendingConfIndex"]) #v)))
    {{ RET #(); ownRaftPhysC c r id { s with pci := v } }} := by
  iintro %Φ H HΦ
  iNamed_physC H
  wp_apply wp_store_access _ rv.pendingConfIndex' v _ _ (raftOwn_access_store_pendingConfIndex _ _ _) $$ Hr as Hr
  iapply HΦ; resealC c { s with pci := v }

theorem raft.wp_store_uncommittedSizeC (r : Loc) (id : w64) (s : NState) (v : entryPayloadSize) :
    {{ ownRaftPhysC (GF := GF) c r id s }}
      (App (Val (GoInstruction (GoStore entryPayloadSize.ty)))
        (Val (PairV #(r.[raft, go!"uncommittedSize"]) #v)))
    {{ RET #(); ownRaftPhysC c r id s }} := by
  iintro %Φ H HΦ
  iNamed_physC H
  wp_apply wp_store_access _ rv.uncommittedSize' v _ _ (raftOwn_access_store_uncommittedSize _ _ _) $$ Hr as Hr
  iapply HΦ; resealC c s

/-- `switchToConfig` stores `ok && pr.IsLearner` (any value since 2026-10-13, recorded in
`NState.isLearner`; until then only `false`). -/
theorem raft.wp_store_isLearnerC (r : Loc) (id : w64) (s : NState) (b : Bool) :
    {{ ownRaftPhysC (GF := GF) c r id s }}
      (App (Val (GoInstruction (GoStore go.bool)))
        (Val (PairV #(r.[raft, go!"isLearner"]) #b)))
    {{ RET #(); ownRaftPhysC c r id { s with isLearner := b } }} := by
  iintro %Φ H HΦ
  iNamed_physC H
  wp_apply wp_store_access _ rv.isLearner' b _ _ (raftOwn_access_store_isLearner _ _ _) $$ Hr as Hr
  iapply HΦ; resealC c { s with isLearner := b }

/-- `None` (`W64 0`, `abortLeaderTransfer`). -/
theorem raft.wp_store_leadTransfereeC (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhysC (GF := GF) c r id s }}
      (App (Val (GoInstruction (GoStore go.uint64)))
        (Val (PairV #(r.[raft, go!"leadTransferee"]) #(W64 0))))
    {{ RET #(); ownRaftPhysC c r id { s with lt := W64 0 } }} := by
  iintro %Φ H HΦ
  iNamed_physC H
  wp_apply wp_store_access _ rv.leadTransferee' (W64 0) _ _ (raftOwn_access_store_leadTransferee _ _ _) $$ Hr as Hr
  iapply HΦ; resealC c { s with lt := W64 0 }

/-- Another node (2026-10-13, `stepLeader`'s `MsgTransferLeader`). -/
theorem raft.wp_store_leadTransferee_toC (r : Loc) (id : w64) (s : NState) (x : w64)
    (Hx : x ≠ id) :
    {{ ownRaftPhysC (GF := GF) c r id s }}
      (App (Val (GoInstruction (GoStore go.uint64)))
        (Val (PairV #(r.[raft, go!"leadTransferee"]) #x)))
    {{ RET #(); ownRaftPhysC c r id { s with lt := x } }} := by
  iintro %Φ H HΦ
  iNamed_physC H
  wp_apply wp_store_access _ rv.leadTransferee' x _ _ (raftOwn_access_store_leadTransferee _ _ _) $$ Hr as Hr
  iapply HΦ; resealC c { s with lt := x }

/-- Two states that are equal: for a state reached by a run of field stores and the
name a spec gives it (`becomeFollower s t l`, say). Proving the `=` with `rfl` is
cheap; leaving it to unification inside `iframe` can run for minutes (in Rocq;
notes/gotchas.md). -/
theorem ownRaftPhysC_eq (r : Loc) (id : w64) (s1 s2 : NState) :
    s1 = s2 → ⊢ ownRaftPhysC (GF := GF) c r id s1 -∗ ownRaftPhysC c r id s2 := by
  intro H; subst H; iintro H; iexact H

/-- The same, put back at the same tally: the wand gives `ownRaftPhysC` at `s` itself
rather than at `{ s with votes := s.votes }`, so a read-only use (a map lookup,
`JointConfig.IDs`), or a split and re-seal repeated inside a `Visit` closure, does not
pile up setters. -/
theorem ownRaftPhysC_tracker_same (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhysC (GF := GF) c r id s -∗
      ∃ tv, r.[raft, go!"trk"] ↦ tv ∗
        ownTrackerC c tv ⟨s.votes, s.progress, s.prvals⟩ ∗
        (∀ tvx, r.[raft, go!"trk"] ↦ tvx -∗
           ownTrackerC c tvx ⟨s.votes, s.progress, s.prvals⟩ -∗
           ownRaftPhysC c r id s) := by
  iintro Hphys
  icases ownRaftPhysC_tracker c r id s $$ Hphys with ⟨%tv, Htrkf, Htrk, Hback⟩
  iexists tv
  iframe Htrkf Htrk
  iintro %tvx Htrkf Htrk
  ihave Hphys := Hback $$ %tvx %s.votes Htrkf Htrk
  iapply ownRaftPhysC_eq c r id _ _ (by cases s; rfl) $$ Hphys

/-- One peer's `Progress`, borrowed out of the struct by its key at the value
`NState.prvals` records, and given back at that value -- for a read (`IsPaused`, field
loads, `Inflights.Full`). The lookup of `r.trk.Progress[to]` itself goes through
`ownRaftPhys_tracker_same`: it reads the tracker field. The two lookups are premises
inside the logic, so that `s` is fixed by the struct hypothesis the lemma is applied
to, not by the lookups' types: `icases ownRaftPhys_pr … $$ Hphys %Hlk %Hv with …`. -/
theorem ownRaftPhysC_pr (r : Loc) (id : w64) (s : NState) (to : w64) (pr : Loc)
    (p : Progress) :
    ⊢ ownRaftPhysC (GF := GF) c r id s -∗
      ⌜s.progress !! to = some pr⌝ -∗
      ⌜s.prvals !! to = some p⌝ -∗
      ownProgress pr p ∗ (ownProgress pr p -∗ ownRaftPhysC c r id s) := by
  iintro Hphys %Hlk %Hv
  icases ownRaftPhysC_tracker_same c r id s $$ Hphys with ⟨%tv, Htrkf, Htrk, Hback⟩
  icases ownTrackerC_lookup_same c tv ⟨s.votes, s.progress, s.prvals⟩ to pr Hlk $$ Htrk
    with ⟨%p', %Hv', Hp, Hpb⟩
  have Heq : p = p' := Option.some.inj (Hv.symm.trans Hv')
  subst Heq
  iframe Hp
  iintro Hp
  ihave Htrk := Hpb $$ Hp
  iapply Hback $$ Htrkf Htrk

/-- The same, given back at new values, which the state then records -- for a write
(`SentEntries`). -/
theorem ownRaftPhysC_pr_upd (r : Loc) (id : w64) (s : NState) (to : w64) (pr : Loc)
    (p : Progress) :
    ⊢ ownRaftPhysC (GF := GF) c r id s -∗
      ⌜s.progress !! to = some pr⌝ -∗
      ⌜s.prvals !! to = some p⌝ -∗
      ownProgress pr p ∗
      (∀ p', ownProgress pr p' -∗ ⌜p'.learner = p.learner⌝ -∗
         ownRaftPhysC c r id { s with prvals := <[to := p']> s.prvals }) := by
  iintro Hphys %Hlk %Hv
  icases ownRaftPhysC_tracker_prvals c r id s $$ Hphys with ⟨%tv, Htrkf, Htrk, Hback⟩
  icases ownTrackerC_lookup c tv ⟨s.votes, s.progress, s.prvals⟩ to pr Hlk $$ Htrk
    with ⟨%p', %Hv', Hp, Hpb⟩
  have Heq : p = p' := Option.some.inj (Hv.symm.trans Hv')
  subst Heq
  iframe Hp
  iintro %p'' Hp %Hl
  ihave Htrk := Hpb $$ %p'' Hp %Hl
  iapply Hback $$ Htrkf Htrk

/-- A write that does not need to know the value it overwrites (`SentCommit`). -/
theorem ownRaftPhysC_pr_any (r : Loc) (id : w64) (s : NState) (to : w64) (pr : Loc) :
    ⊢ ownRaftPhysC (GF := GF) c r id s -∗
      ⌜s.progress !! to = some pr⌝ -∗
      ∃ p, ownProgress pr p ∗
      (∀ p', ownProgress pr p' -∗ ⌜p'.learner = p.learner⌝ -∗
         ownRaftPhysC c r id { s with prvals := <[to := p']> s.prvals }) := by
  iintro Hphys %Hlk
  icases ownRaftPhysC_tracker_prvals c r id s $$ Hphys with ⟨%tv, Htrkf, Htrk, Hback⟩
  icases ownTrackerC_lookup c tv ⟨s.votes, s.progress, s.prvals⟩ to pr Hlk $$ Htrk
    with ⟨%p', %Hv', Hp, Hpb⟩
  iexists p'
  iframe Hp
  iintro %p'' Hp %Hl
  ihave Htrk := Hpb $$ %p'' Hp %Hl
  iapply Hback $$ Htrkf Htrk

/-- The log, at the state `s` records, put back at any state. This is the accessor for
a function that changes the log (`appendEntry`'s `append`, `loadState`'s `committed`,
`newRaft`'s `appliedTo`). -/
theorem ownRaftPhysC_log_at (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhysC (GF := GF) c r id s -∗
      ownRaftLog s.log s.logst ∗ ⌜LogGhOk s s.logst⌝ ∗
      (∀ ls', ownRaftLog s.log ls' -∗ ⌜LogGhOk s ls'⌝ -∗
        ownRaftPhysC c r id { s with logst := ls' }) := by
  iintro H
  iNamed_physC H
  ihave Hlog : ownRaftLog (GF := GF) s.log s.logst $$ [Hlog]
  · rw [← Hlogp]; iexact Hlog
  iframe Hlog
  isplitr
  · ipureintro; exact Hgh_unst
  iintro %ls' Hlog %Hgh_unst'
  ihave Hlog : ownRaftLog (GF := GF) rv.raftLog' ls' $$ [Hlog]
  · rw [Hlogp]; iexact Hlog
  iapply ownRaftPhysC_intro c _ _ { s with logst := ls' } _ msgs msgsAA lok
    Hid Hterm Hvote Hlead Hstate Hstepfn Hprevote HpropForward HnoCCV HnoCheckQuorum HnoLearner
    HnoTransfer Hpci Hid_nz HelectionTimeout Hlok Hlogp Htick HmsgsAA_ok Hout_term Hgh_out
    Hgh_unst' Hvoter
    $$ Hr Hlogger Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc Houtbox

/-- The log at the state `s` records, put back at that same state: for a read through
`ownRaftLog` (a `raftLog` method that keeps its state, a field load through
`ownRaftLog_struct`). The wand gives `ownRaftPhysC` at `s` itself, so no
`ownRaftPhys_eq` is needed afterwards. -/
theorem ownRaftPhysC_log_same (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhysC (GF := GF) c r id s -∗
      ownRaftLog s.log s.logst ∗
      (ownRaftLog s.log s.logst -∗ ownRaftPhysC c r id s) := by
  iintro H
  icases ownRaftPhysC_log_at c r id s $$ H with ⟨Hlog, %Hgh, Hback⟩
  iframe Hlog
  iintro Hlog
  ihave H := Hback $$ %s.logst Hlog %Hgh
  iapply ownRaftPhysC_eq c r id _ _ (by cases s; rfl) $$ H

/-- The ghost flag `unst` holds of the log (2026-10-10, `NGhost`), read out. -/
theorem ownRaftPhysC_gh (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhysC (GF := GF) c r id s -∗ ⌜LogGhOk s s.logst⌝ ∗ ownRaftPhysC c r id s := by
  iintro H
  icases ownRaftPhysC_log_at c r id s $$ H with ⟨Hlog, %Hgh, Hback⟩
  isplitr
  · ipureintro; exact Hgh
  ihave H := Hback $$ %s.logst Hlog %Hgh
  iapply ownRaftPhysC_eq c r id _ _ (by cases s; rfl) $$ H

/-- `r.msgs`, append-only: a message `m'` appended joins the abstract outbox (at the
end, up to permutation -- see `Houtbox`) as whatever `msgAbs` says it contributes:
nothing for a type the model does not describe, else its abstraction, given
`m'.Entries ↦*□ ents`. -/
theorem ownRaftPhysC_msgs (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhysC (GF := GF) c r id s -∗
      ∃ sl ms, r.[raft, go!"msgs"] ↦ sl ∗ sl ↦* ms ∗
        ownSliceCap raftpb.Message sl (DFrac.own 1) ∗
        (∀ sl' m' a, r.[raft, go!"msgs"] ↦ sl' -∗ sl' ↦* (ms ++ [m']) -∗
           ownSliceCap raftpb.Message sl' (DFrac.own 1) -∗
           msgAbs m' a -∗
           ⌜OutTermOk s.prevote s.term m'⌝ -∗
           ownRaftPhysC c r id { s with outbox := s.outbox ++ absList [a] }) := by
  iintro H
  iNamed_physC H
  icases raft_split_msgs r rv $$ Hr with ⟨Hf, Hback⟩
  iexists rv.msgs', msgs
  iframe Hf Hmsgs Hmsgs_cap
  iintro %sl' %m' %a Hf Hmsgs Hmsgs_cap #Ha %Hot
  have Hout_term' : ∀ m ∈ (msgs ++ [m']) ++ msgsAA, OutTermOk s.prevote s.term m := by
    intro m Hm
    simp only [List.mem_append, List.mem_singleton] at Hm
    rcases Hm with (Hm | rfl) | Hm
    · exact Hout_term m (List.mem_append_left _ Hm)
    · exact Hot
    · exact Hout_term m (List.mem_append_right _ Hm)
  ihave Hr := Hback $$ %sl' Hf
  iunfold outboxRel at Houtbox
  icases Houtbox with ⟨%as1, %as2, %Ho, #H1, #H2⟩
  ihave #Houtbox : outboxRel (GF := GF) (s.outbox ++ absList [a]) (msgs ++ [m']) msgsAA $$ []
  · unfold outboxRel
    iexists as1 ++ [a], as2
    isplitr
    · ipureintro
      simp only [absList, List.filterMap_append, List.append_assoc] at Ho ⊢
      refine (Ho.append_right _).trans ?_
      simp only [List.append_assoc]
      exact List.Perm.append_left _ List.perm_append_comm
    isplitr
    · iapply (BigSepL2.bigSepL2_snoc (Φ := fun _ m a => msgAbs (GF := GF) m a)).2
      iframe H1 Ha
    · iexact H2
  iapply ownRaftPhysC_intro c _ _ { s with outbox := s.outbox ++ absList [a] }
      { rv with msgs' := sl' } (msgs ++ [m']) msgsAA lok
    Hid Hterm Hvote Hlead Hstate Hstepfn Hprevote HpropForward HnoCCV HnoCheckQuorum HnoLearner
    HnoTransfer Hpci Hid_nz HelectionTimeout Hlok Hlogp Htick HmsgsAA_ok Hout_term'
    (by simp only [List.length_append, List.length_singleton]; omega) Hgh_unst Hvoter
    $$ Hr Hlogger Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc Houtbox

/-- `r.msgsAfterAppend`, likewise. -/
theorem ownRaftPhysC_msgsAA (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhysC (GF := GF) c r id s -∗
      ∃ sl ms, r.[raft, go!"msgsAfterAppend"] ↦ sl ∗ sl ↦* ms ∗
        ownSliceCap raftpb.Message sl (DFrac.own 1) ∗
        (∀ sl' m' a, r.[raft, go!"msgsAfterAppend"] ↦ sl' -∗
           sl' ↦* (ms ++ [m']) -∗
           ownSliceCap raftpb.Message sl' (DFrac.own 1) -∗
           msgAbs m' a -∗
           ⌜AAMsgOk id s.term m'⌝ -∗
           ⌜OutTermOk s.prevote s.term m'⌝ -∗
           ownRaftPhysC c r id { s with outbox := s.outbox ++ absList [a] }) := by
  iintro H
  iNamed_physC H
  icases raft_split_msgsAA r rv $$ Hr with ⟨Hf, Hback⟩
  iexists rv.msgsAfterAppend', msgsAA
  iframe Hf HmsgsAA HmsgsAA_cap
  iintro %sl' %m' %a Hf HmsgsAA HmsgsAA_cap #Ha %Hok %Hot
  have Hout_term' : ∀ m ∈ msgs ++ (msgsAA ++ [m']), OutTermOk s.prevote s.term m := by
    intro m Hm
    simp only [List.mem_append, List.mem_singleton] at Hm
    rcases Hm with Hm | Hm | rfl
    · exact Hout_term m (List.mem_append_left _ Hm)
    · exact Hout_term m (List.mem_append_right _ Hm)
    · exact Hot
  have HmsgsAA_ok' : ∀ m ∈ msgsAA ++ [m'], AAMsgOk id s.term m := by
    intro m Hm
    rcases List.mem_append.1 Hm with Hm | Hm
    · exact HmsgsAA_ok m Hm
    · rw [List.mem_singleton.1 Hm]; exact Hok
  ihave Hr := Hback $$ %sl' Hf
  iunfold outboxRel at Houtbox
  icases Houtbox with ⟨%as1, %as2, %Ho, #H1, #H2⟩
  ihave #Houtbox : outboxRel (GF := GF) (s.outbox ++ absList [a]) msgs (msgsAA ++ [m']) $$ []
  · unfold outboxRel
    iexists as1, as2 ++ [a]
    isplitr
    · ipureintro
      simp only [absList, List.filterMap_append, List.append_assoc] at Ho ⊢
      simpa [List.append_assoc] using Ho.append_right (List.filterMap _root_.id [a])
    isplitr
    · iexact H1
    · iapply (BigSepL2.bigSepL2_snoc (Φ := fun _ m a => msgAbs (GF := GF) m a)).2
      iframe H2 Ha
  iapply ownRaftPhysC_intro c _ _ { s with outbox := s.outbox ++ absList [a] }
      { rv with msgsAfterAppend' := sl' } msgs (msgsAA ++ [m']) lok
    Hid Hterm Hvote Hlead Hstate Hstepfn Hprevote HpropForward HnoCCV HnoCheckQuorum HnoLearner
    HnoTransfer Hpci Hid_nz HelectionTimeout Hlok Hlogp Htick HmsgsAA_ok' Hout_term'
    (by simp only [List.length_append, List.length_singleton]; omega) Hgh_unst Hvoter
    $$ Hr Hlogger Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc Houtbox

/-- The `readOnly` object (2026-10-12: at `s.rd.ro`, and back at any record, which the state
then records). `reset` replaces it; `bcastHeartbeat` reads its context. -/
theorem ownRaftPhysC_readOnly (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhysC (GF := GF) c r id s -∗
      ∃ (ro : Loc),
        r.[raft, go!"readOnly"] ↦ ro ∗ ownReadOnly ro s.rd.ro ∗
        (∀ (ro' : Loc) (rr' : ReadOnly),
           r.[raft, go!"readOnly"] ↦ ro' -∗ ownReadOnly ro' rr' -∗
           ownRaftPhysC c r id { s with rd := { s.rd with ro := rr' } }) := by
  iintro H
  iNamed_physC H
  iunfold ownRaftMisc at Hmisc
  iNamed Hmisc
  icases raft_split_readOnly r rv $$ Hr with ⟨Hf, Hback⟩
  iexists rv.readOnly'
  iframe Hf Hro_obj
  iintro %ro' %rr' Hf Hro_obj
  ihave Hr := Hback $$ %ro' Hf
  ihave Hmisc : ownRaftMisc (GF := GF) rv.readStates' ro' rv.pendingReadIndexMessages'
      { s.rd with ro := rr' } $$ [HreadStates HreadStates_cap Hro_obj Hpri Hpri_cap]
  · unfold ownRaftMisc
    simp only [named]
    iframe HreadStates HreadStates_cap Hro_obj Hpri Hpri_cap Hpri_ents
  resealC c { s with rd := { s.rd with ro := rr' } }

/-- The tracker and the `readOnly` object together (2026-10-13): `stepLeader`'s
`r.readOnly.maybeAdvance(r.trk.Voters)` lends the tracker's voter map to the read-only
object's method. Back at any tracker value (same tally, progress map and values) and any
read-only record, which the state then records. -/
theorem ownRaftPhysC_readOnly_trk (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhysC (GF := GF) c r id s -∗
      ∃ (tv : tracker.ProgressTracker) (ro : Loc),
        r.[raft, go!"trk"] ↦ tv ∗
        ownTrackerC c tv ⟨s.votes, s.progress, s.prvals⟩ ∗
        r.[raft, go!"readOnly"] ↦ ro ∗ ownReadOnly ro s.rd.ro ∗
        (∀ (tv' : tracker.ProgressTracker) (ro' : Loc) (rr' : ReadOnly),
           r.[raft, go!"trk"] ↦ tv' -∗
           ownTrackerC c tv' ⟨s.votes, s.progress, s.prvals⟩ -∗
           r.[raft, go!"readOnly"] ↦ ro' -∗ ownReadOnly ro' rr' -∗
           ownRaftPhysC c r id { s with rd := { s.rd with ro := rr' } }) := by
  iintro H
  iNamed_physC H
  iunfold ownRaftMisc at Hmisc
  iNamed Hmisc
  icases raft_split_trk_readOnly r rv $$ Hr with ⟨Hft, Hf, Hback⟩
  iexists rv.trk', rv.readOnly'
  iframe Hft Htrk Hf Hro_obj
  iintro %tv' %ro' %rr' Hft Htrk Hf Hro_obj
  ihave Hr := Hback $$ %tv' %ro' Hft Hf
  ihave Hmisc : ownRaftMisc (GF := GF) rv.readStates' ro' rv.pendingReadIndexMessages'
      { s.rd with ro := rr' } $$ [HreadStates HreadStates_cap Hro_obj Hpri Hpri_cap]
  · unfold ownRaftMisc
    simp only [named]
    iframe HreadStates HreadStates_cap Hro_obj Hpri Hpri_cap Hpri_ents
  iapply ownRaftPhysC_intro c r id { s with rd := { s.rd with ro := rr' } }
      { rv with trk' := tv', readOnly' := ro' } msgs msgsAA lok
    Hid Hterm Hvote Hlead Hstate Hstepfn Hprevote HpropForward HnoCCV HnoCheckQuorum HnoLearner
    HnoTransfer Hpci Hid_nz HelectionTimeout Hlok Hlogp Htick HmsgsAA_ok Hout_term Hgh_out Hgh_unst Hvoter
    $$ Hr Hlogger Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc Houtbox

/-- The three read-index fields with what hangs off them (2026-10-12), back at any values
and any read state, which the state then records. -/
theorem ownRaftPhysC_misc (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhysC (GF := GF) c r id s -∗
      ∃ (rs : GoSlice) (ro : Loc) (pr : GoSlice),
        r.[raft, go!"readStates"] ↦ rs ∗ r.[raft, go!"readOnly"] ↦ ro ∗
        r.[raft, go!"pendingReadIndexMessages"] ↦ pr ∗
        ownRaftMisc rs ro pr s.rd ∗
        (∀ (rs' : GoSlice) (ro' : Loc) (pr' : GoSlice) (rd' : RdState),
           r.[raft, go!"readStates"] ↦ rs' -∗ r.[raft, go!"readOnly"] ↦ ro' -∗
           r.[raft, go!"pendingReadIndexMessages"] ↦ pr' -∗
           ownRaftMisc rs' ro' pr' rd' -∗
           ownRaftPhysC c r id { s with rd := rd' }) := by
  iintro H
  iNamed_physC H
  icases raft_split_misc r rv $$ Hr with ⟨Hf1, Hf2, Hf3, Hback⟩
  iexists rv.readStates', rv.readOnly', rv.pendingReadIndexMessages'
  iframe Hf1 Hf2 Hf3 Hmisc
  iintro %rs' %ro' %pr' %rd' Hf1 Hf2 Hf3 Hmisc
  ihave Hr := Hback $$ %rs' %ro' %pr' Hf1 Hf2 Hf3
  resealC c { s with rd := rd' }

/-- Rocq `own_raft_phys_view`: the struct open for `RawNode.Ready` (see
`raft_split_view`). Since 2026-10-13 with the `ReadState`s' slice (read-only, and its
capacity), and `Hclose` takes `readStates` back at any slice and any read state that
changes only the `ReadState`s (`acceptReady` sets the field to `nil`). -/
theorem ownRaftPhysC_view (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhysC (GF := GF) c r id s -∗
      iprop(∃ (rs sl1 sl2 : GoSlice) (ms1 ms2 : List raftpb.Message),
        "#Hf_id" ∷ r.[raft, go!"id"] ↦□ id ∗
        "Hf_Term" ∷ r.[raft, go!"Term"] ↦ s.term ∗
        "Hf_Vote" ∷ r.[raft, go!"Vote"] ↦ s.vote ∗
        "Hf_readStates" ∷ r.[raft, go!"readStates"] ↦ rs ∗
        "%Hrs" ∷ ⌜s.rd.states.length = sint.nat rs.len ∧ 0 ≤ sint.Z rs.len⌝ ∗
        "#HreadStates" ∷ rs ↦*□ s.rd.states ∗
        "HreadStates_cap" ∷ ownSliceCap ReadState rs (DFrac.own 1) ∗
        "Hf_raftLog" ∷ r.[raft, go!"raftLog"] ↦ s.log ∗
        "Hf_state" ∷ r.[raft, go!"state"] ↦ stateW64 s.role ∗
        "Hf_lead" ∷ r.[raft, go!"lead"] ↦ s.lead ∗
        "Hf_msgs" ∷ r.[raft, go!"msgs"] ↦ sl1 ∗ "Hmsgs" ∷ sl1 ↦* ms1 ∗
        "Hmsgs_cap" ∷ ownSliceCap raftpb.Message sl1 (DFrac.own 1) ∗
        "Hf_msgsAA" ∷ r.[raft, go!"msgsAfterAppend"] ↦ sl2 ∗ "HmsgsAA" ∷ sl2 ↦* ms2 ∗
        "HmsgsAA_cap" ∷ ownSliceCap raftpb.Message sl2 (DFrac.own 1) ∗
        "#Houtbox" ∷ outboxRel s.outbox ms1 ms2 ∗
        "%HmsgsAA_ok" ∷ ⌜∀ m ∈ ms2, AAMsgOk id s.term m⌝ ∗
        "%Hout_term" ∷ ⌜∀ m ∈ ms1 ++ ms2, OutTermOk s.prevote s.term m⌝ ∗
        "%Hgh_out" ∷ ⌜s.gh.outlb ≤ ms1.length + ms2.length⌝ ∗
        "%Hgh_unst" ∷ ⌜LogGhOk s s.logst⌝ ∗
        "Hlog" ∷ ownRaftLog s.log s.logst ∗
        "Hclose" ∷ (∀ (sl1' sl2' : GoSlice) (ms1' ms2' : List raftpb.Message) (o : List Msg)
                      (ls' : LogState) (g : NGhost) (rs' : GoSlice) (rd' : RdState),
            r.[raft, go!"Term"] ↦ s.term -∗
            r.[raft, go!"Vote"] ↦ s.vote -∗
            r.[raft, go!"readStates"] ↦ rs' -∗
            rs' ↦*□ rd'.states -∗ ownSliceCap ReadState rs' (DFrac.own 1) -∗
            ⌜rd'.ro = s.rd.ro ∧ rd'.pend = s.rd.pend⌝ -∗
            r.[raft, go!"raftLog"] ↦ s.log -∗
            r.[raft, go!"state"] ↦ stateW64 s.role -∗
            r.[raft, go!"lead"] ↦ s.lead -∗
            r.[raft, go!"msgs"] ↦ sl1' -∗ sl1' ↦* ms1' -∗
            ownSliceCap raftpb.Message sl1' (DFrac.own 1) -∗
            r.[raft, go!"msgsAfterAppend"] ↦ sl2' -∗ sl2' ↦* ms2' -∗
            ownSliceCap raftpb.Message sl2' (DFrac.own 1) -∗
            outboxRel o ms1' ms2' -∗
            ⌜∀ m ∈ ms2', AAMsgOk id s.term m⌝ -∗
            ⌜∀ m ∈ ms1' ++ ms2', OutTermOk s.prevote s.term m⌝ -∗
            ⌜g.outlb ≤ ms1'.length + ms2'.length⌝ -∗
            ⌜g.unst = true → nextUnstable ls' ≠ [] ∨ ls'.snap ≠ none⌝ -∗
            ownRaftLog s.log ls' -∗
            ownRaftPhysC c r id { s with outbox := o, logst := ls', gh := g, rd := rd' })) := by
  iintro H
  iNamed_physC H
  iunfold ownRaftMisc at Hmisc
  iNamed Hmisc
  ihave #HreadStates := HreadStates
  ihave %Hrl := ownSlice_len _ _ _ $$ HreadStates
  icases raft_split_view r rv $$ Hr with
    ⟨Hfid, HfTerm, HfVote, Hfrs, Hflog, Hfst, Hfm, Hfma, Hfld, Hback⟩
  ihave #Hfid : r.[raft, go!"id"] ↦□ id $$ [Hfid]
  · rw [← Hid]; iexact Hfid
  ihave HfTerm : r.[raft, go!"Term"] ↦ s.term $$ [HfTerm]
  · rw [← Hterm]; iexact HfTerm
  ihave HfVote : r.[raft, go!"Vote"] ↦ s.vote $$ [HfVote]
  · rw [← Hvote]; iexact HfVote
  ihave Hflog : r.[raft, go!"raftLog"] ↦ s.log $$ [Hflog]
  · rw [← Hlogp]; iexact Hflog
  ihave Hfst : r.[raft, go!"state"] ↦ stateW64 s.role $$ [Hfst]
  · rw [← Hstate]; iexact Hfst
  ihave Hfld : r.[raft, go!"lead"] ↦ s.lead $$ [Hfld]
  · rw [← Hlead]; iexact Hfld
  ihave Hlog : ownRaftLog (GF := GF) s.log s.logst $$ [Hlog]
  · rw [← Hlogp]; iexact Hlog
  iexists rv.readStates', rv.msgs', rv.msgsAfterAppend', msgs, msgsAA
  simp only [named]
  iframe Hfid HfTerm HfVote Hfrs Hflog Hfst Hfld Hfm Hfma Hmsgs Hmsgs_cap HmsgsAA
    HmsgsAA_cap Houtbox Hlog HreadStates HreadStates_cap
  isplitr
  · ipureintro; exact Hrl
  isplitr
  · ipureintro; exact HmsgsAA_ok
  isplitr
  · ipureintro; exact Hout_term
  isplitr
  · ipureintro; exact Hgh_out
  isplitr
  · ipureintro; exact Hgh_unst
  iintro %sl1' %sl2' %ms1' %ms2' %o %ls' %g %rs' %rd' HfTerm HfVote Hfrs Hrs' Hrs'_cap
    %Hrd' Hflog Hfst Hfld Hfm Hmsgs
    Hmsgs_cap Hfma HmsgsAA HmsgsAA_cap #Houtbox' %HmsgsAA_ok' %Hout_term' %Hg1 %Hg2 Hlog
  ihave Hmisc : ownRaftMisc (GF := GF) rs' rv.readOnly' rv.pendingReadIndexMessages' rd'
      $$ [Hrs' Hrs'_cap Hro_obj Hpri Hpri_cap]
  · unfold ownRaftMisc
    simp only [named]
    rw [Hrd'.1, Hrd'.2]
    iframe Hrs' Hrs'_cap Hro_obj Hpri Hpri_cap Hpri_ents
  ihave HfTerm : r.[raft, go!"Term"] ↦ rv.Term' $$ [HfTerm]
  · rw [Hterm]; iexact HfTerm
  ihave HfVote : r.[raft, go!"Vote"] ↦ rv.Vote' $$ [HfVote]
  · rw [Hvote]; iexact HfVote
  ihave Hflog : r.[raft, go!"raftLog"] ↦ rv.raftLog' $$ [Hflog]
  · rw [Hlogp]; iexact Hflog
  ihave Hfst : r.[raft, go!"state"] ↦ rv.state' $$ [Hfst]
  · rw [Hstate]; iexact Hfst
  ihave Hfld : r.[raft, go!"lead"] ↦ rv.lead' $$ [Hfld]
  · rw [Hlead]; iexact Hfld
  ihave Hlog : ownRaftLog (GF := GF) rv.raftLog' ls' $$ [Hlog]
  · rw [Hlogp]; iexact Hlog
  ihave Hr := Hback $$ %sl1' %sl2' %rs' HfTerm HfVote Hfrs Hflog Hfst Hfm Hfma Hfld
  iapply ownRaftPhysC_intro c _ _ { s with outbox := o, logst := ls', gh := g, rd := rd' }
      { rv with msgs' := sl1', msgsAfterAppend' := sl2', readStates' := rs' } ms1' ms2' lok
    Hid Hterm Hvote Hlead Hstate Hstepfn Hprevote HpropForward HnoCCV HnoCheckQuorum HnoLearner
    HnoTransfer Hpci Hid_nz HelectionTimeout Hlok Hlogp Htick HmsgsAA_ok' Hout_term' Hg1 Hg2 Hvoter
    $$ Hr Hlogger Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc Houtbox'


/-- The tracker replaced while the log is in use (`ownRaftPhys_retrack` at any
configurations): `restore` at a node of any configuration `c0` installs the snapshot's `c`. -/
theorem ownRaftPhysC_retrack (c0 : CfgM) (r : Loc) (id : w64) (s : NState)
    (Hv : s.role ≠ .follower → id ∈ c.voters) :
    ⊢ ownRaftPhysC (GF := GF) c0 r id s -∗
      ∃ tv, r.[raft, go!"trk"] ↦ tv ∗
        ownTrackerC c0 tv ⟨s.votes, s.progress, s.prvals⟩ ∗
        r.[raft, go!"raftLog"] ↦ s.log ∗
        ownRaftLog s.log s.logst ∗
        (∀ tv' votes' prs' pvs' ls',
           r.[raft, go!"raftLog"] ↦ s.log -∗
           r.[raft, go!"trk"] ↦ tv' -∗
           ownTrackerC c tv' ⟨votes', prs', pvs'⟩ -∗
           ownRaftLog s.log ls' -∗ ⌜LogGhOk s ls'⌝ -∗
           ownRaftPhysC c r id
             { s with votes := votes', progress := prs', prvals := pvs', logst := ls' }) := by
  iintro H
  iNamed_physC H
  icases raft_split_raftLog_trk r rv $$ Hr with ⟨Hlf, Hf, Hback⟩
  iexists rv.trk'
  iframe Hf Htrk
  ihave Hlf : r.[raft, go!"raftLog"] ↦ s.log $$ [Hlf]
  · rw [← Hlogp]; iexact Hlf
  ihave Hlog : ownRaftLog (GF := GF) s.log s.logst $$ [Hlog]
  · rw [← Hlogp]; iexact Hlog
  iframe Hlf Hlog
  iintro %tv' %votes' %prs' %pvs' %ls' Hlf Hf Htrk Hlog %Hgh_unst'
  ihave Hlf : r.[raft, go!"raftLog"] ↦ rv.raftLog' $$ [Hlf]
  · rw [Hlogp]; iexact Hlf
  ihave Hlog : ownRaftLog (GF := GF) rv.raftLog' ls' $$ [Hlog]
  · rw [Hlogp]; iexact Hlog
  ihave Hr := Hback $$ %tv' Hlf Hf
  iapply ownRaftPhysC_intro c r id
      { s with votes := votes', progress := prs', prvals := pvs', logst := ls' }
      { rv with trk' := tv' } msgs msgsAA lok
    Hid Hterm Hvote Hlead Hstate Hstepfn Hprevote HpropForward HnoCCV HnoCheckQuorum HnoLearner
    HnoTransfer Hpci Hid_nz HelectionTimeout Hlok Hlogp Htick HmsgsAA_ok Hout_term Hgh_out
    Hgh_unst' Hv
    $$ Hr Hlogger Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc Houtbox

end physCfields

set_option hygiene false in
/-- A logging call through `r.logger`, once the raft fields its arguments read have
been loaded (each with its own lemma, by the caller): the variadic argument slice, the
load of `r.logger`, and the logger spec. Works on `Hphys`. A fixed sequence of steps,
no search: it applies the same lemmas in the same order every time.

The argument slice is kept (anonymously) and its capacity dropped, as in Rocq. The
loaded logger is named `lok` and its `isLogger` (`Hlg`) is cleared after the call. The
method side condition `meth ∈ logMethods` is Rocq's `solve_log_method`, here `decide`.
Depending on the arguments, `wp_slice_literal`'s equation may already be discharged,
hence the `try`s (as in Rocq). -/
macro "wp_raft_log" : tactic => `(tactic| (
  wp_apply Perennial.wp_slice_literal
  try (isplitr; (ipureintro; rfl))
  try iintro %_ ⟨_, -⟩
  try wp_auto
  wp_apply Perennial.EtcdGrove.raft.wp_load_logger $$ Hphys as %lok ⟨Hphys, #Hlg⟩
  wp_apply Perennial.EtcdGrove.Logger.wp_logf lok _ _ _ (by decide) $$ Hlg
  iclear Hlg
  try wp_auto))


/-- `wp_raft_log` on `ownRaftPhysC` (`raft.wp_load_loggerC`). -/
macro "wp_raft_logC" : tactic => `(tactic| (
  wp_apply Perennial.wp_slice_literal
  try (isplitr; (ipureintro; rfl))
  try iintro %_ ⟨_, -⟩
  try wp_auto
  wp_apply Perennial.EtcdGrove.raft.wp_load_loggerC $$ Hphys as %lok ⟨Hphys, #Hlg⟩
  wp_apply Perennial.EtcdGrove.Logger.wp_logf lok _ _ _ (by decide) $$ Hlg
  iclear Hlg
  try wp_auto))

end EtcdGrove
end Perennial
