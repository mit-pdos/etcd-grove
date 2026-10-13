/-
Port of election_proof/protocol.v, lines 1–1424 (the model) at feb5c73d4. The ghost
part of `protocol.v` (lines 1426 on) is ported separately (`Protocol/Ghost*.lean`),
on top of this file.

Protocol-level model of etcd raft: election and log replication.

This file is the specification side of the refinement proof in `Link.lean`: it
defines the abstract state machine that a single raft node is supposed to implement.
(The ghost state `ownRaftGhost` representing a node's protocol state, the knowledge
`isMessage` attached to a message that has legitimately been put on the network, and
the single fancy-update lemma connecting them are in the ghost part.)

Scope. Everything here (and the proofs in `Link.lean`) assumes:
* no pre-vote            (`r.preVote = false`),
* no check-quorum        (`r.checkQuorum = false`),
* no read-only requests  (no `MsgReadIndex` is ever stepped),
* no reconfiguration     (the voter set `cfg` is fixed, no learners),
* no snapshot received   (phase 2 of notes/raft-replication-model.md: the rules
                          `Step.snap*` and `isMessage` for `snap` are here since
                          2026-10-02, but `Step` is not yet specified for `MsgSnap`),
* **no configuration change is ever requested** -- so the log contains no
  `EntryConfChange` or `EntryConfChangeV2` entry, and `r.hasUnappliedConfChanges()` is
  always `false`. See notes/raft-implementation-facts.md.

**Since 2026-10-01 the model has a log** (notes/raft-replication-model.md): a node's
protocol state is `(term, vote, lead, role, votes, outbox)` plus the log (`base`,
`log`, `commit`) and, for a leader, each voter's `Progress.Match` (`matched`). The log
functions are `Plog.lean`'s, which the `raftLog` specs are stated with too.

**Admitted.** By the user's decision of 2026-10-01 this file may contain `Admitted`
lemmas. Since 2026-10-03 it contains none: Leader Completeness and State Machine
Safety are `Qed` -- over two nodes' ghost states since 2026-10-05, when the one global
committed log (`isCommitted`, `ownCommitted`, the invariant `raftCommitInv`) went in --
from the history invariants added to `ownLogGhost` / `ownRaftGhost` that day (full
logs, campaign records, vote-time logs, acknowledgement histories; known leaders and
winning quorums since 2026-10-05, for pre-vote's `Step.abandon`). Every rule's ghost
update, the four protocol facts the code's `Panicf`s rely on, and `log_matching` are
`Qed` too.

The deferred premises of 2026-10-01 are all in (`AppOk`'s prefix clause went in on
2026-10-02 with the pinned `raftLog.entries`).

Lean notes:
* The Rocq modules `role`, `mtype`, `msg`, `pstate` are the types `Role`, `MsgType`,
  `Msg`, `PState` (as in the older `Protocol.lean`, whose names this file reuses: the
  two are not meant to be imported together). The message fields Rocq calls
  `from`/`to` are `src`/`dst`. Rocq's real constructor `msg.mk_v` is `Msg.mkV`; its
  notation `msg.mk` (the constructor applied to `voters = []`) is the reducible
  `Msg.mk`. `mtype.Propose` is `MsgType.propose`.
* The rules of `step` are the constructors of `Step`, without the `step_` prefix and
  lowerCamel (`step_higher_term` is `Step.higherTerm`). Rocq's `let s' := … in` in a
  rule's conclusion is inlined.
* `s <| f := v |>` is `{ s with f := v }`; `l !! k` on lists is `l[k]?`; `is_Some o` is
  `o.isSome`; `l1 `prefix_of` l2` is `l1 <+: l2`; `imap` is `List.mapIdx`; `Forall P l`
  is `∀ x ∈ l, P x`; `default d o` is `o.getD d`; `Z.of_nat k` is `(k : Int)`.
* Prop-valued definitions are UpperCamel (`PlogWfR`, `AppOk`, `IsQuorum`, `PCanVote`),
  and lemma names keep definition names as written (`PlogWfR_wf`, `FullOk_take`).
  Lemmas whose Rocq name does not start with a definition's name keep their snake_case
  name (`plog_match_down`, `full_term_at`, `batch_lookup`).
* Helpers with no Rocq counterpart (stdpp lemmas): `list_drop_S`, `prefix_lookup_Some`.
-/
module

public import Proof.go_etcd_io.raft.v3.Plog
public import Perennial.Std.Word.LittleEndian
public import Proof.go_etcd_io.raft.v3.ProjSimps

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open GMap go_etcd_io.raft.v3

/-! ## Roles -/

inductive Role where
  | follower | candidate | leader
  deriving DecidableEq, Inhabited

/-! ## Abstract messages

One constructor per `raftpb.MessageType` raft sends between nodes. `propose` is
`MsgProp`. -/

inductive MsgType where
  | vote | voteResp | app | appResp | heartbeat | heartbeatResp
  | propose | snap
  | preVote | preVoteResp | readIndex | readIndexResp
  deriving DecidableEq, Inhabited

/-- Every field of a `raftpb.Message` the protocol reads. `entries` is the list behind
`Message.Entries`; see `absMsg` (`Defs.lean`) for why the abstraction of a physical
message needs that list as an argument.

`index`/`logterm` of a `snap` are the snapshot's `Metadata.Index`/`Metadata.Term`, and
`voters` its `Metadata.ConfState.Voters` -- all behind the pointer `Message.Snapshot`,
read by `absSnap` (`Defs.lean`). Every other message has `voters = []`. -/
structure Msg [FfiSyntax] where
  mkV ::
  ty : MsgType
  /-- the sender (Go `m.From`) -/
  src : w64
  /-- the receiver (Go `m.To`) -/
  dst : w64
  term : w64
  reject : Bool
  /-- `Index` -/
  index : w64
  /-- `LogTerm` -/
  logterm : w64
  /-- `Commit` -/
  commit : w64
  /-- `RejectHint` -/
  rejecthint : w64
  /-- `Entries` -/
  entries : List raftpb.Entry
  /-- a `snap`'s `ConfState.Voters`; `[]` otherwise -/
  voters : List w64
  /-- `Context` (2026-10-12, for read-index): the bytes `Message.Context` holds; `[]`
  for every message but a heartbeat and its response carrying a read position -/
  ctx : List w8

section msgs
variable [FfiSyntax]

/-- A message with no voters -- every message but a `snap`. Reducible, the analogue of
Rocq's abbreviation: a message built with it is the constructor applied to `[]`, so
nothing that reduces, injects or rewrites a message has to unfold anything by hand
(added 2026-10-02 with the `voters` field, so that no user of the ten-field `Msg.mk`
changed). -/
@[reducible] def Msg.mk (t0 : MsgType) (fr to0 tm : w64) (rj : Bool) (ix lt cm rh : w64)
    (es : List raftpb.Entry) : Msg :=
  Msg.mkV t0 fr to0 tm rj ix lt cm rh es [] []

/-- A message with no payload: every replication field zero. -/
def Msg.plain (ty : MsgType) (src dst term : w64) (reject : Bool) : Msg :=
  Msg.mk ty src dst term reject (W64 0) (W64 0) (W64 0) (W64 0) []

end msgs

/-- Message types whose sender claims to be the leader of `term`. -/
def fromLeader : MsgType → Bool
  | .app | .heartbeat | .snap => true
  | _ => false

/-! ### The read-index state (2026-10-12; the records moved from `InvMisc.lean`)

A queued read-index request and the read-only object, as `InvMisc.lean`'s `ownReadOnly`
sees them. -/

structure ReadReq [FfiSyntax] where
  index : w64
  src : w64
  ents : List raftpb.Entry

/-- The read-only object. `pending`: `unconfirmedReads`, oldest first.
`acks`: each voter's acknowledged *position* -- the largest context (as a number) the
voter echoed in a heartbeat response; the context of a heartbeat is
`confirmed + length pending` at the time it was sent (`readonlyPosition`).
`confirmed`: `confirmedReads`, the number of requests ever removed from the front of
`pending`. The `option` (`ReadOnlySafe` or `ReadOnlyLeaseBased`) is not in it: no spec
states it (`stepLeader` reads the field and case-splits on the value; until
2026-10-08 a `safe` field recorded it). -/
structure ReadOnly [FfiSyntax] where
  pending : List ReadReq
  acks : GMap w64 w64
  confirmed : w64

/-- The physical read-index state (2026-10-12): `r.readStates` (as the Goose values),
`r.readOnly` (as `ReadOnly`), and `r.pendingReadIndexMessages`, each with the entries
its slice holds. -/
structure RdState [FfiSyntax] where
  states : List ReadState := []
  ro : ReadOnly := ⟨[], ∅, W64 0⟩
  pend : List (raftpb.Message × List raftpb.Entry) := []

/-- The read state with a fresh read-only object, what `reset` installs (and a non-leader's,
in the protocol reading). -/
def rdNL [FfiSyntax] (rd : RdState) : RdState := { rd with ro := ⟨[], ∅, W64 0⟩ }

@[simp] theorem rdNL_rdNL [FfiSyntax] (rd : RdState) : rdNL (rdNL rd) = rdNL rd := rfl

@[simp] theorem rdNL_ite [FfiSyntax] (c : Prop) [Decidable c] (rd : RdState) :
    rdNL (if c then rd else rdNL rd) = rdNL rd := by
  split <;> rfl

section readonly_fns
variable [FfiSyntax]

/-- Go's `min`/`max` builtins on `uint64`, exactly as Goose's `minⁱᵐᵖˡ`/`maxⁱᵐᵖˡ`
compute them: `min x y = if x < y then x else y`, `max x y = if x > y then x else y`
(and Goose renders `x > y` as `y < x`). Stated with `decide`, the form of the
framework's `wp_max2_uint64`. (Moved here from `InvTracker.lean` with the `Progress`
methods.) -/
def w64Min (x y : w64) : w64 := if uint.Z x < uint.Z y then x else y
def w64Max (x y : w64) : w64 := if uint.Z y < uint.Z x then x else y

theorem w64Min_spec (x y : w64) : uint.Z (w64Min x y) = min (uint.Z x) (uint.Z y) := by
  unfold w64Min; split <;> omega

theorem w64Max_spec (x y : w64) : uint.Z (w64Max x y) = max (uint.Z x) (uint.Z y) := by
  unfold w64Max; split <;> omega

/-- The position a heartbeat context encodes: `confirmedReads + len unconfirmedReads`
(wrapping, as the `uint64` sum does). -/
def readonlyPosition (r : ReadOnly) : w64 :=
  r.confirmed + W64 r.pending.length

/-- The position is at most the unwrapped sum. -/
theorem readonlyPosition_le (r : ReadOnly) :
    uint.nat (readonlyPosition r) ≤ uint.nat r.confirmed + r.pending.length := by
  unfold readonlyPosition
  have h1 : uint.nat (W64 r.pending.length) ≤ r.pending.length := by
    word
  have h2 : uint.nat (r.confirmed + W64 r.pending.length) ≤
      uint.nat r.confirmed + uint.nat (W64 r.pending.length) := by
    word
  omega

/-- `addRequest`: append to the queue. -/
def readonlyAdd (r : ReadOnly) (q : ReadReq) : ReadOnly :=
  { r with pending := r.pending ++ [q] }

/-- `recvAck from ctx`, `ctx` as the bytes it holds: nothing for an empty context, else
the voter's ack becomes the larger of its old one (`0` if none) and the first eight
bytes read little-endian. -/
def readonlyRecvAck (r : ReadOnly) (src : w64) (ctx : List w8) : ReadOnly :=
  if ctx = [] then r
  else { r with acks := <[src := w64Max ((r.acks !! src).getD (W64 0))
                                         (leToU64 (ctx.take 8))]> r.acks }

/-- `maybeAdvance`, given `N`, the quorum index of the voters' acks
(`CommittedIndex`): nothing when `N` is not past `confirmed`; else the first
`N - confirmed` requests leave the queue, `confirmed` becomes `N` and the removed
requests are returned. -/
def readonlyAdvance (r : ReadOnly) (N : w64) : ReadOnly × List ReadReq :=
  if uint.Z N ≤ uint.Z r.confirmed then (r, [])
  else
    let k := uint.nat (N - r.confirmed)
    ({ r with pending := r.pending.drop k, confirmed := N }, r.pending.take k)

/-- The context `heartbeatCtx` returns (2026-10-12): none for an empty queue, else the
position, little-endian. -/
def hbCtx (r : ReadOnly) : List w8 :=
  if r.pending = [] then [] else u64Le (readonlyPosition r)

/-- `sendMsgReadIndexResponse` on the read-only object (`ReadOnlySafe`): the request is
queued, then the leader acknowledges the new position itself. -/
def readonlyArrive (r : ReadOnly) (id : w64) (q : ReadReq) : ReadOnly :=
  readonlyRecvAck (readonlyAdd r q) id (hbCtx (readonlyAdd r q))

/-- `releasePendingReadIndexMessages` on the read-only object: each pending request
arrives, read at the commit index `c`, in order. -/
def readonlyRelease (r : ReadOnly) (id c : w64)
    (pend : List (raftpb.Message × List raftpb.Entry)) : ReadOnly :=
  pend.foldl (fun r p => readonlyArrive r id ⟨c, p.1.From', p.2⟩) r

/-- What an arrival does: the request queued, the leader's ack raised to the new
position. -/
theorem readonlyArrive_eq (r : ReadOnly) (id : w64) (q : ReadReq) :
    readonlyArrive r id q =
      { pending := r.pending ++ [q]
        acks := <[id := w64Max ((r.acks !! id).getD (W64 0))
                          (r.confirmed + W64 (r.pending ++ [q]).length)]> r.acks
        confirmed := r.confirmed } := by
  have hl : (u64Le (r.confirmed + W64 (r.pending ++ [q]).length)).length = 8 := u64Le_length _
  have hne : u64Le (r.confirmed + W64 (r.pending ++ [q]).length) ≠ [] := by
    intro h; rw [h] at hl; simp at hl
  unfold readonlyArrive readonlyRecvAck hbCtx readonlyAdd readonlyPosition
  simp only [List.append_eq_nil_iff, List.cons_ne_self, and_false, ↓reduceIte, hne,
    List.take_of_length_le (Nat.le_of_eq hl), u64Le_to_word]

end readonly_fns

/-! ## Protocol node state

`PState` is the **protocol** state of one node: what the state machine below and the
ghost state `ownRaftGhost` are about, and nothing more. It is *not* the abstraction
`ownRaftPhys` is indexed by -- that is the physical abstract state `NState`
(`Defs.lean`). The two are connected by `NStateRel` (`Defs.lean`); `Step`'s spec is the
one place that crosses from one to the other. See notes/decisions.md, "Three layers".

`outbox` is the node's pending outgoing messages — the abstraction of the Go code's
two queues, `r.msgs` and `r.msgsAfterAppend`, together.

`base`/`log`/`commit` are the log (`Plog.lean`): the compaction boundary, the entries
after it, `raftLog.committed`. `matched` is each voter's `Progress.Match` **while the
node is leader**, and `∅` otherwise (a non-leader's `Progress` values are left over
from its last leadership and nothing reads them). The field is not called `match`,
which is a keyword. -/

structure PState [FfiSyntax] where
  /-- `raft.Term` -/
  term : w64
  /-- `raft.Vote`; `W64 0` is the Go code's `None` -/
  vote : w64
  /-- `raft.lead`; `W64 0` is the Go code's `None` -/
  lead : w64
  /-- `raft.state` -/
  role : Role
  /-- `raft.trk.Votes` -/
  votes : GMap w64 Bool
  /-- `r.msgs` and `r.msgsAfterAppend`, together -/
  outbox : List Msg
  /-- the log's compaction boundary -/
  base : entryID
  /-- the entries after `base` -/
  log : List raftpb.Entry
  /-- `raftLog.committed` -/
  commit : w64
  /-- `Progress.Match` per voter, leaders only -/
  matched : GMap w64 w64
  /-- the read-index state (2026-10-12): the `ReadState`s, a leader's read-only object
  (fresh for a non-leader) and the pending requests -/
  rd : RdState := {}

/-! ### The client log (2026-10-10)

The data of committed client entries in commit order, first occurrences only: what
`cLog` (`GhostState.lean`) holds of the committed log, given each entry's data
(`none` for a leader's own entry). -/

/-- One entry's data added to the client log: a new data is appended; a repeated one, or
a leader's own entry (`none`), leaves it. -/
def occStep (L : List (List w8)) : Option (List w8) → List (List w8)
  | none => L
  | some d => if d ∈ L then L else L ++ [d]

def firstOcc (ods : List (Option (List w8))) : List (List w8) := ods.foldl occStep []

theorem firstOcc_snoc (ods : List (Option (List w8))) (o : Option (List w8)) :
    firstOcc (ods ++ [o]) = occStep (firstOcc ods) o := by
  simp [firstOcc, List.foldl_append]

theorem occStep_prefix (L : List (List w8)) (o : Option (List w8)) : L <+: occStep L o := by
  cases o with
  | none => exact List.prefix_refl _
  | some d =>
    by_cases h : d ∈ L
    · simp only [occStep, h, if_true]; exact List.prefix_refl _
    · simp only [occStep, h, if_false]; exact List.prefix_append _ _

theorem foldl_occStep_prefix (L : List (List w8)) (b : List (Option (List w8))) :
    L <+: b.foldl occStep L := by
  induction b generalizing L with
  | nil => exact List.prefix_refl _
  | cons o b ih => exact (occStep_prefix L o).trans (ih _)

theorem firstOcc_append_prefix (a b : List (Option (List w8))) :
    firstOcc a <+: firstOcc (a ++ b) := by
  unfold firstOcc; rw [List.foldl_append]; exact foldl_occStep_prefix _ _

theorem firstOcc_take_prefix (ods : List (Option (List w8))) (n : Nat) :
    firstOcc (ods.take n) <+: firstOcc ods := by
  have := firstOcc_append_prefix (ods.take n) (ods.drop n)
  rwa [List.take_append_drop] at this

theorem mem_foldl_occStep (L : List (List w8)) (b : List (Option (List w8))) (d : List w8) :
    d ∈ b.foldl occStep L ↔ d ∈ L ∨ some d ∈ b := by
  induction b generalizing L with
  | nil => simp
  | cons o b ih =>
    simp only [List.foldl_cons, List.mem_cons]
    rw [ih]
    cases o with
    | none => simp [occStep]
    | some d' =>
      by_cases h : d' ∈ L
      · simp only [occStep, h, if_true]
        constructor
        · rintro (h1 | h1)
          · exact .inl h1
          · exact .inr (.inr h1)
        · rintro (h1 | h1 | h1)
          · exact .inl h1
          · cases h1; exact .inl h
          · exact .inr h1
      · simp only [occStep, h, if_false, List.mem_append, List.mem_singleton]
        constructor
        · rintro ((h1 | h1) | h1)
          · exact .inl h1
          · subst h1; exact .inr (.inl rfl)
          · exact .inr (.inr h1)
        · rintro (h1 | h1 | h1)
          · exact .inl (.inl h1)
          · cases h1; exact .inl (.inr rfl)
          · exact .inr h1

theorem mem_firstOcc (ods : List (Option (List w8))) (d : List w8) :
    d ∈ firstOcc ods ↔ some d ∈ ods := by
  unfold firstOcc; rw [mem_foldl_occStep]; simp

theorem nodup_foldl_occStep (L : List (List w8)) (b : List (Option (List w8))) :
    L.Nodup → (b.foldl occStep L).Nodup := by
  induction b generalizing L with
  | nil => exact id
  | cons o b ih =>
    intro hL
    apply ih
    cases o with
    | none => exact hL
    | some d =>
      by_cases h : d ∈ L
      · simp only [occStep, h, if_true]; exact hL
      · simp only [occStep, h, if_false]
        exact List.nodup_append.mpr ⟨hL, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩,
          fun a ha b hb => by
            simp only [List.mem_singleton] at hb; subst hb; intro e; subst e; exact h ha⟩

theorem firstOcc_nodup (ods : List (Option (List w8))) : (firstOcc ods).Nodup :=
  nodup_foldl_occStep [] ods List.nodup_nil

/-- In a list without duplicates, what comes before `d` is determined. -/
theorem prefix_before_unique (L L0 L1 : List (List w8)) (d : List w8) (Hnd : L.Nodup)
    (H0 : L0 ++ [d] <+: L) (H1 : L1 ++ [d] <+: L) : L0 = L1 := by
  have k0 : L[L0.length]? = some d := by
    obtain ⟨r, rfl⟩ := H0; simp
  have k1 : L[L1.length]? = some d := by
    obtain ⟨r, rfl⟩ := H1; simp
  obtain ⟨h0lt, h0e⟩ := List.getElem?_eq_some_iff.mp k0
  obtain ⟨h1lt, h1e⟩ := List.getElem?_eq_some_iff.mp k1
  have hlen := (List.Nodup.getElem_inj Hnd).mp (h0e.trans h1e.symm)
  have e0 := List.prefix_iff_eq_take.mp ((List.prefix_append L0 [d]).trans H0)
  have e1 := List.prefix_iff_eq_take.mp ((List.prefix_append L1 [d]).trans H1)
  calc L0 = L.take L0.length := e0
    _ = L.take L1.length := by rw [hlen]
    _ = L1 := e1.symm

section pure
variable [FfiSyntax]

/-- `appendEntry`'s stamping loop: `es[k].Term = r.Term` and `es[k].Index = li+1+k`;
nothing else about an entry changes, which is what keeps `Type = EntryNormal` true of
the appended entries. (Moved here from `Defs.lean` on 2026-10-01: the model's
`Step.win` and `Step.propose` stamp too.)

An entry stamped at term `t` and index `i`: what a proposed (unstamped) entry `e0`
becomes in the log (`stamp` is the same at `i = li + 1 + k`). And the list position of
index `i` in a full log (from `base0`). -/
def stampAt (e0 : raftpb.Entry) (t i : w64) : raftpb.Entry :=
  { e0 with Term' := t, Index' := i }

def pos (i : w64) : Nat := (uint.Z i - 1).toNat

def stamp (tm li : w64) (k : Nat) (e : raftpb.Entry) : raftpb.Entry :=
  { e with Term' := tm, Index' := li + W64 1 + W64 k }

/-- Index arithmetic for stamped entries. -/
theorem plogLastIndexZ_nonneg (b : entryID) (es : List raftpb.Entry) :
    0 ≤ plogLastIndexZ b es := by
  unfold plogLastIndexZ; have := uint_Z_nonneg b.index'; omega

omit [FfiSyntax] in
theorem stamp_index_le (L : Int) (k : Nat) :
    0 ≤ L → uint.Z (W64 L + W64 1 + W64 (k : Int)) ≤ L + 1 + k := by
  intro HL
  simp only [uint.Z, W64, BitVec.toNat_add, BitVec.toNat_ofInt]
  omega

omit [FfiSyntax] in
theorem leader_index_le (L : Int) :
    0 ≤ L → uint.Z (W64 L + W64 1 + W64 0) ≤ L + 1 := by
  intro HL
  have H := stamp_index_le L 0 HL
  simpa using H

omit [FfiSyntax] in
theorem stamp_index_eq (L : Int) (k : Nat) :
    0 ≤ L → L + 1 + k < 2 ^ 64 →
    uint.Z (W64 L + W64 1 + W64 (k : Int)) = L + 1 + k := by
  intro HL Hlt
  simp only [uint.Z, W64, BitVec.toNat_add, BitVec.toNat_ofInt]
  omega

/-- What a receiver of an `app` needs of its batch (`raftLog.maybeAppend`'s premises):
consecutive indices from `index + 1`, no wrap, no conf change (phase-1 scope). -/
def AppPayloadOk (m : Msg) : Prop :=
  PlogWf (entryID.mk m.logterm m.index) m.entries ∧
  uint.Z m.index + (m.entries.length : Int) + 1 < 2 ^ 64 ∧
  ∀ e ∈ m.entries, e.Type' = W32 0

omit [FfiSyntax] in
/-- stdpp `drop_S`. -/
theorem list_drop_S {A : Type _} (l : List A) (d : Nat) (e : A) (h : l[d]? = some e) :
    l.drop d = e :: l.drop (d + 1) := by
  obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp h
  rw [List.drop_eq_getElem_cons hlt, heq]

omit [FfiSyntax] in
/-- stdpp `prefix_lookup_Some`. -/
theorem prefix_lookup_Some {A : Type _} {l1 l2 : List A} {k : Nat} {e : A}
    (hk : l1[k]? = some e) (h : l1 <+: l2) : l2[k]? = some e := by
  obtain ⟨t, rfl⟩ := h
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hk).1]; exact hk

/-- A prefix of a well-formed, no-wrap, conf-change-free log from `i + 1` on is a
batch `AppPayloadOk` accepts at `(t, i)`. -/
theorem app_payload_from_log (b : entryID) (L : List raftpb.Entry) (t i : w64)
    (es : List raftpb.Entry) :
    PlogWf b L →
    uint.Z b.index' + (L.length : Int) + 1 < 2 ^ 64 →
    (uint.Z b.index' ≤ uint.Z i ∧ uint.Z i ≤ plogLastIndexZ b L) →
    (∀ e ∈ L, e.Type' = W32 0) →
    es <+: plogFrom b L (i + W64 1) →
    PlogWf (entryID.mk t i) es ∧
    uint.Z i + (es.length : Int) + 1 < 2 ^ 64 ∧
    ∀ e ∈ es, e.Type' = W32 0 := by
  intro Hwf Hnw Hi HN Hpre
  unfold plogLastIndexZ at Hi
  unfold plogFrom at Hpre
  have Hadd : uint.Z (i + W64 1) = uint.Z i + 1 := by word
  rw [Hadd] at Hpre
  have Hlen := Hpre.length_le
  rw [List.length_drop] at Hlen
  refine ⟨fun j e Hj => ?_, by omega, fun e He => HN e (List.mem_of_mem_drop (Hpre.subset He))⟩
  have Hj' := prefix_lookup_Some Hj Hpre
  rw [List.getElem?_drop] at Hj'
  have := Hwf _ _ Hj'
  simp only
  push_cast at this ⊢
  omega

/-- The entry at index `i` of a log, if it is in the stored suffix. -/
def plogEntryAt (b : entryID) (es : List raftpb.Entry) (i : w64) : Option raftpb.Entry :=
  if uint.Z i ≤ uint.Z b.index' then none
  else es[(uint.Z i - uint.Z b.index' - 1).toNat]?

/-- `plogFindConflict` returns the index of the first entry that does not match, all
before it matching. -/
theorem plogFindConflict_some (b : entryID) (es ents : List raftpb.Entry) :
    plogFindConflict b es ents ≠ W64 0 →
    ∃ (d : Nat) (e : raftpb.Entry), ents[d]? = some e ∧
      e.Index' = plogFindConflict b es ents ∧
      ¬ PlogMatches b es (entId e) ∧
      (∀ (j : Nat) (e' : raftpb.Entry), j < d → ents[j]? = some e' →
        PlogMatches b es (entId e')) := by
  induction ents with
  | nil => intro h; exact absurd rfl h
  | cons a ents IH =>
    intro Hne
    by_cases Ha : PlogMatches b es (entId a)
    · have Heq : plogFindConflict b es (a :: ents) = plogFindConflict b es ents := by
        simp [plogFindConflict, Ha]
      rw [Heq] at Hne ⊢
      obtain ⟨d, e, Hd, He, Hnm, Hbef⟩ := IH Hne
      refine ⟨d + 1, e, by simpa using Hd, He, Hnm, ?_⟩
      intro j e' Hj Hj'
      cases j with
      | zero => simp at Hj'; subst Hj'; exact Ha
      | succ j => simp at Hj'; exact Hbef j e' (by omega) Hj'
    · have Heq : plogFindConflict b es (a :: ents) = a.Index' := by
        simp [plogFindConflict, Ha]
      rw [Heq]
      exact ⟨0, a, rfl, rfl, Ha, fun j _ Hj _ => absurd Hj (Nat.not_lt_zero _)⟩

/-- ... and `0` when every entry matches, provided no entry has index `0`. -/
theorem plogFindConflict_zero (b : entryID) (es ents : List raftpb.Entry) :
    (∀ (k : Nat) (e : raftpb.Entry), ents[k]? = some e → e.Index' ≠ W64 0) →
    plogFindConflict b es ents = W64 0 →
    ∀ (k : Nat) (e : raftpb.Entry), ents[k]? = some e → PlogMatches b es (entId e) := by
  induction ents with
  | nil => intro _ _ k e Hk; simp at Hk
  | cons a ents IH =>
    intro Hnz Hci k e Hk
    by_cases Ha : PlogMatches b es (entId a)
    · simp only [plogFindConflict, Ha, ↓reduceIte] at Hci
      cases k with
      | zero => simp at Hk; subst Hk; exact Ha
      | succ k =>
        simp at Hk
        exact IH (fun k e H => Hnz (k + 1) e (by simpa using H)) Hci k e Hk
    · simp only [plogFindConflict, Ha, ↓reduceIte] at Hci
      exact absurd Hci (Hnz 0 a rfl)

/-- The entries of a well-formed batch after `prev` have nonzero indices. -/
theorem batch_index_nz (prev : entryID) (ents : List raftpb.Entry) (Hwf : PlogWf prev ents) :
    ∀ (k : Nat) (e : raftpb.Entry), ents[k]? = some e → e.Index' ≠ W64 0 := by
  intro k e Hk Hz
  have := Hwf _ _ Hk
  rw [Hz] at this
  have h0 : uint.Z (W64 0 : w64) = 0 := by simp
  have := uint_Z_nonneg prev.index'
  push_cast at *; omega

/-- The conflicting entry `ents[d]` of `plogFindConflict_some`, after a matched `prev`,
is at most one past the log's end. -/
theorem conflict_end (b : entryID) (es : List raftpb.Entry) (prev : entryID)
    (ents : List raftpb.Entry) (d : Nat) (e : raftpb.Entry)
    (Hwf : PlogWf prev ents) (Hm : PlogMatches b es prev) (Hd : ents[d]? = some e)
    (Hbefore : ∀ (j : Nat) (e' : raftpb.Entry), j < d → ents[j]? = some e' →
        PlogMatches b es (entId e')) :
    uint.Z e.Index' ≤ plogLastIndexZ b es + 1 := by
  have Hed := Hwf _ _ Hd
  have ⟨_, Hl⟩ := plogTermAt_some_range _ _ _ _ Hm
  cases d with
  | zero => push_cast at Hed; omega
  | succ d' =>
    have Hlt := (List.getElem?_eq_some_iff.mp Hd).1
    obtain ⟨e', He'⟩ : ∃ e', ents[d']? = some e' :=
      ⟨ents[d'], List.getElem?_eq_getElem (by omega)⟩
    have Hme' := Hbefore d' e' (by omega) He'
    unfold PlogMatches entId at Hme'
    have ⟨_, Hle⟩ := plogTermAt_some_range _ _ _ _ Hme'
    have Hed' := Hwf _ _ He'
    simp only at Hle
    push_cast at Hed Hed'; omega

/-- After `plogMaybeAppend` of a well-formed, non-wrapping batch, the log reaches
`lastnewi`: the batch's entries are all there (no conflict), or the log was cut at the
first conflict and the rest of the batch appended. -/
theorem plogMaybeAppend_last (b : entryID) (es : List raftpb.Entry) (prev : entryID)
    (ents : List raftpb.Entry) (lastnewi : w64) (es' : List raftpb.Entry) :
    PlogWf prev ents →
    uint.Z prev.index' + (ents.length : Int) + 1 < 2 ^ 64 →
    plogMaybeAppend b es prev ents = some (lastnewi, es') →
    uint.Z lastnewi ≤ plogLastIndexZ b es' := by
  intro Hwf Hnw
  unfold plogMaybeAppend
  split
  case isFalse => intro h; cases h
  rename_i Hm
  intro H
  simp only [Option.some.injEq, Prod.mk.injEq] at H
  obtain ⟨rfl, rfl⟩ := H
  have := uint_Z_nonneg prev.index'
  rw [uint_Z_W64 _ (by omega) (by omega)]
  have ⟨Hb, Hl⟩ := plogTermAt_some_range _ _ _ _ Hm
  have Hnz := batch_index_nz prev ents Hwf
  split
  · -- no conflict: the last entry of the batch is in the log
    rename_i Hci
    by_cases H0 : ents.length = 0
    · rw [H0]; push_cast; exact Hl
    obtain ⟨e, He⟩ : ∃ e, ents[ents.length - 1]? = some e :=
      ⟨ents[ents.length - 1], List.getElem?_eq_getElem (by omega)⟩
    have Hme := plogFindConflict_zero _ _ _ Hnz Hci _ _ He
    unfold PlogMatches entId at Hme
    have ⟨_, Hle⟩ := plogTermAt_some_range _ _ _ _ Hme
    have := Hwf _ _ He
    simp only at Hle
    push_cast at this; omega
  · -- a conflict at batch position `d`: cut there, append the rest
    rename_i Hci
    obtain ⟨d, e, Hd, Hei, _, Hbefore⟩ := plogFindConflict_some _ _ _ Hci
    have Hed := Hwf _ _ Hd
    have Hend := conflict_end b es prev ents d e Hwf Hm Hd Hbefore
    have Hdrop : (uint.Z (plogFindConflict b es ents) - uint.Z prev.index' - 1).toNat = d := by
      rw [← Hei]; push_cast at Hed; omega
    rw [Hdrop, list_drop_S _ _ _ Hd]
    unfold plogTruncateAppend plogLastIndexZ
    simp only [List.length_append, List.length_take, List.length_cons, List.length_drop]
    have Hlt := (List.getElem?_eq_some_iff.mp Hd).1
    unfold plogLastIndexZ at Hend Hl
    push_cast at Hed ⊢
    omega

/-! ## Pure facts the replication-safety invariants rest on (2026-10-02)

See `LogOk`, `LogRecs` and `AckAgree` in the ghost part. -/

/-- Well-formedness *in range*: an entry whose position puts it at an index a `w64`
can name has that index. This is `PlogWf` minus the entries past `2^64 - 1`, which
only `Step.win` can create (its stamped entry wraps when `lastIndex() = 2^64 - 1`; the
rule has no no-wrap premise, and the code's `Hnowrap` is not in `PState`).
`plogTermAt` never reaches those positions, so nothing below needs more. -/
def PlogWfR (b : entryID) (es : List raftpb.Entry) : Prop :=
  ∀ (k : Nat) (e : raftpb.Entry), es[k]? = some e →
    uint.Z b.index' + (k : Int) + 1 < 2 ^ 64 →
    uint.Z e.Index' = uint.Z b.index' + (k : Int) + 1

theorem PlogWf_wfR (b : entryID) (es : List raftpb.Entry) : PlogWf b es → PlogWfR b es := by
  intro H k e Hk _
  have := H k e Hk
  push_cast at this; omega

/-- The index just before position `k` of the suffix: where the `k`-th entry's
predecessor is. -/
def pidx (b : entryID) (k : Nat) : w64 :=
  W64 (uint.Z b.index' + (k : Int))

theorem plogTermAt_app_l (b : entryID) (es es2 : List raftpb.Entry) (j : w64) :
    uint.Z j ≤ plogLastIndexZ b es →
    plogTermAt b (es ++ es2) j = plogTermAt b es j := by
  unfold plogTermAt plogLastIndexZ
  intro Hj
  split; · rfl
  split; · rfl
  rw [List.getElem?_append_left (by omega)]

theorem plogTermAt_app_r (b : entryID) (es es2 : List raftpb.Entry) (j : w64) :
    plogLastIndexZ b es < uint.Z j →
    plogTermAt b (es ++ es2) j =
      (fun e : raftpb.Entry => e.Term') <$>
        es2[(uint.Z j - plogLastIndexZ b es - 1).toNat]? := by
  unfold plogTermAt plogLastIndexZ
  intro Hj
  have := uint_Z_nonneg b.index'
  simp only [show ¬ (uint.Z j < uint.Z b.index') by omega,
    show ¬ (uint.Z j = uint.Z b.index') by omega, ↓reduceIte]
  rw [List.getElem?_append_right (by omega)]
  congr 2
  omega

theorem plogTermAt_take (b : entryID) (es : List raftpb.Entry) (n : Nat) (j : w64) :
    uint.Z j ≤ uint.Z b.index' + (n : Int) →
    plogTermAt b (es.take n) j = plogTermAt b es j := by
  unfold plogTermAt
  intro Hj
  split; · rfl
  split; · rfl
  rw [List.getElem?_take, ite_eq_left (by omega)]

theorem plogTermAt_in_range (b : entryID) (es : List raftpb.Entry) (j : w64) :
    (uint.Z b.index' ≤ uint.Z j ∧ uint.Z j ≤ plogLastIndexZ b es) →
    (plogTermAt b es j).isSome := by
  intro Hj
  cases H : plogTermAt b es j with
  | some _ => rfl
  | none =>
    have := (plogTermAt_none_range b es j).mp H
    omega

/-- Above the base, a term is an entry's, and (in range) the entry is at the right
index. -/
theorem plogTermAt_some_entry (b : entryID) (es : List raftpb.Entry) (j t : w64) :
    PlogWfR b es → plogTermAt b es j = some t →
    uint.Z b.index' < uint.Z j →
    ∃ e, es[(uint.Z j - uint.Z b.index' - 1).toNat]? = some e ∧
         e.Index' = j ∧ e.Term' = t := by
  intro Hwf Ht Hb
  unfold plogTermAt at Ht
  simp only [show ¬ (uint.Z j < uint.Z b.index') by omega,
    show ¬ (uint.Z j = uint.Z b.index') by omega, ↓reduceIte] at Ht
  cases He : es[(uint.Z j - uint.Z b.index' - 1).toNat]? with
  | none => rw [He] at Ht; cases Ht
  | some e =>
    rw [He] at Ht
    simp only [Option.map_eq_map, Option.map_some, Option.some.injEq] at Ht
    refine ⟨e, rfl, ?_, Ht⟩
    have := uint_Z_lt j
    have := Hwf _ _ He (by omega)
    apply uint_Z_inj.mp
    omega

theorem plogEntryAt_lookup (b : entryID) (es : List raftpb.Entry) (j : w64) :
    uint.Z b.index' < uint.Z j →
    plogEntryAt b es j = es[(uint.Z j - uint.Z b.index' - 1).toNat]? := by
  intro Hj
  unfold plogEntryAt
  rw [ite_eq_right (by omega)]

/-- The last entry's term, in range. -/
theorem plogTermAt_last_r (b : entryID) (es : List raftpb.Entry) :
    PlogWfR b es → plogLastIndexZ b es < 2 ^ 64 →
    plogTermAt b es (W64 (plogLastIndexZ b es)) = some (plogLast b es).term' := by
  intro Hwf Hlt
  have H0 := plogLastIndexZ_nonneg b es
  unfold plogLast
  cases Hl : es.getLast? with
  | some e =>
    have Hk := getLast?_some_getElem? es e Hl
    have Hne : es.length ≠ 0 := by
      intro h; rw [List.length_eq_zero_iff] at h; subst h; cases Hl
    apply plogTermAt_lookup b es _ _ e Hk
    unfold plogLastIndexZ at Hlt H0 ⊢
    rw [uint_Z_W64 _ H0 Hlt]
    push_cast; omega
  | none =>
    rw [List.getLast?_eq_none_iff] at Hl
    subst Hl
    have : W64 (plogLastIndexZ b []) = b.index' := by
      unfold plogLastIndexZ; apply uint_Z_inj.mp
      have := uint_Z_nonneg b.index'
      have := uint_Z_lt b.index'
      simp only [List.length_nil, Int.natCast_zero, Int.add_zero]
      exact uint_Z_W64 _ (by omega) (by omega)
    rw [this]
    exact plogTermAt_base b []

/-- What two logs' records give: entries at the same (term, index) are the same entry
and have the same predecessor term. `logRecs_agree` derives it from the ghost
state. -/
def RecsAgree (b1 : entryID) (es1 : List raftpb.Entry) (b2 : entryID)
    (es2 : List raftpb.Entry) : Prop :=
  ∀ (k1 k2 : Nat) (e1 e2 : raftpb.Entry), es1[k1]? = some e1 → es2[k2]? = some e2 →
    uint.Z b1.index' + (k1 : Int) + 1 < 2 ^ 64 →
    uint.Z b2.index' + (k2 : Int) + 1 < 2 ^ 64 →
    e1.Term' = e2.Term' →
    e1.Index' = e2.Index' →
    e1 = e2 ∧ plogTermAt b1 es1 (pidx b1 k1) = plogTermAt b2 es2 (pidx b2 k2)

/-- Log matching, pure: two logs with the same term at `i` have the same terms all the
way down to the higher of their bases. -/
theorem plog_match_down (b1 : entryID) (es1 : List raftpb.Entry) (b2 : entryID)
    (es2 : List raftpb.Entry) (i : w64) :
    PlogWfR b1 es1 → PlogWfR b2 es2 → RecsAgree b1 es1 b2 es2 →
    (plogTermAt b1 es1 i).isSome →
    plogTermAt b1 es1 i = plogTermAt b2 es2 i →
    ∀ j : w64, uint.Z b1.index' ≤ uint.Z j →
      uint.Z b2.index' ≤ uint.Z j → uint.Z j ≤ uint.Z i →
      plogTermAt b1 es1 j = plogTermAt b2 es2 j := by
  intro Hwf1 Hwf2 HRA Hs Heq j Hj1 Hj2 Hji
  suffices H : ∀ (n : Nat) (i : w64), (uint.Z i - uint.Z j).toNat = n →
      (plogTermAt b1 es1 i).isSome → plogTermAt b1 es1 i = plogTermAt b2 es2 i →
      uint.Z j ≤ uint.Z i → plogTermAt b1 es1 j = plogTermAt b2 es2 j from
    H _ i rfl Hs Heq Hji
  intro n
  induction n with
  | zero =>
    intro i Hn _ Heq Hji
    have : i = j := uint_Z_inj.mp (by omega)
    subst this; exact Heq
  | succ n IH =>
    intro i Hn Hs Heq Hji
    obtain ⟨t, Ht⟩ := Option.isSome_iff_exists.mp Hs
    have := uint_Z_nonneg b1.index'
    have := uint_Z_nonneg b2.index'
    have := uint_Z_lt i
    have := uint_Z_lt j
    have Hi1 : uint.Z b1.index' < uint.Z i := by omega
    have Hi2 : uint.Z b2.index' < uint.Z i := by omega
    obtain ⟨e1, He1, Hidx1, Ht1⟩ := plogTermAt_some_entry _ _ _ _ Hwf1 Ht Hi1
    have Ht' : plogTermAt b2 es2 i = some t := by rw [← Heq]; exact Ht
    obtain ⟨e2, He2, Hidx2, Ht2⟩ := plogTermAt_some_entry _ _ _ _ Hwf2 Ht' Hi2
    obtain ⟨_, Hpt⟩ := HRA _ _ _ _ He1 He2 (by omega) (by omega)
      (by rw [Ht1, Ht2]) (by rw [Hidx1, Hidx2])
    have Hi' : uint.Z (W64 (uint.Z i - 1)) = uint.Z i - 1 :=
      uint_Z_W64 _ (by omega) (by omega)
    have Hp1 : pidx b1 (uint.Z i - uint.Z b1.index' - 1).toNat = W64 (uint.Z i - 1) := by
      unfold pidx
      rw [show uint.Z b1.index' + ((uint.Z i - uint.Z b1.index' - 1).toNat : Int)
        = uint.Z i - 1 by omega]
    have Hp2 : pidx b2 (uint.Z i - uint.Z b2.index' - 1).toNat = W64 (uint.Z i - 1) := by
      unfold pidx
      rw [show uint.Z b2.index' + ((uint.Z i - uint.Z b2.index' - 1).toNat : Int)
        = uint.Z i - 1 by omega]
    rw [Hp1, Hp2] at Hpt
    apply IH (W64 (uint.Z i - 1)) (by omega) _ Hpt (by omega)
    apply plogTermAt_in_range
    have := plogTermAt_some_range _ _ _ _ Ht
    omega

/-- A batch `ents` after `prev`, taken from a log `l` (a prefix of `l`'s entries after
`prev`, which `l` has), agrees with `l` in terms on `[prev.index, prev.index +
|ents|]`. -/
theorem plog_prefix_batch (bL : entryID) (l : List raftpb.Entry) (prev : entryID)
    (ents : List raftpb.Entry) :
    uint.Z prev.index' + (ents.length : Int) + 1 < 2 ^ 64 →
    plogTermAt bL l prev.index' = some prev.term' →
    ents <+: plogFrom bL l (prev.index' + W64 1) →
    ∀ j : w64, uint.Z prev.index' ≤ uint.Z j →
      uint.Z j ≤ uint.Z prev.index' + (ents.length : Int) →
      plogTermAt bL l j = plogTermAt prev ents j := by
  intro Hnw Hprev Hpre j Hj1 Hj2
  have ⟨Hb, _⟩ := plogTermAt_some_range _ _ _ _ Hprev
  by_cases Heq : uint.Z j = uint.Z prev.index'
  · have : j = prev.index' := uint_Z_inj.mp Heq
    subst this
    rw [Hprev, plogTermAt_base]
  have Hlt : (uint.Z j - uint.Z prev.index' - 1).toNat < ents.length := by omega
  obtain ⟨x, Hx⟩ : ∃ x, ents[(uint.Z j - uint.Z prev.index' - 1).toNat]? = some x :=
    ⟨_, List.getElem?_eq_getElem Hlt⟩
  have Hx' := prefix_lookup_Some Hx Hpre
  unfold plogFrom at Hx'
  rw [List.getElem?_drop] at Hx'
  have Hadd : uint.Z (prev.index' + W64 1) = uint.Z prev.index' + 1 := by word
  rw [Hadd] at Hx'
  rw [plogTermAt_lookup prev ents j _ x Hx (by push_cast; omega)]
  rw [plogTermAt_lookup bL l j _ x Hx' (by push_cast; omega)]

/-- `plogMaybeAppend`, taken apart: the previous entry matched, the new last index is
the batch's, and either nothing changed (every entry matched) or the log was cut at
the first conflicting entry `ents[d]` and the batch from `d` on appended. -/
theorem plogMaybeAppend_inv (b : entryID) (es : List raftpb.Entry) (prev : entryID)
    (ents : List raftpb.Entry) (lastnewi : w64) (es' : List raftpb.Entry) :
    PlogWf prev ents →
    uint.Z prev.index' + (ents.length : Int) + 1 < 2 ^ 64 →
    plogMaybeAppend b es prev ents = some (lastnewi, es') →
    PlogMatches b es prev ∧
    uint.Z lastnewi = uint.Z prev.index' + (ents.length : Int) ∧
    ( (es' = es ∧ ∀ (k : Nat) (e : raftpb.Entry), ents[k]? = some e →
          PlogMatches b es (entId e))
    ∨ (∃ (d : Nat) (e : raftpb.Entry), ents[d]? = some e ∧ ¬ PlogMatches b es (entId e) ∧
         (∀ (k : Nat) (e' : raftpb.Entry), k < d → ents[k]? = some e' →
            PlogMatches b es (entId e')) ∧
         uint.Z e.Index' = uint.Z prev.index' + (d : Int) + 1 ∧
         uint.Z e.Index' ≤ plogLastIndexZ b es + 1 ∧
         es' = es.take (uint.Z e.Index' - uint.Z b.index' - 1).toNat ++ ents.drop d) ) := by
  intro Hwf Hnw
  unfold plogMaybeAppend
  split
  case isFalse => intro h; cases h
  rename_i Hm
  intro H
  simp only [Option.some.injEq, Prod.mk.injEq] at H
  obtain ⟨rfl, rfl⟩ := H
  have := uint_Z_nonneg prev.index'
  refine ⟨Hm, uint_Z_W64 _ (by omega) (by omega), ?_⟩
  have Hnz := batch_index_nz prev ents Hwf
  split
  · rename_i Hci
    exact .inl ⟨rfl, plogFindConflict_zero _ _ _ Hnz Hci⟩
  · rename_i Hci
    obtain ⟨d, e, Hd, Hei, Hnm, Hbefore⟩ := plogFindConflict_some _ _ _ Hci
    have Hed := Hwf _ _ Hd
    push_cast at Hed
    refine .inr ⟨d, e, Hd, Hnm, Hbefore, by omega,
      conflict_end b es prev ents d e Hwf Hm Hd Hbefore, ?_⟩
    rw [← Hei]
    have : (uint.Z e.Index' - uint.Z prev.index' - 1).toNat = d := by omega
    rw [this, list_drop_S _ _ _ Hd]
    rfl

/-- The batch's entries, by index. -/
theorem batch_lookup (prev : entryID) (ents : List raftpb.Entry) (j : w64) :
    PlogWf prev ents →
    (uint.Z prev.index' < uint.Z j ∧
      uint.Z j ≤ uint.Z prev.index' + (ents.length : Int)) →
    ∃ x, ents[(uint.Z j - uint.Z prev.index' - 1).toNat]? = some x ∧
         x.Index' = j ∧ plogTermAt prev ents j = some x.Term' := by
  intro Hwf Hj
  have Hlt : (uint.Z j - uint.Z prev.index' - 1).toNat < ents.length := by omega
  refine ⟨_, List.getElem?_eq_getElem Hlt, ?_, ?_⟩
  · have := Hwf _ _ (List.getElem?_eq_getElem Hlt)
    apply uint_Z_inj.mp
    push_cast at this; omega
  · exact plogTermAt_lookup _ _ _ _ _ (List.getElem?_eq_getElem Hlt) (by push_cast; omega)

/-- After `plogMaybeAppend`, the log has the batch's terms on `[prev.index, prev.index
+ |ents|]`. -/
theorem plogMaybeAppend_batch (b : entryID) (es : List raftpb.Entry) (prev : entryID)
    (ents : List raftpb.Entry) (lastnewi : w64) (es' : List raftpb.Entry) :
    PlogWf prev ents →
    uint.Z prev.index' + (ents.length : Int) + 1 < 2 ^ 64 →
    plogMaybeAppend b es prev ents = some (lastnewi, es') →
    ∀ j : w64, uint.Z prev.index' ≤ uint.Z j →
      uint.Z j ≤ uint.Z prev.index' + (ents.length : Int) →
      plogTermAt b es' j = plogTermAt prev ents j := by
  intro Hwf Hnw Happ j Hj1 Hj2
  obtain ⟨Hm, _, Hcase⟩ := plogMaybeAppend_inv _ _ _ _ _ _ Hwf Hnw Happ
  have ⟨Hb, Hl⟩ := plogTermAt_some_range _ _ _ _ Hm
  -- below the conflict (or everywhere, without one), the old log has the batch's terms
  have Hold : ∀ (d : Nat), (∀ (k : Nat) (e' : raftpb.Entry), k < d → ents[k]? = some e' →
        PlogMatches b es (entId e')) →
      uint.Z j ≤ uint.Z prev.index' + (d : Int) →
      plogTermAt b es j = plogTermAt prev ents j := by
    intro d Hbef Hjd
    by_cases Heq : uint.Z j = uint.Z prev.index'
    · have : j = prev.index' := uint_Z_inj.mp Heq
      subst this
      rw [plogTermAt_base]; exact Hm
    · obtain ⟨x, Hx, Hxi, Hxt⟩ := batch_lookup prev ents j Hwf ⟨by omega, Hj2⟩
      rw [Hxt]
      have Hmx := Hbef _ x (by omega) Hx
      unfold PlogMatches entId at Hmx
      simp only at Hmx
      rw [Hxi] at Hmx
      exact Hmx
  rcases Hcase with ⟨rfl, Hall⟩ | ⟨d, e, Hd, _, Hbefore, Hei, Hend, rfl⟩
  · exact Hold ents.length (fun k e' _ Hk => Hall k e' Hk) (by omega)
  · have Hdlt := (List.getElem?_eq_some_iff.mp Hd).1
    unfold plogLastIndexZ at Hend Hl
    have Hlt : plogLastIndexZ b (es.take (uint.Z e.Index' - uint.Z b.index' - 1).toNat)
        = uint.Z e.Index' - 1 := by
      unfold plogLastIndexZ; rw [List.length_take]; omega
    by_cases Hjc : uint.Z j < uint.Z e.Index'
    · rw [plogTermAt_app_l _ _ _ _ (by omega), plogTermAt_take _ _ _ _ (by omega)]
      exact Hold d Hbefore (by omega)
    · rw [plogTermAt_app_r _ _ _ _ (by omega), Hlt, List.getElem?_drop]
      obtain ⟨x, Hx, _, Hxt⟩ := batch_lookup prev ents j Hwf ⟨by omega, Hj2⟩
      rw [Hxt]
      have : d + (uint.Z j - (uint.Z e.Index' - 1) - 1).toNat =
          (uint.Z j - uint.Z prev.index' - 1).toNat := by omega
      rw [this, Hx]
      rfl

/-- Below the cut the log is unchanged. -/
theorem plog_cut_keep (b : entryID) (es : List raftpb.Entry) (ci : Int)
    (ents2 : List raftpb.Entry) (j : w64) :
    (uint.Z b.index' < ci ∧ ci ≤ plogLastIndexZ b es + 1) →
    uint.Z j < ci →
    plogTermAt b (es.take (ci - uint.Z b.index' - 1).toNat ++ ents2) j = plogTermAt b es j := by
  intro Hci Hj
  unfold plogLastIndexZ at Hci
  rw [plogTermAt_app_l]
  · rw [plogTermAt_take]; omega
  · unfold plogLastIndexZ; rw [List.length_take]; omega

theorem plog_cut_last (b : entryID) (es : List raftpb.Entry) (ci : Int)
    (ents2 : List raftpb.Entry) :
    (uint.Z b.index' < ci ∧ ci ≤ plogLastIndexZ b es + 1) →
    plogLastIndexZ b (es.take (ci - uint.Z b.index' - 1).toNat ++ ents2)
      = ci - 1 + (ents2.length : Int) := by
  intro Hci
  unfold plogLastIndexZ at Hci ⊢
  rw [List.length_append, List.length_take]
  omega

/-- `plogMaybeAppend` keeps the log well-formed (in range), and the new log reaches
`lastnewi` -- exactly, when it was cut. -/
theorem plogMaybeAppend_wfR (b : entryID) (es : List raftpb.Entry) (prev : entryID)
    (ents : List raftpb.Entry) (lastnewi : w64) (es' : List raftpb.Entry) :
    PlogWfR b es →
    PlogWf prev ents →
    uint.Z prev.index' + (ents.length : Int) + 1 < 2 ^ 64 →
    plogMaybeAppend b es prev ents = some (lastnewi, es') →
    PlogWfR b es' ∧ uint.Z lastnewi ≤ plogLastIndexZ b es' := by
  intro Hwfr Hwf Hnw Happ
  have Hlast := plogMaybeAppend_last _ _ _ _ _ _ Hwf Hnw Happ
  obtain ⟨Hm, _, Hcase⟩ := plogMaybeAppend_inv _ _ _ _ _ _ Hwf Hnw Happ
  have ⟨Hb, Hl⟩ := plogTermAt_some_range _ _ _ _ Hm
  rcases Hcase with ⟨rfl, _⟩ | ⟨d, e, Hd, _, _, Hei, Hend, rfl⟩
  · exact ⟨Hwfr, Hlast⟩
  refine ⟨?_, Hlast⟩
  unfold plogLastIndexZ at Hend
  have Hn : (uint.Z e.Index' - uint.Z b.index' - 1).toNat ≤ es.length := by omega
  intro k x Hk Hr
  by_cases Hkn : k < (uint.Z e.Index' - uint.Z b.index' - 1).toNat
  · rw [List.getElem?_append_left (by rw [List.length_take]; omega),
      List.getElem?_take, ite_eq_left Hkn] at Hk
    exact Hwfr k x Hk Hr
  · rw [List.getElem?_append_right (by rw [List.length_take]; omega),
      List.length_take, List.getElem?_drop] at Hk
    have := Hwf _ _ Hk
    push_cast at this; omega

/-! ## Full logs (2026-10-03)

Leader Completeness compares logs *below* their compaction boundaries: a voter's log at
vote time against a candidate's, a follower's after a snapshot against the leader's.
The ghost state therefore keeps, for each log `(b, es)`, the compacted prefix `fp`
(entries `1 .. b.index`, the last one `b`) with its records, and reasons about the
**full log** `fp ++ es` from the fixed base `base0`. `FullOk` is the link; the lemmas
below translate `plogTermAt`/`plogLast` between the two views. (`PlogWf base0 F`
already puts every entry of a full log at a `w64` index: nothing in it has wrapped.) -/

def base0 : entryID := entryID.mk (W64 0) (W64 0)

def FullOk (b : entryID) (fp : List raftpb.Entry) : Prop :=
  (fp.length : Int) = uint.Z b.index' ∧
  PlogWf base0 fp ∧ plogLast base0 fp = b

theorem base0_index : uint.Z (base0 : entryID).index' = 0 := rfl

theorem FullOk_base0 : FullOk base0 [] :=
  ⟨rfl, fun _ _ h => by simp at h, rfl⟩

theorem full_term_at (b : entryID) (fp es : List raftpb.Entry) (j : w64) :
    FullOk b fp → uint.Z b.index' ≤ uint.Z j →
    plogTermAt base0 (fp ++ es) j = plogTermAt b es j := by
  intro ⟨Hlen, _, Hlast⟩ Hj
  have H0 := base0_index
  unfold plogTermAt
  rw [H0]
  have := uint_Z_nonneg j
  simp only [show ¬ (uint.Z j < 0) by omega, show ¬ (uint.Z j < uint.Z b.index') by omega,
    ↓reduceIte]
  by_cases Hj0 : uint.Z j = 0
  · -- the empty prefix: `b = base0`
    have Hfp : fp = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst Hfp
    simp only [plogLast, List.getLast?_nil] at Hlast
    subst Hlast
    rw [H0, List.nil_append]
  rw [ite_eq_right Hj0]
  by_cases Hjb : uint.Z j = uint.Z b.index'
  · rw [ite_eq_left Hjb]
    rw [List.getElem?_append_left (by omega)]
    unfold plogLast at Hlast
    cases Hx : fp.getLast? with
    | some x =>
      rw [Hx] at Hlast
      have Hk := getLast?_some_getElem? fp x Hx
      have : (uint.Z j - 0 - 1).toNat = fp.length - 1 := by omega
      rw [this, Hk]
      subst Hlast; rfl
    | none =>
      rw [List.getLast?_eq_none_iff] at Hx
      subst Hx; simp at Hlen; omega
  · rw [ite_eq_right Hjb, List.getElem?_append_right (by omega)]
    congr 2
    omega

theorem full_term_at_le (b : entryID) (fp es : List raftpb.Entry) (j : w64) :
    FullOk b fp → uint.Z j ≤ uint.Z b.index' →
    plogTermAt base0 (fp ++ es) j = plogTermAt base0 fp j := by
  intro ⟨Hlen, _, _⟩ Hj
  apply plogTermAt_app_l
  unfold plogLastIndexZ; rw [base0_index]; omega

theorem full_last (b : entryID) (fp es : List raftpb.Entry) :
    FullOk b fp → plogLast base0 (fp ++ es) = plogLast b es := by
  intro ⟨_, _, Hlast⟩
  unfold plogLast at *
  rw [List.getLast?_append]
  cases es.getLast? with
  | some _ => rfl
  | none => simp only [Option.none_or]; exact Hlast

theorem full_last_index (b : entryID) (fp es : List raftpb.Entry) :
    FullOk b fp → plogLastIndexZ base0 (fp ++ es) = plogLastIndexZ b es := by
  intro ⟨Hlen, _, _⟩
  unfold plogLastIndexZ; rw [base0_index, List.length_append]; push_cast; omega

theorem full_up_to_date (b : entryID) (fp es : List raftpb.Entry) (x : entryID) :
    FullOk b fp → plogUpToDate base0 (fp ++ es) x = plogUpToDate b es x := by
  intro H
  unfold plogUpToDate; rw [full_last _ _ _ H]

theorem full_wf (b : entryID) (fp es : List raftpb.Entry) :
    FullOk b fp → PlogWf b es → PlogWf base0 (fp ++ es) := by
  intro ⟨Hlen, Hwf, _⟩ Hwfe
  rw [PlogWf_app]
  refine ⟨Hwf, fun k e Hk => ?_⟩
  have := Hwfe k e Hk
  rw [base0_index]; omega

/-- In range, `PlogWfR` is `PlogWf`. -/
theorem PlogWfR_wf (b : entryID) (es : List raftpb.Entry) :
    PlogWfR b es → plogLastIndexZ b es < 2 ^ 64 → PlogWf b es := by
  intro Hwf Hr k e Hk
  have Hlt := (List.getElem?_eq_some_iff.mp Hk).1
  unfold plogLastIndexZ at Hr
  have := Hwf k e Hk (by omega)
  push_cast; omega

/-- ... and a `PlogWf` log is in range. -/
theorem PlogWf_range (b : entryID) (es : List raftpb.Entry) :
    PlogWf b es → plogLastIndexZ b es < 2 ^ 64 := by
  intro Hwf
  unfold plogLastIndexZ
  by_cases H0 : es.length = 0
  · rw [H0]; have := uint_Z_lt b.index'; push_cast; omega
  have := Hwf _ _ (List.getElem?_eq_getElem (l := es) (i := es.length - 1) (by omega))
  have := uint_Z_lt (es[es.length - 1]'(by omega)).Index'
  push_cast at *; omega

/-- The prefix of a full log up to `i`, as the compacted prefix of the log with base
`(t, i)`. -/
theorem FullOk_take (F : List raftpb.Entry) (t i : w64) :
    PlogWf base0 F → plogTermAt base0 F i = some t →
    FullOk (entryID.mk t i) (F.take (uint.Z i).toNat) := by
  intro Hwf Ht
  have ⟨_, Hle⟩ := plogTermAt_some_range _ _ _ _ Ht
  unfold plogLastIndexZ at Hle
  rw [base0_index] at Hle
  have := uint_Z_nonneg i
  refine ⟨?_, PlogWf_take _ _ _ Hwf, ?_⟩
  · simp only [List.length_take]; omega
  · unfold plogLast
    by_cases H0 : uint.Z i = 0
    · unfold plogTermAt at Ht
      rw [base0_index] at Ht
      simp only [H0, show ¬ ((0 : Int) < 0) by omega, ↓reduceIte, Option.some.injEq] at Ht
      subst Ht
      rw [H0]
      simp only [Int.toNat_zero, List.take_zero, List.getLast?_nil]
      unfold base0; congr 1
      exact (uint_Z_inj.mp (by rw [H0]; rfl)).symm
    · rw [List.getLast?_eq_getElem?, List.length_take]
      have Hmin : min (uint.Z i).toNat F.length - 1 = (uint.Z i - 0 - 1).toNat := by omega
      rw [Hmin, List.getElem?_take, ite_eq_left (by omega)]
      unfold plogTermAt at Ht
      rw [base0_index] at Ht
      simp only [show ¬ (uint.Z i < 0) by omega, H0, ↓reduceIte] at Ht
      cases Hx : F[(uint.Z i - 0 - 1).toNat]? with
      | none => rw [Hx] at Ht; cases Ht
      | some x =>
        rw [Hx] at Ht
        simp only [Option.map_eq_map, Option.map_some, Option.some.injEq] at Ht
        subst Ht
        simp only [entId]
        congr 1
        have := Hwf _ _ Hx
        rw [base0_index] at this
        apply uint_Z_inj.mp
        push_cast at this; omega

theorem plogTermAt_take_full (F : List raftpb.Entry) (n : Nat) (j : w64) :
    uint.Z j ≤ (n : Int) → plogTermAt base0 (F.take n) j = plogTermAt base0 F j := by
  intro Hj
  apply plogTermAt_take
  rw [base0_index]; omega

/-- A full log is defined everywhere up to its end. -/
theorem full_term_at_some (F : List raftpb.Entry) (j k : w64) :
    (plogTermAt base0 F k).isSome → uint.Z j ≤ uint.Z k →
    (plogTermAt base0 F j).isSome := by
  intro Hs Hjk
  obtain ⟨x, Hx⟩ := Option.isSome_iff_exists.mp Hs
  apply plogTermAt_in_range
  have := plogTermAt_some_range _ _ _ _ Hx
  have := uint_Z_nonneg j
  rw [base0_index] at *
  omega

/-- Prefixes keep the terms they have. -/
theorem plogTermAt_prefix (b : entryID) (F0 F : List raftpb.Entry) (j : w64) :
    F0 <+: F → (plogTermAt b F0 j).isSome →
    plogTermAt b F j = plogTermAt b F0 j := by
  intro ⟨F', HF⟩ Hs
  subst HF
  obtain ⟨x, Hx⟩ := Option.isSome_iff_exists.mp Hs
  apply plogTermAt_app_l
  exact (plogTermAt_some_range _ _ _ _ Hx).2

/-- The pure side of a campaign record (`isCamp`, 2026-10-03): a well-formed full log
all of whose terms are below the campaign's. -/
def CampOk (T : w64) (F : List raftpb.Entry) : Prop :=
  PlogWf base0 F ∧
  ∀ (j x : w64), plogTermAt base0 F j = some x → uint.Z x < uint.Z T

/-- What an entry's record says of its predecessor term `pt` (`isEntryR`): the entry,
at index `k`, is past the leader's campaign log `F0`; it follows `F0`'s last entry or
one of its own term; `pt ≤ T`. -/
def PtOk (F0 : List raftpb.Entry) (T : w64) (k : Int) (pt : w64) : Prop :=
  plogLastIndexZ base0 F0 < k ∧ uint.Z pt ≤ uint.Z T ∧
  (k = plogLastIndexZ base0 F0 + 1 → pt = (plogLast base0 F0).term') ∧
  (plogLastIndexZ base0 F0 + 1 < k → pt = T)

end pure

section model
variable [FfiSyntax]

-- `cfg` is the (fixed) set of voters; `id` the node being described.
variable (cfg : GSet w64) (id : w64)

def IsQuorum (q : GSet w64) : Prop := size cfg < 2 * size (q ∩ cfg)

omit [FfiSyntax] in
/-- Two quorums meet. This is the whole content of election safety; the same lemma,
for the same `IsQuorum`, is proved in `readonly.lean`. -/
theorem quorums_intersect (q1 q2 : GSet w64) :
    IsQuorum cfg q1 → IsQuorum cfg q2 → ∃ x, x ∈ q1 ∧ x ∈ q2 := by
  intro Hsize1 Hsize2
  by_cases Hempty : q1 ∩ q2 = ∅
  · exfalso
    have Hunion : (q1 ∩ cfg) ∪ (q2 ∩ cfg) ⊆ cfg := by
      rw [GMap.elem_of_subseteq]; set_solver
    have Hdisj : (q1 ∩ cfg) ## (q2 ∩ cfg) := by
      rw [GMap.elem_of_disjoint]
      intro x h1 h2
      rw [GMap.elem_of_intersection] at h1 h2
      have : x ∈ q1 ∩ q2 := (GMap.elem_of_intersection _ _ _).mpr ⟨h1.1, h2.1⟩
      rw [Hempty] at this
      exact GMap.not_elem_of_empty _ this
    have Hle := GMap.subseteq_size Hunion
    rw [GMap.size_union Hdisj] at Hle
    unfold IsQuorum at *
    omega
  · obtain ⟨x, Hx⟩ := GMap.set_choose_L _ Hempty
    exact ⟨x, by set_solver, by set_solver⟩

def granted (votes : GMap w64 Bool) : GSet w64 :=
  domSet (filter (fun _ v => v) votes)

def rejected (votes : GMap w64 Bool) : GSet w64 :=
  domSet (filter (fun _ v => !v) votes)

/-- Putting messages on the network. -/
def psendMsgs (s : PState) (ms : List Msg) : PState :=
  { s with outbox := s.outbox ++ ms }

theorem psendMsgs_outbox (s : PState) (ms : List Msg) :
    (psendMsgs s ms).outbox = s.outbox ++ ms := rfl
theorem psendMsgs_term (s : PState) (ms : List Msg) : (psendMsgs s ms).term = s.term := rfl
theorem psendMsgs_role (s : PState) (ms : List Msg) : (psendMsgs s ms).role = s.role := rfl
theorem psendMsgs_votes (s : PState) (ms : List Msg) : (psendMsgs s ms).votes = s.votes := rfl
theorem psendMsgs_log (s : PState) (ms : List Msg) : (psendMsgs s ms).log = s.log := rfl
theorem psendMsgs_commit (s : PState) (ms : List Msg) :
    (psendMsgs s ms).commit = s.commit := rfl
theorem psendMsgs_matched (s : PState) (ms : List Msg) :
    (psendMsgs s ms).matched = s.matched := rfl
theorem psendMsgs_base (s : PState) (ms : List Msg) : (psendMsgs s ms).base = s.base := rfl

/-- `lastIndex()` of the log, as a `w64`. -/
def plastIndex (s : PState) : w64 :=
  W64 (plogLastIndexZ s.base s.log)

/-! ## Role transitions

These mirror the Go code exactly. `reset(term)` clears `Vote` only when the term
actually changes, always clears `lead` and the vote tally; the `becomeX` wrappers then
set `lead` and `state`. None of them sends, so all three carry the outbox across
unchanged, and none touches the log. A non-leader's `matched` is `∅` (see `PState`); a
new leader's is whatever `reset` left, which `Step.win` pins with `LeaderMatchOk`. -/

def pbecomeFollower (s : PState) (term lead : w64) : PState where
  term := term
  vote := if term = s.term then s.vote else W64 0
  lead := lead
  role := .follower
  votes := ∅
  outbox := s.outbox
  base := s.base
  log := s.log
  commit := s.commit
  matched := ∅
  rd := rdNL s.rd

def pbecomeCandidate (s : PState) : PState where
  term := s.term + W64 1
  vote := id
  lead := W64 0
  role := .candidate
  votes := ∅
  outbox := s.outbox
  base := s.base
  log := s.log
  commit := s.commit
  matched := ∅
  rd := rdNL s.rd

def pbecomeLeader (s : PState) (mt : GMap w64 w64) : PState where
  term := s.term
  vote := s.vote
  lead := id
  role := .leader
  votes := ∅
  outbox := s.outbox
  base := s.base
  log := s.log
  commit := s.commit
  matched := mt
  rd := rdNL s.rd

/-- What `reset` leaves in `Progress.Match` (`raft.go:779-808`): `0` for every voter,
then `lastIndex()` for the node itself. Stated without the voter set: a `0` claims
nothing. -/
def LeaderMatchOk (s : PState) (mt : GMap w64 w64) : Prop :=
  mt !! id = some (plastIndex s) ∧
  ∀ v x, v ≠ id → mt !! v = some x → x = W64 0

/-- The empty entry a new leader appends (`pb.Entry{Data: nil}`, the zero `Entry`),
stamped at the leader's term and the log's next index; the protocol reading of
`leaderEntry` (`Defs.lean`). -/
def pleaderEntry (s : PState) : raftpb.Entry :=
  stamp s.term (plastIndex s) 0 (zero_val raftpb.Entry)

def pappend (s : PState) (es : List raftpb.Entry) : PState :=
  { s with log := s.log ++ es }

/-- A candidate that has just won: `becomeLeader` up to its `send`. -/
def pwinState (s : PState) (mt : GMap w64 w64) : PState :=
  pappend (pbecomeLeader id s mt) [pleaderEntry s]

/-- `appendEntry`'s self-acknowledgement: a `MsgAppResp` to itself at the new last
index, which `Step(MsgAppResp)` later turns into the leader's own `Match`. -/
def pselfAck (s : PState) : Msg :=
  Msg.mk .appResp id id s.term false (plastIndex s) (W64 0) (W64 0) (W64 0) []

/-- `campaign`'s vote request to `dst`, carrying the last entry id it read (`Index:
last.index, LogTerm: last.term`). -/
def pvoteReq (dst term : w64) (last : entryID) : Msg :=
  Msg.mk .vote id dst term false last.index' last.term' (W64 0) (W64 0) []

/-- Receiving a message from the leader of the current term: `stepFollower`'s
`r.lead = m.From` or `stepCandidate`'s `becomeFollower(m.Term, m.From)`, which agree on
`PState` (a follower's `votes` are `∅`; the vote is kept at the same term). -/
def padoptLeader (s : PState) (src : w64) : PState :=
  { s with lead := src, role := .follower, votes := ∅, matched := ∅ }

def matchOf (s : PState) (v : w64) : w64 :=
  (s.matched !! v).getD (W64 0)

/-- The voters whose `Match` is at least `n`. -/
def ackedBy (s : PState) (n : w64) : GSet w64 :=
  domSet (filter (fun _ x => decide (uint.Z n ≤ uint.Z x)) s.matched)

/-- `raft.trk.RecordVote`: the first vote recorded for a node wins; later ones are
dropped. -/
def recordVote (votes : GMap w64 Bool) (src : w64) (v : Bool) : GMap w64 Bool :=
  match votes !! src with
  | some _ => votes
  | none => <[src := v]> votes

/-- A node may grant its vote to `src` in its current term when it has not already
voted for somebody else and does not currently recognise a leader. -/
def PCanVote (s : PState) (src : w64) : Prop :=
  s.vote = src ∨ (s.vote = W64 0 ∧ s.lead = W64 0)

/-- A node that is not leader never records itself as the leader. An invariant of
every reachable state (`ownRaftGhost` carries it): the rules that adopt a sender as
leader (`Step.higherTerm` for a `fromLeader` message, `Step.app*`, `Step.heartbeat`)
require the sender to be another node, `Step.campaign`/`Step.lose` clear `lead`, and
`pbecomeLeader` sets it only together with `Role.leader`. `Step` needs it for a
forwarded proposal: `send` `Panicf`s on a message to oneself (`stepFollower`'s
`MsgProp` premise `lead ≠ id`). -/
def LeadOk (s : PState) : Prop :=
  s.role ≠ .leader → s.lead ≠ id

/-- A follower's vote tally is empty. Also an invariant (`ownRaftGhost` carries it):
every rule that makes a follower clears the tally (`pbecomeFollower`, `padoptLeader`),
and `Step.recordVote` needs a candidate. `Step` needs it where the code and the model
take different routes to the same follower: a follower at the current term receiving
`MsgApp`/`MsgHeartbeat` runs `r.lead = m.From`, leaving the tally alone, where
`padoptLeader` sets it to `∅`. -/
def FollowerVotesOk (s : PState) : Prop :=
  s.role = .follower → s.votes = ∅

/-- What a leader's `MsgApp` says (`maybeSendAppend`: `Index: pr.Next-1, LogTerm:
term(pr.Next-1), Entries: entries(pr.Next, maxMsgSize), Commit: committed`).

`(index, logterm)` is an entry of the leader's log (`raftLog.term` pins the term it
returns), and the entries are the leader's from `index + 1` on, cut short
(`raftLog.entries` / `raftLog.slice` return a prefix of the log from the index asked
for). `AppPayloadOk` is what a receiver needs of the batch itself
(`raftLog.maybeAppend`'s premises); the sender has it from its own log's
well-formedness, no-wrap and no-conf-change facts (`app_payload_from_log`), and
`isMessage` carries it. -/
def AppOk (s : PState) (m : Msg) : Prop :=
  m.ty = .app ∧ m.src = id ∧ m.term = s.term ∧
  m.dst ≠ id ∧
  plogTermAt s.base s.log m.index = some m.logterm ∧
  uint.Z m.commit ≤ uint.Z s.commit ∧
  (∀ e ∈ m.entries, e ∈ s.log) ∧
  m.entries <+: plogFrom s.base s.log (m.index + W64 1) ∧
  AppPayloadOk m

/-- `maybeSendSnapshot`'s `MsgSnap`: from the leader of the current term, carrying the
metadata `(logterm, index)` of the snapshot `raftLog.snapshot` returned (`absSnap`,
`Defs.lean`): non-empty, **at or below the commit index, and an entry id of the
leader's log** -- the log has `logterm` at `index`, possibly as its base.

The last two are conjuncts since 2026-10-03. They are what a receiver needs
(`isMessage`'s `snap` case: `isCommittedIdx index` and the leader-prefix fact at
`(logterm, index)`), and `snapOk_message` builds that from them. The sender has them
from `raftLog.snapshot`'s spec: a pending snapshot is the log's own base; a `Storage`
snapshot is the storage's current one, which `ownRaftLog` keeps at or below
`committed` and in the log (`StoredSnapOk`, `InvRaftlog.lean`). The voters are not
constrained here (the receiver's `Step` takes them as a transport premise). -/
def SnapOk (s : PState) (m : Msg) : Prop :=
  m.ty = .snap ∧ m.src = id ∧ m.term = s.term ∧
  m.dst ≠ id ∧ m.index ≠ W64 0 ∧
  uint.Z m.index ≤ uint.Z s.commit ∧
  plogTermAt s.base s.log m.index = some m.logterm

/-- What `maybeSendAppend` may send: an `app`, or (when the log no longer has what the
peer needs) a `snap`. -/
def ReplOk (s : PState) (m : Msg) : Prop := AppOk id s m ∨ SnapOk id s m

/-- `sendHeartbeat`: `Commit: min(pr.Match, committed)`. -/
def HeartbeatOk (s : PState) (m : Msg) : Prop :=
  m.ty = .heartbeat ∧ m.src = id ∧ m.term = s.term ∧
  m.dst ≠ id ∧
  uint.Z m.commit ≤ uint.Z s.commit ∧
  uint.Z m.commit ≤ uint.Z (matchOf s m.dst)

/-! ## The transition relation

`Step s recv s'` says: a node in state `s`, making use of the already-sent messages
`recv`, may move to state `s'`. Messages the node itself sends are not a separate
output: they are the growth of `s'.outbox`.

Reflexivity and transitivity are part of the relation so that a single Go function
which performs several protocol steps refines a single `Step`. -/

/-! ### Read-index (2026-10-13)

A confirmed request is answered (`responseToReadIndexReq`): a local one (from `0`, or from
the leader itself) becomes a `ReadState` whose context is its entry's data, a forwarded one
a `MsgReadIndexResp` to its sender carrying its entries. `N` is acknowledged by a quorum
when a quorum's acks are at least `N` (what `maybeAdvance`'s `CommittedIndex` gives). -/

def preadRespond (s : PState) (q : ReadReq) : PState :=
  if q.src = W64 0 ∨ q.src = id then
    match q.ents with
    | e :: _ => { s with rd := { s.rd with states := s.rd.states ++ [⟨q.index, e.Data'⟩] } }
    | [] => s
  else psendMsgs s [Msg.mk .readIndexResp id q.src s.term false q.index (W64 0) (W64 0)
                      (W64 0) q.ents]

def preadRespondAll (s : PState) (qs : List ReadReq) : PState :=
  qs.foldl (preadRespond id) s

/-- Answering changes only the outbox and the read state. -/
theorem preadRespond_eq (s : PState) (q : ReadReq) :
    ∃ o r, preadRespond id s q = { s with outbox := o, rd := r } := by
  unfold preadRespond
  split
  · split
    · exact ⟨_, _, rfl⟩
    · exact ⟨s.outbox, s.rd, by cases s; rfl⟩
  · exact ⟨_, _, rfl⟩

theorem preadRespondAll_eq (s : PState) (qs : List ReadReq) :
    ∃ o r, preadRespondAll id s qs = { s with outbox := o, rd := r } := by
  unfold preadRespondAll
  induction qs generalizing s with
  | nil => exact ⟨s.outbox, s.rd, by cases s; rfl⟩
  | cons q qs ih =>
    rw [List.foldl_cons]
    obtain ⟨o1, r1, h1⟩ := preadRespond_eq id s q
    rw [h1]
    obtain ⟨o, r, h⟩ := ih { s with outbox := o1, rd := r1 }
    exact ⟨o, r, h⟩

def QuorumAcked (f : w64 → w64) (N : w64) : Prop :=
  ∃ Q, IsQuorum cfg Q ∧ ∀ v ∈ Q, uint.Z N ≤ uint.Z (f v)

inductive Step : PState → List Msg → PState → Prop where
  /-- Structural rules. -/
  | refl (s : PState) : Step s [] s
  | trans (s₀ : PState) (r₁ : List Msg) (s₁ : PState) (r₂ : List Msg) (s₂ : PState) :
      Step s₀ r₁ s₁ → Step s₁ r₂ s₂ → Step s₀ (r₁ ++ r₂) s₂
  /-- `Step`'s term preamble: a message from a higher term makes the node step down.
  It adopts the sender as leader exactly when the message is one only a leader sends.

  The third premise: a leader's message is from another node (`send` never queues a
  leader message to oneself), so adopting its sender keeps `LeadOk`. -/
  | higherTerm (m : Msg) (s : PState) :
      uint.Z s.term < uint.Z m.term →
      m.dst = id →
      (fromLeader m.ty = true → m.src ≠ id) →
      Step s [m] (pbecomeFollower s m.term (if fromLeader m.ty then m.src else W64 0))
  /-- `hup` / `campaign`: a non-leader starts an election. It increments its term,
  votes for itself, and sends a `MsgVote` to every other voter plus a self-addressed
  `MsgVoteResp` (which the Go code routes through `msgsAfterAppend`). Each request
  carries the candidate's last entry id (`Index: last.index, LogTerm: last.term`):
  `campaign` reads `lastEntryID()` once per peer, and nothing in between changes the
  log.

  The no-wrap premise: the term increments, and a term that wrapped round to one the
  node has already voted in would let it vote twice in that term. -/
  | campaign (s : PState) (peers : List w64) :
      s.role ≠ .leader →
      id ∈ cfg →
      uint.Z s.term + 1 < 2 ^ 64 →
      peers ≡ₚ elements (cfg \ {[id]}) →
      Step s []
        (psendMsgs (pbecomeCandidate id s)
          ([Msg.plain .voteResp id id (pbecomeCandidate id s).term false] ++
           peers.map (fun dst => pvoteReq id dst (pbecomeCandidate id s).term
                                   (plogLast s.base s.log))))
  /-- Granting a vote: the candidate's last entry, as the request reports it, is at
  least as recent as ours (`raftLog.isUpToDate`). Leader completeness rests on this
  check.

  `W64 0` is the Go code's `None`, so a vote *for* it is not a vote at all. -/
  | grantVote (m : Msg) (s : PState) :
      m.ty = .vote →
      m.dst = id →
      m.src ≠ W64 0 →
      m.term = s.term →
      PCanVote s m.src →
      plogUpToDate s.base s.log (entryID.mk m.logterm m.index) = true →
      Step s [m]
        (psendMsgs { s with vote := m.src } [Msg.plain .voteResp id m.src s.term false])
  /-- Refusing a vote. Always legal. -/
  | rejectVote (m : Msg) (s : PState) :
      m.ty = .vote →
      m.dst = id →
      Step s [m] (psendMsgs s [Msg.plain .voteResp id m.src s.term true])
  /-- `stepCandidate` / `poll`: record a vote response for the current term. -/
  | recordVote (m : Msg) (s : PState) :
      m.ty = .voteResp →
      m.dst = id →
      m.term = s.term →
      s.role = .candidate →
      Step s [m] { s with votes := recordVote s.votes m.src (!m.reject) }
  /-- Winning: a quorum of grants makes the candidate leader (`becomeLeader`: `reset`,
  whose `Match` values `LeaderMatchOk` pins, then `appendEntry` of the empty entry,
  which queues the self-acknowledgement), and it immediately broadcasts
  (`bcastAppend`).

  The broadcast is deliberately loose: **any** list of messages `maybeSendAppend` may
  send, including none at all; see `Spec/raft__bcastAppend.lean` for why one per peer
  would be false.

  The no-wrap premise: the leader's entry, at `lastIndex() + 1`, does not wrap: the
  code's `ownRaftLog` `Hnowrap` of the candidate's log (2026-10-03; without it a
  wrapped entry, at index `0`, makes `isUpToDate` wrong and Leader Completeness false
  at `2^64` entries). -/
  | win (s : PState) (mt : GMap w64 w64) (ms : List Msg) :
      s.role = .candidate →
      IsQuorum cfg (granted s.votes) →
      plogLastIndexZ s.base s.log + 1 < 2 ^ 64 →
      LeaderMatchOk id s mt →
      (∀ m ∈ ms, ReplOk id (pwinState id s mt) m) →
      Step s [] (psendMsgs (pwinState id s mt) ([pselfAck id (pwinState id s mt)] ++ ms))
  /-- Losing: `VoteLost` is "the voters who have not rejected are not a quorum" (see
  the 2026-09 history in notes/false-statements.md). -/
  | lose (s : PState) :
      s.role = .candidate →
      ¬ IsQuorum cfg (cfg \ rejected s.votes) →
      Step s [] (pbecomeFollower s s.term (W64 0))
  /-- `Ready` hands the pending messages to the transport, emptying the queues.
  Dropping messages from one's own outbox is always legal. -/
  | drain (s : PState) (o' : List Msg) :
      o'.Subperm s.outbox →
      Step s [] { s with outbox := o' }

  /- ### Log replication (phase 1 of notes/raft-replication-model.md)

  Every rule below is about a message of the node's current term: a higher-term
  message has already been through `Step.higherTerm`. -/

  /-- `handleAppendEntries`, accepting: `maybeAppend` matched `(logterm, index)`. The
  log becomes `plogMaybeAppend`'s, `committed` moves to `min(m.Commit, lastnewi)`
  (never back), and the node acknowledges `lastnewi`. The conflict premise (Rocq's
  `let ci := plogFindConflict … in ci = W64 0 ∨ …`, inlined) is what makes
  `maybeAppend`'s `Panicf` dead; `app_no_conflict_below_commit` is the protocol
  fact. -/
  | appAccept (m : Msg) (s : PState) (lastnewi : w64) (es' : List raftpb.Entry) :
      m.ty = .app →
      m.dst = id →
      m.src ≠ id →
      m.term = s.term →
      s.role ≠ .leader →
      uint.Z s.commit ≤ uint.Z m.index →
      plogMaybeAppend s.base s.log (entryID.mk m.logterm m.index) m.entries
        = some (lastnewi, es') →
      (plogFindConflict s.base s.log m.entries = W64 0 ∨
        uint.Z s.commit < uint.Z (plogFindConflict s.base s.log m.entries)) →
      Step s [m]
        (psendMsgs
          { padoptLeader s m.src with
              log := es',
              commit := plogCommitTo s.commit
                          (if uint.Z m.commit < uint.Z lastnewi then m.commit else lastnewi) }
          [Msg.mk .appResp id m.src s.term false lastnewi (W64 0) (W64 0) (W64 0) []])
  /-- `handleAppendEntries`, `a.prev.index < committed`: acknowledge the commit
  index. -/
  | appStale (m : Msg) (s : PState) :
      m.ty = .app →
      m.dst = id →
      m.src ≠ id →
      m.term = s.term →
      s.role ≠ .leader →
      uint.Z m.index < uint.Z s.commit →
      Step s [m]
        (psendMsgs (padoptLeader s m.src)
          [Msg.mk .appResp id m.src s.term false s.commit (W64 0) (W64 0) (W64 0) []])
  /-- `handleAppendEntries`, rejecting: the log does not have `(logterm, index)`. The
  hint is an optimisation; any is allowed. -/
  | appReject (m : Msg) (s : PState) (hint hintterm : w64) :
      m.ty = .app →
      m.dst = id →
      m.src ≠ id →
      m.term = s.term →
      s.role ≠ .leader →
      uint.Z s.commit ≤ uint.Z m.index →
      ¬ PlogMatches s.base s.log (entryID.mk m.logterm m.index) →
      Step s [m]
        (psendMsgs (padoptLeader s m.src)
          [Msg.mk .appResp id m.src s.term true m.index hintterm (W64 0) hint []])
  /-- `handleHeartbeat`: `commitTo(m.Commit)`, whose `Panicf` the premise rules out
  (`heartbeat_commit_le_last`). The response echoes the heartbeat's context (2026-10-12):
  a read-index position, which the leader counts as an acknowledgement. -/
  | heartbeat (m : Msg) (s : PState) :
      m.ty = .heartbeat →
      m.dst = id →
      m.src ≠ id →
      m.term = s.term →
      s.role ≠ .leader →
      uint.Z m.commit ≤ plogLastIndexZ s.base s.log →
      Step s [m]
        (psendMsgs
          { padoptLeader s m.src with commit := plogCommitTo s.commit m.commit }
          [{ Msg.plain .heartbeatResp id m.src s.term false with ctx := m.ctx }])
  /-- `MsgBeat` / `bcastHeartbeat`: any heartbeats `HeartbeatOk` allows, with the read-only
  object's context (2026-10-13). -/
  | beat (s : PState) (ms : List Msg) :
      s.role = .leader →
      (∀ m ∈ ms, HeartbeatOk id s m) →
      (∀ m ∈ ms, m.ctx = hbCtx s.rd.ro) →
      Step s [] (psendMsgs s ms)
  /-- `stepLeader`'s `MsgAppResp`, accepting: `pr.MaybeUpdate(m.Index)` raises the
  sender's `Match`. A *rejecting* `appResp` changes no protocol state (`MaybeDecrTo`
  moves `Next`, not `Match`): `Step.refl`. -/
  | appResp (m : Msg) (s : PState) (x : w64) :
      m.ty = .appResp →
      m.dst = id →
      m.term = s.term →
      s.role = .leader →
      m.reject = false →
      s.matched !! m.src = some x →
      Step s [m]
        { s with matched :=
            <[m.src := if uint.Z x < uint.Z m.index then m.index else x]> s.matched }
  /-- `maybeCommit`: a quorum's `Match` reaches `n`, and the entry there is of the
  leader's own term. -/
  | commit (s : PState) (n : w64) :
      s.role = .leader →
      uint.Z s.commit < uint.Z n →
      uint.Z n ≤ plogLastIndexZ s.base s.log →
      plogTermAt s.base s.log n = some s.term →
      IsQuorum cfg (ackedBy s n) →
      Step s [] { s with commit := n }
  /-- `bcastAppend` / `sendAppend` outside an election win. -/
  | sendApps (s : PState) (ms : List Msg) :
      s.role = .leader →
      (∀ m ∈ ms, ReplOk id s m) →
      Step s [] (psendMsgs s ms)
  /-- `MsgProp` at the leader: `appendEntry` of the batch, which queues the
  self-acknowledgement. `EntryNormal` only: no conf change in phase 1. The proposal is
  received (2026-10-10): its `isMessage` carries each entry's data (`entData`).

  The third premise: the stamped indices do not wrap (`appendEntry`'s `Hsmall` and the
  log's own bound give it). Rocq's `let s' := pappend s (imap …) in` is inlined. -/
  | propose (m : Msg) (s : PState) (ents : List raftpb.Entry) :
      m.ty = .propose →
      m.entries = ents →
      s.role = .leader →
      (∀ e ∈ ents, e.Type' = W32 0) →
      plogLastIndexZ s.base s.log + (ents.length : Int) < 2 ^ 64 →
      Step s [m]
        (psendMsgs (pappend s (ents.mapIdx (stamp s.term (plastIndex s))))
          [pselfAck id (pappend s (ents.mapIdx (stamp s.term (plastIndex s))))])
  /-- `MsgProp` at a follower that knows a leader: forwarded, with `Term` left at `0`
  (`send`'s `MsgProp` exception) and `From` stamped. -/
  | propForward (m : Msg) (s : PState) :
      m.ty = .propose →
      s.role = .follower →
      s.lead ≠ W64 0 →
      Step s [m]
        (psendMsgs s
          [Msg.mkV .propose id s.lead (W64 0) m.reject m.index m.logterm m.commit
             m.rejecthint m.entries [] m.ctx])

  /- ### Snapshots (phase 2 of notes/raft-replication-model.md)

  `handleSnapshot` (raft.go:1827) after `stepFollower`'s `r.lead = m.From` /
  `stepCandidate`'s `becomeFollower(m.Term, m.From)` -- the leader is adopted, as for
  an `app` (`padoptLeader`). `restore(s)` (raft.go:1849) returns `false` when
  `Metadata.Index ≤ committed` (`Step.snapStale`); when the node is not a follower
  (dead: both callers have just made it one); when `r.id` is in none of the
  `ConfState`'s sets (dead under the fixed voter set: the voters are `cfg` and
  `id ∈ cfg`, premises below); and when the log already has `(Term, Index)`, after
  `commitTo(Index)` (`Step.snapFastfwd`). Otherwise the log is replaced by the snapshot
  (`Step.snapRestore`). The reply is `MsgAppResp{Index: lastIndex()}` after a restore
  -- `Index`, the unstable log being empty at offset `Index + 1` -- and
  `MsgAppResp{Index: committed}` otherwise: `Index` after the fast-forward, the old
  commit index when stale. The voter premise is on the message's `voters`: under the
  fixed-voter-set scope `Step` takes it as a transport premise. -/

  /-- `restore` proper: `raftLog.restore` makes the snapshot the compaction boundary,
  with nothing after it, and commits it. -/
  | snapRestore (m : Msg) (s : PState) :
      m.ty = .snap →
      m.dst = id →
      m.src ≠ id →
      m.term = s.term →
      s.role ≠ .leader →
      m.voters ≡ₚ elements cfg →
      id ∈ cfg →
      uint.Z s.commit < uint.Z m.index →
      ¬ PlogMatches s.base s.log (entryID.mk m.logterm m.index) →
      Step s [m]
        (psendMsgs
          { padoptLeader s m.src with
              base := entryID.mk m.logterm m.index, log := [], commit := m.index }
          [Msg.mk .appResp id m.src s.term false m.index (W64 0) (W64 0) (W64 0) []])
  /-- The log already has the snapshot's last entry: `commitTo(Index)` only. -/
  | snapFastfwd (m : Msg) (s : PState) :
      m.ty = .snap →
      m.dst = id →
      m.src ≠ id →
      m.term = s.term →
      s.role ≠ .leader →
      m.voters ≡ₚ elements cfg →
      id ∈ cfg →
      uint.Z s.commit < uint.Z m.index →
      PlogMatches s.base s.log (entryID.mk m.logterm m.index) →
      Step s [m]
        (psendMsgs { padoptLeader s m.src with commit := m.index }
          [Msg.mk .appResp id m.src s.term false m.index (W64 0) (W64 0) (W64 0) []])
  /-- An obsolete snapshot: acknowledge the commit index. -/
  | snapStale (m : Msg) (s : PState) :
      m.ty = .snap →
      m.dst = id →
      m.src ≠ id →
      m.term = s.term →
      s.role ≠ .leader →
      uint.Z m.index ≤ uint.Z s.commit →
      Step s [m]
        (psendMsgs (padoptLeader s m.src)
          [Msg.mk .appResp id m.src s.term false s.commit (W64 0) (W64 0) (W64 0) []])

  /-- `acceptReady` (2026-10-13): the `ReadState`s are handed out with the `Ready`
  (`r.readStates = nil`). -/
  | takeReads (s : PState) :
      Step s [] ({ s with rd := { s.rd with states := [] } })

  /- ### Read-index (2026-10-13; `notes/decisions.md`, "Read-index")

  A request carries a read credit (`rdOwn`), which `Step`'s refinement takes with it. -/

  /-- `stepFollower`'s `MsgReadIndex`: forwarded to the leader, from the node itself for a
  local request (`From = 0`). (No leader: dropped, `Step.refl`.) -/
  | readFwd (m : Msg) (s : PState) :
      m.ty = .readIndex → s.role ≠ .leader → s.lead ≠ W64 0 →
      Step s [m] (psendMsgs s [{ m with
        src := if m.src = W64 0 then id else m.src
        dst := s.lead
        term := W64 0 }])
  /-- `stepLeader`'s `MsgReadIndex` before an entry of the term is committed: pending. -/
  | readPend (m : Msg) (s : PState) (pm : raftpb.Message) :
      m.ty = .readIndex → s.role = .leader → m.src = pm.From' →
      Step s [m] ({ s with rd := { s.rd with pend := s.rd.pend ++ [(pm, m.entries)] } })
  /-- `sendMsgReadIndexResponse`: the request queued at the commit index, which is at an
  entry of the term, and acknowledged by the leader itself. -/
  | readArrive (m : Msg) (s : PState) :
      m.ty = .readIndex → s.role = .leader →
      plogTermAt s.base s.log s.commit = some s.term →
      Step s [m] ({ s with rd := { s.rd with
                     ro := readonlyArrive s.rd.ro id ⟨s.commit, m.src, m.entries⟩ } })
  /-- `releasePendingReadIndexMessages`: the pending requests arrive, in order. -/
  | readRelease (s : PState) :
      s.role = .leader → plogTermAt s.base s.log s.commit = some s.term →
      Step s [] ({ s with rd := { s.rd with
        pend := []
        ro := readonlyRelease s.rd.ro id s.commit s.rd.pend } })
  /-- `stepLeader`'s `MsgHeartbeatResp` with a context: the sender's acknowledgement,
  then the requests up to a position a quorum acknowledged confirmed and answered. -/
  | readAck (m : Msg) (s : PState) (N : w64) :
      m.ty = .heartbeatResp → m.dst = id → m.term = s.term → s.role = .leader →
      m.ctx ≠ [] →
      QuorumAcked cfg (fun v => ((readonlyRecvAck s.rd.ro m.src m.ctx).acks !! v).getD (W64 0))
        N →
      Step s [m] (preadRespondAll id
        ({ s with rd := { s.rd with
             ro := (readonlyAdvance (readonlyRecvAck s.rd.ro m.src m.ctx) N).1 } })
        (readonlyAdvance (readonlyRecvAck s.rd.ro m.src m.ctx) N).2)
  /-- `stepFollower`'s `MsgReadIndexResp`: a `ReadState`. -/
  | readState (m : Msg) (s : PState) (e : raftpb.Entry) :
      m.ty = .readIndexResp → m.entries = [e] →
      Step s [m] ({ s with rd := { s.rd with states := s.rd.states ++ [⟨m.index, e.Data'⟩] } })

  /- ### Pre-vote (phase 3, 2026-10-04)

  Pre-vote is an implementation detail: the protocol does not model it
  (notes/raft-replication-model.md, "Phase 3 ... Pre-vote"). What a pre-vote does to
  protocol state is covered by these rules and the existing ones (`Step.campaign` for
  the real election a won pre-vote starts, `Step.higherTerm` for a rejecting
  `preVoteResp` of a higher term). -/

  /-- Sending a pre-vote message, which carries nothing (`MsgFree`; that definition is
  in the ghost part, so the premise names the two types): a `preVote` at the next
  term, a `preVoteResp` either way. -/
  | sendFree (s : PState) (m : Msg) :
      (m.ty = .preVote ∨ m.ty = .preVoteResp) →
      m.src = id →
      Step s [] (psendMsgs s [m])
  /-- A non-leader that (pre-)campaigns, or a pre-candidate that loses, is a follower
  at the same term with no leader, keeping its vote (`becomePreCandidate`: `lead :=
  None`, the tally reset). For a candidate this is `Step.lose` without the quorum
  premise; a follower forgets its leader. -/
  | abandon (s : PState) :
      s.role ≠ .leader →
      Step s [] (pbecomeFollower s s.term (W64 0))
  /-- `Step`'s stale-term arm with pre-vote on: a `MsgApp`/`MsgHeartbeat` from a lower
  term is answered with `MsgAppResp{To: m.From}` -- `Term` stamped, `Index = 0`, which
  acknowledges nothing (`isAcked` at `0` holds for free). -/
  | zeroAck (s : PState) (dst : w64) :
      Step s [] (psendMsgs s [Msg.mk .appResp id dst s.term false
                                (W64 0) (W64 0) (W64 0) (W64 0) []])

end model

end EtcdGrove
end Perennial

-- Projection lemmas, `@[simp, word_unfold]` (ProjSimps.lean).
proj_simps Perennial.EtcdGrove.psendMsgs Perennial.EtcdGrove.pappend Perennial.EtcdGrove.padoptLeader
