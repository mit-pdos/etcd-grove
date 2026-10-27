/-
Port of `election_proof/inv_misc.v` (at 857d09190): raft components election neither
reads nor writes.

Lean notes: Rocq's section variable `cfg` is not used by anything in this file, so it
is dropped (in Rocq it is not a parameter of these definitions either, since they do
not mention it). `raft.readOnly.t`, `raft.ReadState.t`, `raft.ReadOnlyOption.t` and
`raft.readIndexRequest.t` are `readOnly`, `ReadState`, `ReadOnlyOption` and
`readIndexRequest`; Rocq's `list loc` / `own_slice_cap loc` for `unconfirmedReads` is
`List Loc` / `ownSliceCap Loc`. The records `readreq.t` and `readonly.t` are `ReadReq`
and `ReadOnly` (fields lowerCamel; `readreq.from` is `ReadReq.src`, `from` being a Lean
keyword, as `Msg.src`). `le_to_u64` is `leToU64`.

Raft v3.7 (retarget stage R4, `notes/decisions.md`, "`raft.go` over pointer messages"): a
`readIndexRequest` holds a `*pb.Message` and `pendingReadIndexMessages` is a `[]*pb.Message`;
both hold their request messages **frozen** (`msgOwn l □ st`, persistent, as the old
`req.Entries ↦*□` were): nothing writes a stored request (`responseToReadIndexReq` reads `From`
and shares `Entries`). The record's pair (`ReadReq`'s `src`/`ents`, `RdState.pend`'s
`(MessageM × List EntryM)`) is what the message holds; its snapshot, context and responses are
existential.
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftlog
public import Proof.go_etcd_io.raft.v3.InvTracker
public import Proof.go_etcd_io.raft.v3.InvPbMsg

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-! ## The read-only object's records (2026-10-04; here and not in `Defs.lean` so that
adding them does not invalidate the log and tracker proofs)

`ownReadOnly ro r` is indexed by `ReadOnly`, not by the Goose `readOnly` struct
(notes/raft-replication-model.md, "Public representation predicates"): exactly the
state the five methods' specs (`addRequest`, `recvAck`, `AckedIndex`, `maybeAdvance`,
`heartbeatCtx`) and `reset`/`stepLeader` (the `option`) read.

A queued read-index request is the part of `readIndexRequest` anyone reads back: the
commit index at the time, the requester (`req.From`, which `responseToReadIndexReq`
compares with `r.id`) and the request's entries (`req.Entries[0].Data` is the context
of a local read, and a forwarded request's response carries `req.Entries` whole). The
message's other fields are never read after queueing. The entries are held read-only,
like a queued message's (`msgAbs`). -/
section records
variable [GooseExts]

/-- `recvAck` changes only the acks, so not the heartbeat context. -/
theorem hbCtx_recvAck (r : ReadOnly) (src : w64) (ctx : List w8) :
    hbCtx (readonlyRecvAck r src ctx) = hbCtx r := by
  unfold readonlyRecvAck
  split <;> rfl

/-- A queue with a request added is not empty: its context is the position. -/
theorem hbCtx_add (r : ReadOnly) (q : ReadReq) :
    hbCtx (readonlyAdd r q) = u64Le (readonlyPosition (readonlyAdd r q)) := by
  unfold hbCtx
  rw [ite_eq_right (by simp [readonlyAdd])]

end records

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-! ### The parts of the raft struct election neither reads nor writes

The read-state slice, the read-only queue, and the pending `MsgReadIndex` slice.
Indexed by exactly those three fields, so that updating any other field of the struct
leaves it alone.

The Hoare triples about the functions that touch these fields -- `newReadOnly`, the
five `traceX` hooks, `resetRandomizedElectionTimeout`, `abortLeaderTransfer` -- each
live in their own spec/postulates/proof/link collection; see notes/decisions.md. -/

/-- A queued read-index request (`readIndexRequest`) against its record (`ReadReq`,
above): the pointee, read-only for good (nothing writes a `readIndexRequest` after
`addRequest` allocates it, and `maybeAdvance` hands the pointers out), with the commit
index read off it, and its request message frozen (stage R4: a `*pb.Message`, `msgOwn □`),
holding the requester and the request's entries. Persistent. -/
def ownReadreq (p : Loc) (q : ReadReq) : IProp GF :=
  iprop(∃ (rv : readIndexRequest) (mm : MessageM) (sn : Option SnapshotM) (ctx : List w8)
      (rs : List Loc),
  "Hrv" ∷ p ↦□ rv ∗
  "%Hrv_idx" ∷ ⌜rv.index' = q.index ∧ mm.From' = q.src⌝ ∗
  "#Hrv_msg" ∷ msgOwn rv.req' DFrac.discard ⟨mm, q.ents, sn, ctx, rs⟩)

instance ownReadreq_pers (p : Loc) (q : ReadReq) : Persistent (ownReadreq (GF := GF) p q) := by
  unfold ownReadreq
  repeat (first
    | infer_instance
    | (refine @exists_persistent _ _ _ _ ?_; intro _)
    | refine @sep_persistent _ _ _ _ ?_ ?_)

/-- A pending `MsgReadIndex` (`pendingReadIndexMessages`) holding the record's pair `p`
(`RdState.pend`): frozen (stage R4), its snapshot, context and responses unconstrained.
Persistent. -/
def ownPendRI (l : Loc) (p : MessageM × List EntryM) : IProp GF :=
  iprop(∃ (sn : Option SnapshotM) (ctx : List w8) (rs : List Loc),
    msgOwn l DFrac.discard ⟨p.1, p.2, sn, ctx, rs⟩)

instance ownPendRI_pers (l : Loc) (p : MessageM × List EntryM) :
    Persistent (ownPendRI (GF := GF) l p) := by
  unfold ownPendRI
  repeat (first
    | infer_instance
    | (refine @exists_persistent _ _ _ _ ?_; intro _))

/-- The `readOnly` object, as its methods (`addRequest`, `recvAck`, `AckedIndex`,
`maybeAdvance`, `heartbeatCtx`) and `reset` see it: the struct, its `acks` map and its
`unconfirmedReads` queue, indexed by one record (`ReadOnly`). Public; the struct, the
queue's backing array and its capacity are inside.

The queue's slice and the requests it points at are held **read-only** (`↦*□`,
`ownReadreq`) and only the capacity past the end is owned: `addRequest` appends in
place into that slack (`wp_slice_append_persistent`) and `maybeAdvance` hands out the
dropped prefix, which aliases the queue's array and keeps its capacity
(`read_only.go:85`) -- a caller that appended to it would overwrite live reads, so the
prefix goes out as `↦*□` with no `ownSliceCap`: nobody but `ro` can write the slack.

Pointer-receiver methods read through `ro`, so the struct is owned here (`Hro`) --
notes/false-statements.md. -/
def ownReadOnly (ro : Loc) (r : ReadOnly) : IProp GF :=
  iprop(∃ (rov : readOnly) (ptrs : List Loc),
  "Hro" ∷ ro ↦ rov ∗
  "%Hro_conf" ∷ ⌜rov.confirmedReads' = r.confirmed⌝ ∗
  -- (2026-10-12) `ReadOnlySafe`: `ReadOnlyLeaseBased` needs bounded clock drift, out of
  -- scope (`newRaft` takes the option `Safe`, `reset` keeps it)
  "%Hro_safe" ∷ ⌜rov.option' = W64 0⌝ ∗
  "Hacks" ∷ rov.acks' ↦$ r.acks ∗
  "Hucr" ∷ rov.unconfirmedReads' ↦*□ ptrs ∗
  "Hucr_cap" ∷ ownSliceCap Loc rov.unconfirmedReads' (DFrac.own 1) ∗
  "Hreqs" ∷ ([∗list] _k ↦ p;q ∈ ptrs;r.pending, ownReadreq p q))

/-- The `ReadState`s of `r.readStates` (D6, stage R4): the slice of Go structs read-only, each
one's `Index` the record's and its `RequestCtx` a read-only slice holding the record's bytes
(until D6 the model held the Go structs themselves). Persistent. -/
def readStatesPts (rs : GoSlice) (sts : List ReadStateM) : IProp GF :=
  iprop(∃ vs : List ReadState, rs ↦*□ vs ∗
    [∗list] v;st ∈ vs;sts, ⌜v.Index' = st.Index'⌝ ∗ v.RequestCtx' ↦*□ st.RequestCtx')

instance readStatesPts_persistent (rs : GoSlice) (sts : List ReadStateM) :
    Persistent (readStatesPts (GF := GF) rs sts) := by
  unfold readStatesPts; infer_instance

theorem readStatesPts_len (rs : GoSlice) (sts : List ReadStateM) :
    readStatesPts (GF := GF) rs sts ⊢ ⌜sts.length = sint.nat rs.len ∧ 0 ≤ sint.Z rs.len⌝ := by
  iintro H
  iunfold readStatesPts at H
  icases H with ⟨%vs, Hs, Hb⟩
  ihave %H1 := ownSlice_len $$ Hs
  ihave %H2 := BigSepL2.bigSepL2_length $$ Hb
  ipureintro; omega

/-- Full ownership of the three read-index fields and everything hanging off them: the
`readStates` slice, the `readOnly` object, and the `pendingReadIndexMessages` slice, at
the physical read state `rd` (2026-10-12; until then existential, with the two queues
empty).

The `ReadState`s are held **read-only** (`↦*□`, `readStatesPts`), with the capacity past the end owned
(2026-10-13), as `ownReadOnly` holds its queue: `readyWithoutAccept` hands the slice out
(`rd.ReadStates = r.readStates`) while the node keeps it until `acceptReady` sets the
field to `nil`, and a `Ready` that `node.go` abandons may still be sent later, after
`r.readStates` was appended to; `responseToReadIndexReq` and `stepFollower` append in place
into the slack (`wp_slice_append_persistent`), which leaves the elements handed out
alone. -/
def ownRaftMisc (readStates : GoSlice) (ro : Loc) (pendingReadIndex : GoSlice)
    (rd : RdState) : IProp GF :=
  iprop(
  "HreadStates" ∷ readStatesPts readStates rd.states ∗
  "HreadStates_cap" ∷ ownSliceCap ReadState readStates (DFrac.own 1) ∗
  "Hro_obj" ∷ ownReadOnly ro rd.ro ∗
  -- (stage R4) a `[]*pb.Message`: the pointers owned with the capacity, each message frozen
  "Hpri" ∷ (∃ pls : List Loc, pendingReadIndex ↦* pls ∗
    [∗list] l;p ∈ pls;rd.pend, ownPendRI l p) ∗
  "Hpri_cap" ∷ ownSliceCap Loc pendingReadIndex (DFrac.own 1))

/-- `reset` replaces `r.readOnly` with `newReadOnly(r.readOnly.option)`, so it reads
the old object's `option` field; it reaches the object through `ownRaftPhysC_readOnly`
(`InvRaftPhys.lean`), which also installs the new one. -/
theorem ownReadOnly_option (ro : Loc) (r : ReadOnly) :
    ⊢ ownReadOnly (GF := GF) ro r -∗
      ∃ (o : ReadOnlyOption),
        ⌜o = W64 0⌝ ∗
        ro.[readOnly, go!"option"] ↦ o ∗
        (ro.[readOnly, go!"option"] ↦ o -∗ ownReadOnly ro r) := by
  iintro Hro_obj
  unfold ownReadOnly
  icases Hro_obj with ⟨%rov, %ptrs, Hro_obj⟩
  iNamed Hro_obj
  iexists rov.option'
  icases (go_etcd_io.raft.v3.readOnly.readOnly_access_load_option ro rov (DFrac.own 1)).access_strict
    $$ Hro with ⟨Hopt, Hback⟩
  isplitr; · ipureintro; exact Hro_safe
  iframe Hopt
  iintro Hopt
  ihave Hro := Hback $$ Hopt
  iexists rov, ptrs
  simp only [named]
  iframe Hro Hacks Hucr Hucr_cap Hreqs
  ipureintro; exact ⟨Hro_conf, Hro_safe⟩

end proof

end EtcdGrove
end Perennial

-- Projection lemmas, `@[simp, word_unfold]` (ProjSimps.lean).
proj_simps Perennial.EtcdGrove.readonlyAdd
