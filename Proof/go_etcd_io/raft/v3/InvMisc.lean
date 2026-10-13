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
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftlog
public import Proof.go_etcd_io.raft.v3.InvTracker

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
variable [FfiSyntax]

/-- The read-index scope of the election and replication proofs: no `ReadState`, no queued
or pending request. -/
def RdScope (rd : RdState) : Prop :=
  rd.states = [] ∧ rd.ro.pending = [] ∧ rd.pend = []

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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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
index, the requester and the request's entries read off it. Persistent. -/
def ownReadreq (p : Loc) (q : ReadReq) : IProp GF :=
  iprop(∃ (rv : readIndexRequest),
  "Hrv" ∷ p ↦□ rv ∗
  "%Hrv_idx" ∷ ⌜rv.index' = q.index ∧ rv.req'.From' = q.src⌝ ∗
  "Hrv_ents" ∷ rv.req'.Entries' ↦*□ q.ents)

instance ownReadreq_pers (p : Loc) (q : ReadReq) : Persistent (ownReadreq (GF := GF) p q) := by
  unfold ownReadreq; infer_instance

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

/-- Full ownership of the three read-index fields and everything hanging off them: the
`readStates` slice, the `readOnly` object, and the `pendingReadIndexMessages` slice, at
the physical read state `rd` (2026-10-12; until then existential, with the two queues
empty). -/
def ownRaftMisc (readStates : GoSlice) (ro : Loc) (pendingReadIndex : GoSlice)
    (rd : RdState) : IProp GF :=
  iprop(
  "HreadStates" ∷ readStates ↦* rd.states ∗
  "HreadStates_cap" ∷ ownSliceCap ReadState readStates (DFrac.own 1) ∗
  "Hro_obj" ∷ ownReadOnly ro rd.ro ∗
  "Hpri" ∷ pendingReadIndex ↦* rd.pend.map Prod.fst ∗
  "Hpri_cap" ∷ ownSliceCap raftpb.Message pendingReadIndex (DFrac.own 1) ∗
  "#Hpri_ents" ∷ ([∗list] p ∈ rd.pend, p.1.Entries' ↦*□ p.2))

/-- `reset` replaces `r.readOnly` with `newReadOnly(r.readOnly.option)`, so it reads
the old object's `option` field; it reaches the object through `ownRaftPhys_readOnly`
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
