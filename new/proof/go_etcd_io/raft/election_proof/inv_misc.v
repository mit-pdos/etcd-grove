(** * Raft components election neither reads nor writes *)

Require Export New.proof.go_etcd_io.raft.election_proof.inv_raftlog.
Require Export New.proof.go_etcd_io.raft.election_proof.inv_tracker.

(** ** The read-only object's records (2026-10-04; here and not in [defs.v] so that adding them does not
    invalidate the log and tracker proofs)

    [own_ReadOnly ro r] ([inv_misc.v]) is indexed by [readonly.t], not by
    the Goose [readOnly] struct (notes/raft-replication-model.md, "Public
    representation predicates"): exactly the state the five methods'
    specs ([addRequest], [recvAck], [AckedIndex], [maybeAdvance],
    [heartbeatCtx]) and [reset]/[stepLeader] (the [option]) read.

    A queued read-index request is the part of [readIndexRequest] anyone
    reads back: the commit index at the time, the requester ([req.From],
    which [responseToReadIndexReq] compares with [r.id]) and the request's
    entries ([req.Entries[0].Data] is the context of a local read, and a
    forwarded request's response carries [req.Entries] whole).  The
    message's other fields are never read after queueing.  The entries are
    held read-only, like a queued message's ([msg_abs]). *)
Module readreq.
Record t := mk { index : w64; from : w64; ents : list raftpb.Entry.t }.
#[global] Instance settable : Settable t := settable! mk <index; from; ents>.
End readreq.

(** The read-only object.  [safe]: [option = ReadOnlySafe] ([0]; the only
    other option raft has, [ReadOnlyLeaseBased], is [1]).  [pending]:
    [unconfirmedReads], oldest first.  [acks]: each voter's acknowledged
    *position* -- the largest context (as a number) the voter echoed in a
    heartbeat response; the context of a heartbeat is [confirmed +
    length pending] at the time it was sent ([readonly_position]).
    [confirmed]: [confirmedReads], the number of requests ever removed
    from the front of [pending]. *)
Module readonly.
Record t := mk { safe : bool; pending : list readreq.t;
                 acks : gmap w64 w64; confirmed : w64 }.
#[global] Instance settable : Settable t :=
  settable! mk <safe; pending; acks; confirmed>.
End readonly.

(** The position a heartbeat context encodes: [confirmedReads + len
    unconfirmedReads] (wrapping, as the [uint64] sum does). *)
Definition readonly_position (r : readonly.t) : w64 :=
  word.add r.(readonly.confirmed) (W64 (length r.(readonly.pending))).

(** [addRequest]: append to the queue. *)
Definition readonly_add (r : readonly.t) (q : readreq.t) : readonly.t :=
  r <| readonly.pending := r.(readonly.pending) ++ [q] |>.

(** [recvAck from ctx], [ctx] as the bytes it holds: nothing for an empty
    context, else the voter's ack becomes the larger of its old one ([0] if
    none) and the first eight bytes read little-endian. *)
Definition readonly_recvAck (r : readonly.t) (from : w64) (ctx : list w8)
    : readonly.t :=
  if decide (ctx = []) then r
  else r <| readonly.acks := <[from := w64_max (default (W64 0) (r.(readonly.acks) !! from))
                                                (le_to_u64 (take 8 ctx))]>
                                r.(readonly.acks) |>.

(** [maybeAdvance], given [N], the quorum index of the voters' acks
    ([CommittedIndex]): nothing when [N] is not past [confirmed]; else the
    first [N - confirmed] requests leave the queue, [confirmed] becomes [N]
    and the removed requests are returned. *)
Definition readonly_advance (r : readonly.t) (N : w64) : readonly.t * list readreq.t :=
  if decide (uint.Z N ≤ uint.Z r.(readonly.confirmed)) then (r, [])
  else
    let k := uint.nat (word.sub N r.(readonly.confirmed)) in
    (r <| readonly.pending := drop k r.(readonly.pending) |>
       <| readonly.confirmed := N |>,
     take k r.(readonly.pending)).

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

(** The (fixed) set of voters. *)
Context (cfg : gset w64).


(** *** The parts of the raft struct election neither reads nor writes:
    the read-state slice, the read-only queue, and the pending
    [MsgReadIndex] slice.  Indexed by exactly those three fields, so that
    updating any other field of the struct leaves it alone.

    The Hoare triples about the functions that touch these fields --
    [newReadOnly], the five [traceX] hooks, [resetRandomizedElectionTimeout],
    [abortLeaderTransfer] -- each live in their own
    spec/postulates/proof/link collection; see notes/decisions.md. *)

(** Full ownership of those three fields and everything hanging off them:
    the [readStates] slice, the [readOnly] object together with its [acks]
    map and its [unconfirmedReads] slice, and the
    [pendingReadIndexMessages] slice.  The *contents* are existential --
    election never reads any of it -- but the ownership is real, so nothing
    else in the development can claim the same heap. *)
(** A queued read-index request ([readIndexRequest]) against its record
    ([readreq.t], [defs] above): the pointee, read-only for good (nothing
    writes a [readIndexRequest] after [addRequest] allocates it, and
    [maybeAdvance] hands the pointers out), with the commit index, the
    requester and the request's entries read off it.  Persistent. *)
Definition own_readreq (p : loc) (q : readreq.t) : iProp Σ :=
  ∃ (rv : raft.readIndexRequest.t),
  "Hrv" ∷ p ↦□ rv ∗
  "%Hrv_idx" ∷ ⌜ rv.(raft.readIndexRequest.index') = q.(readreq.index) ∧
                 rv.(raft.readIndexRequest.req').(raftpb.Message.From')
                   = q.(readreq.from) ⌝ ∗
  "Hrv_ents" ∷ rv.(raft.readIndexRequest.req').(raftpb.Message.Entries')
                 ↦*□ q.(readreq.ents).

Global Instance own_readreq_pers p q : Persistent (own_readreq p q).
Proof. rewrite /own_readreq. apply _. Qed.

(** The [readOnly] object, as its methods ([addRequest], [recvAck],
    [AckedIndex], [maybeAdvance], [heartbeatCtx]) and [reset] see it: the
    struct, its [acks] map and its [unconfirmedReads] queue, indexed by one
    record ([readonly.t]).  Public; the struct, the queue's backing array
    and its capacity are inside.

    The queue's slice and the requests it points at are held **read-only**
    ([↦*□], [own_readreq]) and only the capacity past the end is owned:
    [addRequest] appends in place into that slack ([wp_slice_append_persistent])
    and [maybeAdvance] hands out the dropped prefix, which aliases the
    queue's array and keeps its capacity ([read_only.go:85]) -- a caller
    that appended to it would overwrite live reads, so the prefix goes out
    as [↦*□] with no [own_slice_cap]: nobody but [ro] can write the slack.

    Pointer-receiver methods read through [ro], so the struct is owned
    here ([Hro]) -- notes/false-statements.md. *)
Definition own_ReadOnly (ro : loc) (r : readonly.t) : iProp Σ :=
  ∃ (rov : raft.readOnly.t) (ptrs : list loc),
  "Hro" ∷ ro ↦ rov ∗
  "%Hro_safe" ∷ ⌜ r.(readonly.safe)
                    = bool_decide (rov.(raft.readOnly.option') = W64 0) ⌝ ∗
  "%Hro_conf" ∷ ⌜ rov.(raft.readOnly.confirmedReads') = r.(readonly.confirmed) ⌝ ∗
  "Hacks" ∷ rov.(raft.readOnly.acks') ↦$ r.(readonly.acks) ∗
  "Hucr" ∷ rov.(raft.readOnly.unconfirmedReads') ↦*□ ptrs ∗
  "Hucr_cap" ∷ own_slice_cap loc rov.(raft.readOnly.unconfirmedReads') (DfracOwn 1) ∗
  "Hreqs" ∷ ([∗ list] p; q ∈ ptrs; r.(readonly.pending), own_readreq p q).

(** Full ownership of the three fields election neither reads nor writes
    and everything hanging off them: the [readStates] slice, the
    [readOnly] object, and the [pendingReadIndexMessages] slice.  The
    [readStates] contents are existential -- nothing in scope reads them --
    and the two read-index queues are empty (phase-1 scope, 2026-10-01);
    the ownership is real, so nothing else in the development can claim the
    same heap. *)
Definition own_raft_misc (readStates : slice.t) (ro : loc)
                         (pendingReadIndex : slice.t) : iProp Σ :=
  ∃ (rss : list raft.ReadState.t) (rr : readonly.t),
  "HreadStates" ∷ readStates ↦* rss ∗
  "HreadStates_cap" ∷ own_slice_cap raft.ReadState.t readStates (DfracOwn 1) ∗
  "Hro_obj" ∷ own_ReadOnly ro rr ∗
  (** Scope (phase 1): no read-index requests -- which is what makes
      [heartbeatCtx] return [nil].  Phase 3 lifts this conjunct (and
      only this one) when [stepLeader] starts queueing [MsgReadIndex]. *)
  "%Hro_pending" ∷ ⌜ rr.(readonly.pending) = [] ⌝ ∗
  (** Scope (phase 1): no read-index requests, so no [MsgReadIndex] is
      pending -- which is what makes [releasePendingReadIndexMessages] a
      no-op.  The empty list is in the points-to, as for [Hucr] above. *)
  "Hpri" ∷ pendingReadIndex ↦* ([] : list raftpb.Message.t) ∗
  "Hpri_cap" ∷ own_slice_cap raftpb.Message.t pendingReadIndex (DfracOwn 1).


(** [reset] replaces [r.readOnly] with [newReadOnly(r.readOnly.option)],
    so it reads the old object's [option] field ([safe] says which it is); it reaches the object
    through [own_raft_phys_readOnly] ([inv_raft_phys.v]), which also
    installs the new one. *)
Lemma own_ReadOnly_option ro (r : readonly.t) :
  own_ReadOnly ro r -∗
  ∃ (o : raft.ReadOnlyOption.t),
    ⌜ r.(readonly.safe) = bool_decide (o = W64 0) ⌝ ∗
    ro.[raft.readOnly.t, "option"] ↦ o ∗
    (ro.[raft.readOnly.t, "option"] ↦ o -∗ own_ReadOnly ro r).
Proof.
  iIntros "Hro_obj". iNamed "Hro_obj".
  iExists rov.(raft.readOnly.option'). iSplit; first done.
  iDestruct (access_strict
               (A := ro.[raft.readOnly.t, "option"] ↦ rov.(raft.readOnly.option'))
               (A' := ro.[raft.readOnly.t, "option"] ↦ rov.(raft.readOnly.option'))
               (P := ro ↦ rov) (P' := ro ↦ rov) with "Hro") as "[Hopt Hback]".
  iFrame "Hopt". iIntros "Hopt".
  iDestruct ("Hback" with "Hopt") as "Hro".
  rewrite /own_ReadOnly. iExists rov, ptrs. iFrame. done.
Qed.


End proof.
