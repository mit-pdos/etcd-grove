/- Port of election_proof/spec_raft__appendEntry.v (feb5c73d4).

Lean notes: Rocq's `imap` is `List.mapIdx` (same argument order: index, then element).
The Rocq `Forall (λ e, …) ents` premises are `∀ e ∈ ents, …`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `appendEntry` stamps the current term and the next indices into the caller's batch,
charges it against the uncommitted-entry budget, appends it to the log and then queues
a self-addressed `MsgAppResp` at the new last index (`raft.appendEntry.impl`,
`Code/go_etcd_io/raft/v3.lean`: `r.send(pb.Message{To: r.id, Type:
pb.MsgAppResp, Index: li})`, `li` what `raftLog.append` returned). Since 2026-10-01
`MsgAppResp` has an abstraction, so the outbox grows by that message, `selfAck`
(`Defs.lean`): the leader acknowledging its own append, which the model's `Step.win`
and `Step.propose` send. (Until then `mtypeOf MsgAppResp = none` and the abstract outbox
was unchanged.)

Three pieces of history, because this claim has been wrong before. Its form before
2026-09-15 owned only `ownRaftLog` while the code it describes writes
`r.msgsAfterAppend`, which made it **false**; it could not be stated honestly before the
outbox was abstracted, because the old `is_phys_msg` clause was unprovable for a
`MsgAppResp`. Until 2026-09-18 it was called `wp_raft__appendEmptyEntry`, after a Go
method that **does not exist** -- the method is `appendEntry`. Both are in
notes/false-statements.md. And until 2026-09-20 the triple was an `Axiom`: it is now
proved.

Two more things the first form of this triple got wrong, both found by review on
2026-09-18 and both the same old mistake -- a claim about the code that nobody had read
the body for.

**It took no ownership of `es`.** The method writes `Term` and `Index` into *every
element* of the slice (`raft.appendEntry.impl`'s `slice.for_range`), so a triple that
does not own `es` asserts the safety of a write to memory it has no claim on -- the
`ProgressTracker.Visit` mistake again, one level out: not "own the receiver's fields"
but "own what you write". `es ↦* ents` is now a precondition. It comes back:
`raftLog.append` copies the entry *values* into `unstable.entries`, so the caller's
slice is not consumed -- and since 2026-09-25 it comes back *named*, as the stamped
batch (`stamp`, `Protocol/Model.lean`): `Term := r.Term` and `Index :=
lastIndex()+1+k` in element `k`. (Until the log's state was in `NState` the witness
was existential, because naming it would have pinned the log's length.)

**It claimed `RET #true` unconditionally**, and `appendEntry` does have a
`return: #false` -- the path where `increaseUncommittedSize` rejects the batch. The fix
is *not* to make the result existential. `becomeLeader`, the only caller in scope, does

    if !r.appendEntry(pb.Entry{Data: nil}) { r.logger.Panic(…) }

and `Logger.wp_logf` deliberately excludes `Panic`, so a bare existential result makes
`becomeLeader` unprovable rather than merely weaker. What is true is that the reject
path is unreachable *for an empty payload*: `increaseUncommittedSize` returns `false`
only when

    uncommittedSize > 0 ∧ payloadsSize(ents) > 0 ∧ … > maxUncommittedSize

(`raft.increaseUncommittedSize.impl`), and `payloadsSize` sums `len(e.Data)`.

From 2026-09-18 to 2026-10-01 that was a *premise* (`Hempty`) and the result was
`RET #true`. Since 2026-10-01 the triple takes an arbitrary batch (until 2026-10-13 of
`EntryNormal` entries) -- what
`stepLeader`'s `MsgProp` arm passes, and what the model's `Step.propose` describes -- so
the result is a bool `accepted`, and the fact above is a *conjunct* of the
postcondition: `(∀ e ∈ ents, Data empty) → accepted = true`. That is as far as
acceptance can be pinned: the exact condition reads `r.uncommittedSize` and
`r.maxUncommittedSize`, which `NState` does not hold. `becomeLeader` destructs
`accepted` and kills the `false` branch with the implication, so its `Panic` is still
demonstrably dead code.

### The two paths (read against the body, 2026-10-01)

The stamping loop runs *before* `increaseUncommittedSize`, so the caller's slice is
stamped on both paths and `es ↦* ents.mapIdx (stamp …)` is outside the `if`. The reject
path reads `r.id` and `r.logger`, calls `Warningf`, and returns `false`: nothing in the
struct is written, so it comes back at `s`. The accept path writes `r.uncommittedSize`
(which `ownRaftPhys` does not pin), appends, and sends the self-ack. (The named result
`accepted` is allocated and never read: both exits are `return: #b`.)

### The premises

What the *log* needs (until 2026-10-13 also `Hnorm`, no configuration change in the
batch, for `ownRaftLog`'s `HnoConfChange`; since reconfiguration stage D the log takes
conf-change entries as data. The method does *not* set `Type` -- only `Term` and `Index`
-- so the caller's value is what lands in the log):

- `Hsmall`: the batch has fewer than `2^61` entries, so that `lastIndex()+1+k` does not
  wrap while the loop stamps it in.

### The no-wrap gap, and how it is closed

Handing `ownRaftPhys` back after `raftLog.append` also asserts `ownRaftLog`'s
`Hnowrap` -- that `prev.index + |sents| + |uents| + 1 < 2^64` still holds for the
*longer* log. The pre-state gives that bound at the old length, so until 2026-09-20
this triple was an axiom with a documented over-claim, and the plan recorded here was
to make it a premise and thread it through `becomeLeader` to `Step`.

**That plan does not work, and the reason is worth writing down.** A premise of
`becomeLeader` (or of `Step`) may mention only `cfg`, `r`, `id` and `s`; the log's
length is existentially quantified *inside* `ownRaftPhys`, so no premise at those specs
can say anything about it. Threading would therefore have meant exposing the log's last
index in every spec from here up to `Step` -- or indexing `ownRaftPhys` by it, which is
95 call sites. Nor can the bound be an invariant of the log: any property preserved by
`append` is closed under `+1` at the last index and so bounds nothing (this is why the
"fixed slack" idea fails -- a slack constant shrinks by one on every append).

What is true is that the log's last index splits into a part `append` moves and a part
it does not. `|uents|` is the length of the Go slice `unstable.entries`, and
Perennial's `own_slice_len` bounds *any* slice's length by `2^63` -- re-derived from the
new slice after the `append`, so it is inductive for free. `prev.index + |sents|` is the
compaction boundary plus the stable prefix, which lives behind the client-supplied
`Storage` and which nothing on this path changes. So the assumption was put where it
belongs: `isStorage`'s `Hbounded` clause (`InvStorage.lean`) says the stable log's last
index is below `2^61`. With it, and with `Hsmall`, the log's last index stays below
`2^61 + 2^63` and the append cannot wrap -- no caller obligation, and `becomeLeader`'s
spec is unchanged.

### The rest of the body

`increaseUncommittedSize` writes `r.uncommittedSize`, a field `ownRaftPhys` does not
mention; `traceReplicate` is a literal no-op; and the `MsgAppResp` is `SendOk`'s
`MsgAppResp` clause, which allows it to be self-addressed at a nonzero term (since
2026-10-10, the premise `s.term ≠ 0`: a leader's term, `ownRaftGhost_term_nz`).

### The log in the postcondition

Since 2026-09-25 the log's state is in `NState`, so the postcondition says exactly what
was appended: the batch, stamped with the current term and consecutive indices after
`lastIndex()` (`stamp`, `logLast`, `logAppend`, `Defs.lean`). Until then it returned
the struct at the *same* state, which was only true because `ownRaftPhys` quantified
the log away. -/
abbrev raft.appendEntry.spec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (es : GoSlice)
    (ents : List raftpb.Entry),
  -- a batch small enough that `lastIndex()+1+k` does not wrap
  (ents.length : Int) < 2^61 →
  -- a leader's term (2026-10-10): the self-acknowledgement is stamped with it, and
  -- `RawNode.Advance` steps it, which needs a nonzero term (`AAMsgOk`)
  s.term ≠ W64 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhysCV c c.voters r id s ∗
      es ↦* ents }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"appendEntry")) (Val #es))
  {{ (accepted : Bool), RET #accepted;
      -- an all-empty batch is never dropped -- see above
      ⌜(∀ e ∈ ents, sint.Z e.Data'.len = 0) → accepted = true⌝ ∗
      -- stamped on both paths: the loop runs before the budget check
      es ↦* ents.mapIdx (stamp s.term (logLast s.logst)) ∗
      if accepted then
        ownRaftPhysCV c c.voters r id
          (sendMsgs
            { s with logst :=
                logAppend s.logst (ents.mapIdx (stamp s.term (logLast s.logst))) }
            [selfAck id
              { s with logst :=
                  logAppend s.logst (ents.mapIdx (stamp s.term (logLast s.logst))) }])
      else
        -- dropped: `Warningf` and `return false`, nothing written
        ownRaftPhysCV c c.voters r id s }}

/-- The statement on `ownRaftPhys` (the simple configuration `cfg`) until 2026-10-13,
derived from `raft.appendEntry.spec` by `raft.appendEntry.spec_simple`. -/
abbrev raft.appendEntry.specS : Prop :=
  ∀ (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (es : GoSlice)
    (ents : List raftpb.Entry),
  (ents.length : Int) < 2^61 →
  s.term ≠ W64 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhys cfg r id s ∗
      es ↦* ents }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"appendEntry")) (Val #es))
  {{ (accepted : Bool), RET #accepted;
      ⌜(∀ e ∈ ents, sint.Z e.Data'.len = 0) → accepted = true⌝ ∗
      es ↦* ents.mapIdx (stamp s.term (logLast s.logst)) ∗
      if accepted then
        ownRaftPhys cfg r id
          (sendMsgs
            { s with logst :=
                logAppend s.logst (ents.mapIdx (stamp s.term (logLast s.logst))) }
            [selfAck id
              { s with logst :=
                  logAppend s.logst (ents.mapIdx (stamp s.term (logLast s.logst))) }])
      else
        ownRaftPhys cfg r id s }}

open Iris.ProofMode in
theorem raft.appendEntry.spec_simple
    (H : raft.appendEntry.spec (GF := GF) (hG := hG)) :
    raft.appendEntry.specS (GF := GF) (hG := hG) := by
  intro cfg r id s es ents Hlen Ht
  iintro %Φ ⟨#Hpkg, Hphys, Hes⟩ HΦ
  ihave Hphys := ownRaftPhys_toC' $$ Hphys
  iapply H _ r id s es ents Hlen Ht $$ [$Hpkg $Hphys $Hes]
  inext
  iintro %acc ⟨%Hacc, Hes, Hphys⟩
  iapply HΦ
  iframe Hes
  isplitr
  · ipureintro; exact Hacc
  cases acc <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> iapply ownRaftPhysC_toS $$ Hphys

end spec

end EtcdGrove
end Perennial
