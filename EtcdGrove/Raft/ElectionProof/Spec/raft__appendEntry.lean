/- Port of election_proof/spec_raft__appendEntry.v.

Lean notes: Rocq's `imap` is `List.mapIdx` (same argument order: index, then element).
-/
import EtcdGrove.Raft.ElectionProof.InvRaftPhys

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- Out of scope: the empty entry a new leader appends. `appendEntry` stamps the
current term and the next indices into the caller's batch, charges it against the
uncommitted-entry budget, appends it to the log and then queues a self-addressed
`MsgAppResp` (`raft.appendEntry.impl`, `Perennial/Code/go_etcd_io/raft/v3.lean`).
`mtypeOf MsgAppResp = none`, so `absMsgOpt` drops it and the abstract state -- outbox
included -- is unchanged.

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
but "own what you write". `es ↦* ents` is now a precondition and comes back
existentially quantified, since the method has overwritten two fields of each entry.
It does come back: `raftLog.append` copies the entry *values* into `unstable.entries`,
so the caller's slice is not consumed. (The witness is `ents` with `Term := r.Term` and
`Index := lastIndex()+1+k` in each element; naming it here would pin `r.Term` and the
log's length, neither of which `ownRaftPhys` exposes, and no caller needs it.)

**It claimed `RET #true` unconditionally**, and `appendEntry` does have a
`return: #false` -- the path where `increaseUncommittedSize` rejects the batch. The fix
is *not* to make the result existential. `becomeLeader`, the only caller in scope, does

    if !r.appendEntry(pb.Entry{Data: nil}) { r.logger.Panic(…) }

and `Logger.wp_logf` deliberately excludes `Panic`, so an existential result makes
`becomeLeader` unprovable rather than merely weaker. What is actually true is that the
reject path is unreachable *for an empty payload*: `increaseUncommittedSize` returns
`false` only when

    uncommittedSize > 0 ∧ payloadsSize(ents) > 0 ∧ … > maxUncommittedSize

(`raft.increaseUncommittedSize.impl`), and `payloadsSize` sums `len(e.Data)`. So
`Hempty` below -- every entry's `Data` is empty, which is exactly what `becomeLeader`
passes -- is what makes `RET #true` honest, and it is also what makes the `Panic`
demonstrably dead code rather than assumed away.

### The premises

`Hempty` is the one just described. The other two are what the *log* needs, and both
are discharged by `becomeLeader` from the literal it builds:

- `Hnorm`: no entry in the batch is a configuration change. `ownRaftLog`'s
  `HnoConfChange` is about the whole log, so appending an `EntryConfChange` would break
  it. `becomeLeader` passes `pb.Entry{Data: nil}`, whose `Type` is the zero value
  `EntryNormal`. (Note the method does *not* set `Type` -- only `Term` and `Index` --
  so the caller's value is what lands in the log.)
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

`increaseUncommittedSize` adds a zero payload, so `r.uncommittedSize` is unchanged in
everything `ownRaftPhys` can see (it mentions no such field); `traceReplicate` is a
literal no-op; and the `MsgAppResp` has no `mtypeOf`, so the abstract outbox is
unchanged -- it is `send_ok`'s third clause, and a self-addressed message is allowed
there for exactly this type.

### The log in the postcondition

Since 2026-09-25 the log's state is in `NState`, so the postcondition says exactly what
was appended: the batch, stamped with the current term and consecutive indices after
`lastIndex()` (`stamp`, `logLast`, `logAppend`, `Defs.lean`). Until then it returned
the struct at the *same* state, which was only true because `ownRaftPhys` quantified
the log away. -/
abbrev raft.appendEntry.spec : Prop :=
  ∀ (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (es : GoSlice)
    (ents : List raftpb.Entry),
  -- empty payloads, so `increaseUncommittedSize` cannot reject -- see above
  (∀ e ∈ ents, sint.Z e.Data'.len = 0) →
  -- no configuration change, so the log's `HnoConfChange` survives
  (∀ e ∈ ents, e.Type' = EntryNormal) →
  -- a batch small enough that `lastIndex()+1+k` does not wrap
  (ents.length : Int) < 2^61 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhys cfg r id s ∗
      es ↦* ents }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"appendEntry")) (Val #es))
  {{ RET #true;
      ownRaftPhys cfg r id
        { s with logst :=
            (logAppend s.logst (ents.mapIdx (stamp s.term (logLast s.logst)))) } ∗
      es ↦* ents.mapIdx (stamp s.term (logLast s.logst)) }}

end spec

end EtcdGrove
end Perennial
