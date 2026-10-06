/-
Port of `election_proof/inv_misc.v`: raft components election neither reads nor writes.

The parts of the raft struct election neither reads nor writes: the read-state slice,
the read-only queue, and the pending `MsgReadIndex` slice. Indexed by exactly those
three fields, so that updating any other field of the struct leaves it alone.

The Hoare triples about the functions that touch these fields -- `newReadOnly`, the
five `traceX` hooks, `resetRandomizedElectionTimeout`, `abortLeaderTransfer` -- each
live in their own spec/postulates/proof/link collection; see notes/decisions.md.

Lean notes: Rocq's section variable `cfg` is not used by anything in this file, so it
is dropped (in Rocq it is not a parameter of these definitions either, since they do
not mention it). `raft.readOnly.t`, `raft.ReadState.t` and `raft.ReadOnlyOption.t` are
`readOnly`, `ReadState` and `ReadOnlyOption`; Rocq's `list loc` / `own_slice_cap loc`
for `unconfirmedReads` is `List Loc` / `ownSliceCap Loc`.
-/
import EtcdGrove.Raft.ElectionProof.InvRaftlog
import EtcdGrove.Raft.ElectionProof.InvTracker

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The `readOnly` object: the struct, its `acks` map and its `unconfirmedReads` slice.
Its own predicate because `newReadOnly` allocates one: that spec owns nothing going in
and hands back exactly this (2026-09-23; it used to consume and return the whole of
`ownRaftMisc`, including two slices it never touches). -/
def ownReadOnly (ro : Loc) : IProp GF :=
  iprop(∃ (rov : readOnly) (acks : GMap w64 w64) (ucr : List Loc),
  "Hro" ∷ ro ↦ rov ∗
  "Hacks" ∷ rov.acks' ↦$ acks ∗
  "Hucr" ∷ rov.unconfirmedReads' ↦* ucr ∗
  "Hucr_cap" ∷ ownSliceCap Loc rov.unconfirmedReads' (DFrac.own 1))

/-- Full ownership of the three fields election neither reads nor writes and
everything hanging off them: the `readStates` slice, the `readOnly` object, and the
`pendingReadIndexMessages` slice. The *contents* are existential -- election never
reads any of it -- but the ownership is real, so nothing else in the development can
claim the same heap. -/
def ownRaftMisc (readStates : GoSlice) (ro : Loc) (pendingReadIndex : GoSlice) : IProp GF :=
  iprop(∃ (rss : List ReadState) (prims : List raftpb.Message),
  "HreadStates" ∷ readStates ↦* rss ∗
  "HreadStates_cap" ∷ ownSliceCap ReadState readStates (DFrac.own 1) ∗
  "Hro_obj" ∷ ownReadOnly ro ∗
  "Hpri" ∷ pendingReadIndex ↦* prims ∗
  "Hpri_cap" ∷ ownSliceCap raftpb.Message pendingReadIndex (DFrac.own 1))

/-- `reset` replaces `r.readOnly` with `newReadOnly(r.readOnly.option)`, so it reads
the old object's `option` field; it reaches the object through `ownRaftPhys_readOnly`
(`InvRaftPhys.lean`), which also installs the new one. -/
theorem ownReadOnly_option (ro : Loc) :
    ⊢ ownReadOnly (GF := GF) ro -∗
      ∃ (o : ReadOnlyOption),
        ro.[readOnly, go!"option"] ↦ o ∗
        (ro.[readOnly, go!"option"] ↦ o -∗ ownReadOnly ro) := by
  iintro Hro_obj
  unfold ownReadOnly
  icases Hro_obj with ⟨%rov, %acks, %ucr, Hro_obj⟩
  iNamed Hro_obj
  iexists rov.option'
  icases (go_etcd_io.raft.v3.readOnly.readOnly_access_load_option ro rov (DFrac.own 1)).access_strict
    $$ Hro with ⟨Hopt, Hback⟩
  iframe Hopt
  iintro Hopt
  ihave Hro := Hback $$ Hopt
  iexists rov, acks, ucr
  simp only [named]
  iframe Hro Hacks Hucr Hucr_cap

end proof

end EtcdGrove
end Perennial
