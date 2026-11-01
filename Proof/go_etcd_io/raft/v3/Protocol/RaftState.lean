/-
# A node's durable protocol state (2026-10-31, durability stage I-1)

The pure record a durable client owns of a node (`raftState γ id S`, whose sealed body is the
protocol's `ownDurGhost γ id S`, `Protocol/GhostState.lean`): its term, vote, log from a base,
and the commit index of the last batch it entered (candidate 12's `RaftState`, with the
commit the user's resolution of review 1's R1 added). Only a `Ready`'s batch moves it
(`RaftState.next`), when the client enters it. `notes/raft-durability-proof-plan.md`, I-1.
-/
module

public import Proof.go_etcd_io.raft.v3.Protocol.Model

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open go_etcd_io.raft.v3

section raftState
variable [GooseExts]

/-- The durable part of a node's protocol state: term, vote, its log from a base (the
committed prefix up to `base` is not repeated), and the commit index as of the last entered
batch. -/
structure RaftState where
  term : w64
  vote : w64
  /-- the entry before `ents` -/
  base : entryID
  /-- consecutive from `base.index + 1` -/
  ents : List EntryM
  /-- the commit index of the last batch entered -/
  commit : w64

/-- A node that has never stored anything. -/
def RaftState.init : RaftState := ⟨W64 0, W64 0, entryID.mk (W64 0) (W64 0), [], W64 0⟩

/-- The last index of the stored log. -/
def RaftState.last (S : RaftState) : Nat := uint.nat S.base.index' + S.ents.length

/-- `MemoryStorage.Append`'s effect on a log `(b, es)`: nothing if every new entry is at or
below the base; otherwise the new entries cut at the base, the stored ones replaced from the
first new index on (`plogTruncateAppend`). -/
def appendEnts (b : entryID) (es : List EntryM) (ents : List EntryM) : List EntryM :=
  match ents with
  | [] => es
  | e0 :: _ =>
      plogTruncateAppend b es (ents.drop (uint.Z b.index' + 1 - uint.Z e0.Index').toNat)

/-- A batch's effect: a snapshot (if any) makes its id the base and drops the entries; the hard
state's term, vote and commit; the entries as `MemoryStorage.Append` puts them. -/
def RaftState.next (S : RaftState) (term vote commit : w64) (snap : Option SnapshotM)
    (es : List EntryM) : RaftState :=
  let S1 : RaftState := match snap with
    | some sn => { S with base := entryID.mk sn.Metadata'.Term' sn.Metadata'.Index', ents := [] }
    | none => S
  { S1 with term := term, vote := vote, commit := commit, ents := appendEnts S1.base S1.ents es }

/-- The stored entries above `b` (a base at or above `S.base`): what a storage restarted from
`S` at the base `b` holds. -/
def RaftState.entsFrom (S : RaftState) (b : entryID) : List EntryM :=
  S.ents.drop (uint.Z b.index' - uint.Z S.base.index').toNat

/-- `S`'s full log is `F`: its base is `F`'s entry at `S.base.index` (`FullOk` of the
prefix below it), and its entries are `F`'s from there. -/
def DurFull (S : RaftState) (F : List EntryM) : Prop :=
  S.ents = F.drop (uint.nat S.base.index') ∧ FullOk S.base (F.take (uint.nat S.base.index'))

end raftState

end EtcdGrove
end Perennial
