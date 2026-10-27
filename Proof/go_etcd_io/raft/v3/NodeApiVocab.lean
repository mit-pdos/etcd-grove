/-
# Raft's node API over an abstract log: the pure vocabulary (2026-10-27)

The records and pure definitions the drafted API (`NodeApiDraft.lean`) is stated in, which its
implementation (`NodeApiImpl.lean`) shares: an entry of the committed log as a client sees it
(`LogEntry`), the fillers and the requested entries (`opsOf`), the bootstrap log (`BootLog`), the
state of a node's `Ready` loop (`NodeDriverState`), a `Ready`'s committed entries
(`committedEntriesAt`). Moved out of the draft unchanged, in its namespace.
-/
module

public import Proof.go_etcd_io.raft.v3.InvNodeCtx
public import Proof.go_etcd_io.raft.v3.InvMemstorage

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Draft

open Iris Iris.BI go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- An entry of the committed log as a client sees it. Its index is its position (the `i`-th entry,
from 0, has index `i + 1`). -/
structure LogEntry where
  term : w64
  type : raftpb.EntryType
  data : List w8

/-- The Go record of the entry at index `idx`. -/
def LogEntry.toEntryM (idx : w64) (e : LogEntry) : EntryM := ⟨e.term, idx, e.type, e.data⟩

/-- A raft entry as a client sees it: its index dropped. -/
def LogEntry.ofEntryM (e : EntryM) : LogEntry := ⟨e.Term', e.Type', e.Data'⟩

/-- A raft log as a client sees it (the committed log up to a snapshot, `SnapLoan.dlv`). -/
def strip (L : List EntryM) : List LogEntry := L.map LogEntry.ofEntryM

/-- **A filler**: an entry that carries nothing, an empty normal entry or an empty `ConfChangeV2`.
Raft appends these itself: a new leader's entry (`raft.go:961`), the entry leaving a joint
configuration (`AutoLeave`, `raft.go:742`), the entry in place of a conf change it refuses
(`raft.go:1341`). A client's empty proposal looks the same, so it is a filler too: an operation must
be encoded as non-empty bytes to take effect as one. -/
def LogEntry.isFiller (e : LogEntry) : Prop :=
  e.data = [] ∧ (e.type = W32 0 ∨ e.type = W32 2)

instance (e : LogEntry) : Decidable e.isFiller := by unfold LogEntry.isFiller; infer_instance

/-- **The requested entries** of a log: everything but its fillers. -/
def opsOf (l : List LogEntry) : List LogEntry := l.filter fun e => !decide e.isFiller

/-- The bootstrap log: a `ConfChangeAddNode` of each peer, its context `ctx`, at term 1, as
`MarshalConfChange` encodes it (`bs`). -/
def BootLog (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry) : Prop :=
  boot.length = ps.length ∧ (boot.length : Int) < 2 ^ 61 ∧
  ∀ (k : Nat) (e : LogEntry), boot[k]? = some e →
    ∃ id ctx, ps[k]? = some id ∧ ctxs[k]? = some ctx ∧ e.term = W64 1 ∧ e.type = W32 1 ∧
      -- `Bootstrap`'s `ConfChange{Type: ConfChangeAddNode, NodeID: id, Context: ctx}`
      MarshalsConfChange (some (.v1 ⟨W32 0, id, ctx, W64 0⟩)) e.data

/-- The Go entries of the log entries `l`, at the indices after `base`. -/
def LogEntry.toEntries (l : List LogEntry) (base : Nat) : List EntryM :=
  l.mapIdx fun i e => e.toEntryM (W64 (base + i + 1))

/-- The state of a node's `Ready` loop. -/
structure NodeDriverState where
  /-- the node's storage (fixed: the `Storage` it was started with), which a `Ready` hands the
  driver entries for, and `Advance` takes the receipt of -/
  storage : Storage
  /-- the committed log delivered so far (fillers included); after a `Ready` with a snapshot, the
  committed log up to the snapshot -/
  delivered : List LogEntry
  /-- the hard state last handed out -/
  hardState : HardStateM
  /-- while a `Ready` is being handled (between receiving it and `Advance`): its entries to persist,
  and its snapshot's loan, if it has one (the storage contract's vocabulary: `readyOut`,
  `advReceipt`) -/
  handling : Option (List EntryM × Option SnapLoan)

/-- The state a node's `Ready` loop starts in, at the storage `stor`. -/
def NodeDriverState.init (stor : Storage) : NodeDriverState := ⟨stor, [], hsZero, none⟩

end pure

section iprop
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The Go entries `sl` are the log entries `ce`, at the indices after `base` (read-only). -/
def committedEntriesAt (sl : GoSlice) (base : Nat) (ce : List LogEntry) : IProp GF :=
  entsRO sl (LogEntry.toEntries ce base)

instance committedEntriesAt_persistent (sl : GoSlice) (base : Nat) (ce : List LogEntry) :
    Persistent (committedEntriesAt (GF := GF) sl base ce) := by
  unfold committedEntriesAt; infer_instance

end iprop

end Draft
end EtcdGrove
end Perennial
