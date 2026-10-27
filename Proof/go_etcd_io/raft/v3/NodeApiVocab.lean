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

/-- **A filler**: an entry that carries nothing, an empty normal entry. Raft appends these itself:
a new leader's entry (`raft.go:961`), the entry in place of a conf change it refuses
(`raft.go:1341`). A client's empty proposal looks the same, so it is a filler too: an operation must
be encoded as non-empty bytes to take effect as one. (2026-10-27: until then also an empty
`ConfChangeV2`, raft's auto-leave entry, `raft.go:742`, which raft's proof shows is never appended,
and a client's empty `ConfChangeV2`, which is now a requested entry like any conf change.) -/
def LogEntry.isFiller (e : LogEntry) : Prop :=
  e.data = [] ∧ e.type = W32 0

instance (e : LogEntry) : Decidable e.isFiller := by unfold LogEntry.isFiller; infer_instance

/-- **A filler is a normal entry** (`EntryNormal`): what etcd's apply loop needs, which panics on an
entry of type `EntryConfChangeV2`. (2026-10-27, in place of the server port's `noConfChangeV2`.) -/
theorem LogEntry.isFiller_normal (e : LogEntry) (h : e.isFiller) : e.type = W32 0 := h.2

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

/-! ### The configuration, abstractly (2026-10-27, for etcd's server: moved from the draft) -/

/-- **A cluster's membership**, as raft's `ConfState` reports it (a `tracker.Config` without the
progress map): the voters, the outgoing voters of a joint configuration, the learners, the learners
to add when the joint configuration is left, and whether it is left automatically. -/
structure Membership where
  voters : GSet w64
  votersOutgoing : GSet w64
  learners : GSet w64
  learnersNext : GSet w64
  autoLeave : Bool

/-- The membership of the voters `vs` only (not joint, no learners): every membership etcd's server
uses. -/
def Membership.simple (vs : GSet w64) : Membership := ⟨vs, ∅, ∅, ∅, false⟩

/-- **A `ConfState` reports the membership `m`**: its four lists hold `m`'s four sets (in some
order, without repeats), its `AutoLeave` is `m`'s. (Today `confstateOk`.) -/
def confStateIs (cs : ConfStateM) (m : Membership) : Prop :=
  cs.Voters' ≡ₚ elements m.voters ∧ cs.VotersOutgoing' ≡ₚ elements m.votersOutgoing ∧
    cs.Learners' ≡ₚ elements m.learners ∧ cs.LearnersNext' ≡ₚ elements m.learnersNext ∧
    cs.AutoLeave' = m.autoLeave

/-- **A conf-change entry**: of type `EntryConfChange` (1) or `EntryConfChangeV2` (2). -/
def LogEntry.isConfChange (e : LogEntry) : Prop := e.type = W32 1 ∨ e.type = W32 2

/-- No conf-change entry at the positions `[lo, hi)` of the log `l`. (Today `NoConfIn`.) -/
def NoConfChangeIn (l : List LogEntry) (lo hi : Nat) : Prop :=
  ∀ (k : Nat) (e : LogEntry), lo ≤ k → k < hi → l[k]? = some e → ¬ e.isConfChange

/-- **A conf-change decoder**: the change a conf-change entry makes, given the committed log before
it (fillers included). Fixed when a dynamic cluster is allocated: every node must apply the same
change for the same committed entry (raft's `CCDec`; etcd's server validates a change against the
membership the log before it leaves, and hands raft a refused one with `NodeID = 0`). -/
abbrev ConfChangeDecoder := List LogEntry → LogEntry → Option ConfChangeIM

/-- **A node's view of its configuration**: the conf-change entries of the committed log below
position `applied` are applied (`node.ApplyConfChange`), and the membership they give. (Today
`nodeCfg`'s `(ca, cfg)`.) -/
structure ConfigView where
  applied : Nat
  membership : Membership


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
