/-
The raft storage a restarting member builds from its WAL (`bootstrap.go`, etcd-io/etcd#19693,
"Bootstrap from backend position"; pr-verify, 2026-10-17). Lean-first (no Rocq counterpart).

With the PR, `bootstrapWALFromBackend` opens the WAL at the backend's position `pos` (its
consistent index and term, `schema.ReadConsistentIndex`) instead of at the latest snapshot, and
`bootstrappedWAL.MemoryStorage` applies a data-less snapshot at `pos` with the conf state (the
backend's, then the v3 store's, `bootstrap`), sets the WAL's hard state and appends the entries
the WAL holds after `pos`. This file has the pure model of that storage (`bwalStor`) and what
raft's restart asks of it (`RestartOk`).

**`RestartOk`** is `raft.loadState`'s premise (`Spec/go_etcd_io/raft/v3/raft__loadState.lean`:
`committed ≤ hs.Commit ≤ lastIndex`) at the log `newRaft` builds over a storage, whose
`committed` is the storage's first index minus one (`newLogWithSize`), its boundary
`σ.prev.index'`, and whose last index is `σ.prev.index' + |σ.ents|`. raft panics
(`"%x state.commit %d is out of range [%d, %d]"`) when it fails. (raft's `RestartNode.spec`
covers only a fresh storage, so the chain from `bwalStor` to `loadState` is not a theorem here:
`RestartOk` restates the premise on the storage.) `bwalStor_restartOk_iff` says what it is for
the storage `MemoryStorage()` builds: the WAL's commit index must lie between the backend's
consistent index and the WAL's last entry. Nothing in `bootstrapWALFromBackend` ensures the
lower bound off `--force-new-cluster` (`restartOk_counterexample`, and the Go test
`notes/pr-verify/etcd-19693/bootstrap_restart_test.go`).
-/
module

public import Proof.go_etcd_io.raft.v3.InvMemstorage
public import Code.go_etcd_io.etcd.server.v3.storage.wal

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open go_etcd_io.raft.v3

section pure
variable [FfiSyntax]

/-- The snapshot `MemoryStorage()` applies when there is a conf state: no data, at `pos` (index
and term), with the conf state `cs`. -/
def bwalSnap (pos : go_etcd_io.etcd.server.v3.storage.wal.Position) (cs : ConfStateM) :
    SnapshotM :=
  SnapshotM.mk [] (SnapshotMetadataM.mk cs pos.Index' pos.Term')

/-- The storage before the entries: the snapshot at `pos` if the conf state pointer `cp` is set,
else a fresh storage (`NewMemoryStorage`'s). -/
def bwalBase (pos : go_etcd_io.etcd.server.v3.storage.wal.Position) (cp : Loc) (cs : ConfStateM) :
    StorState :=
  if cp = null then memStorEmpty else memStorApplied (bwalSnap pos cs)

/-- The storage `MemoryStorage()` builds: the base, then the WAL's entries `p`. -/
def bwalStor (pos : go_etcd_io.etcd.server.v3.storage.wal.Position) (cp : Loc) (cs : ConfStateM)
    (p : List EntryM) : StorState :=
  { bwalBase pos cp cs with ents := p }

theorem bwalBase_ents_pend (pos : go_etcd_io.etcd.server.v3.storage.wal.Position) (cp : Loc)
    (cs : ConfStateM) : (bwalBase pos cp cs).ents = [] ∧ (bwalBase pos cp cs).pend = [] := by
  unfold bwalBase
  split <;> exact ⟨rfl, rfl⟩

/-- No entries: the storage is the base. -/
theorem bwalStor_nil (pos : go_etcd_io.etcd.server.v3.storage.wal.Position) (cp : Loc)
    (cs : ConfStateM) : bwalStor pos cp cs [] = bwalBase pos cp cs := by
  unfold bwalStor bwalBase
  split <;> rfl

/-- The entries appended to the base and absorbed (`Append`'s receipt) are `bwalStor`'s. -/
theorem bwalStor_absorb (pos : go_etcd_io.etcd.server.v3.storage.wal.Position) (cp : Loc)
    (cs : ConfStateM) (p : List EntryM) :
    storAbsorb { bwalBase pos cp cs with pend := p } = bwalStor pos cp cs p := by
  unfold storAbsorb storApp bwalStor bwalBase
  cases p <;> split <;> simp [memStorEmpty, memStorApplied]

/-- The append right's premise (`PendOk`) at the base, for entries continuing it. -/
theorem bwalBase_pendOk (pos : go_etcd_io.etcd.server.v3.storage.wal.Position) (cp : Loc)
    (cs : ConfStateM) (p : List EntryM) (Hne : p ≠ [])
    (Hhead : ∀ e0, p.head? = some e0 →
      uint.Z e0.Index' = uint.Z (bwalBase pos cp cs).prev.index' + 1) :
    PendOk (bwalBase pos cp cs) p := by
  refine ⟨Hne, fun e0 he => ?_⟩
  have h := Hhead e0 he
  rw [(bwalBase_ents_pend pos cp cs).1]
  simp only [List.length_nil]
  constructor <;> omega

/-- What raft's restart asks of the storage and the hard state: `raft.loadState`'s premise at
the log `newRaft` builds over the storage (see the file header). -/
def RestartOk (σ : StorState) (hs : HardStateM) : Prop :=
  uint.Z σ.prev.index' ≤ uint.Z hs.Commit' ∧
    uint.Z hs.Commit' ≤ uint.Z σ.prev.index' + (σ.ents.length : Int)

theorem bwalBase_prev_index (pos : go_etcd_io.etcd.server.v3.storage.wal.Position) (cp : Loc)
    (cs : ConfStateM) :
    (bwalBase pos cp cs).prev.index' = if cp = null then W64 0 else pos.Index' := by
  unfold bwalBase
  split <;> rfl

/-- With a conf state, the restart needs the WAL's commit index between the backend's
consistent index `pos.Index'` and the WAL's last entry. -/
theorem bwalStor_restartOk_iff (pos : go_etcd_io.etcd.server.v3.storage.wal.Position) (cp : Loc)
    (cs : ConfStateM) (p : List EntryM) (hs : HardStateM) (Hcp : cp ≠ null) :
    RestartOk (bwalStor pos cp cs p) hs ↔
      uint.Z pos.Index' ≤ uint.Z hs.Commit' ∧
        uint.Z hs.Commit' ≤ uint.Z pos.Index' + (p.length : Int) := by
  unfold RestartOk bwalStor
  simp only
  rw [bwalBase_prev_index]
  simp only [Hcp, if_false]

/-- `--force-new-cluster`'s commit index, `max(HardState.Commit, consistentIndex)`
(`bootstrapWALFromBackend`), meets the lower bound. -/
theorem force_commit_lower (ci old : w64) : uint.Z ci ≤ uint.Z (if uint.Z old < uint.Z ci then ci else old) := by
  split <;> word

/-- The PR's restart case the Go test `TestRestartWithConsistentIndexPastWALCommit` builds: the
backend at index 8 (term 1), the WAL's entries 9 and 10 after it, its last durable hard state
committing 5. The restart premise fails, so raft panics. -/
theorem restartOk_counterexample (cp : Loc) (cs : ConfStateM) (e9 e10 : EntryM) (Hcp : cp ≠ null) :
    ¬ RestartOk (bwalStor (go_etcd_io.etcd.server.v3.storage.wal.Position.mk (W64 1) (W64 8)) cp cs
        [e9, e10]) (HardStateM.mk (W64 1) (W64 1) (W64 5)) := by
  rw [bwalStor_restartOk_iff _ _ _ _ _ Hcp]
  simp only
  intro h
  have h1 := h.1
  word

end pure

end EtcdGrove
end Perennial
