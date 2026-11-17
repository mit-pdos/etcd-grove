/-
The declarations `walFresh`, `walSaveSnap`, `walSaveSnap_base_ge` of
`Proof/go_etcd_io/etcd/server/v3/storage/WalRecs.lean`, split from it so that the WAL
(`Proof/go_etcd_io/etcd/server/v3/storage/wal/`) imports them without the rest (until 2026-11-15 an
extract of `etc/gen-part-copies.py` for the part `LinuxFs/`; notes/wal-lean-integration.md). The
source imports this module.
-/
module

public import Proof.go_etcd_io.raft.v3.NodeApiVocabCore
public import Proof.go_etcd_io.raft.v3.Protocol.CommitWitCore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section extract
variable [GooseExts]

/-- **The records of a new WAL** (`wal.Create`: the initial snapshot record at `⟨0, 0⟩`, no
entries, no hard state). -/
def walFresh : StorContents :=
  ⟨HardStateM.mk (W64 0) (W64 0) (W64 0), none, entryID.mk (W64 0) (W64 0), []⟩

/-- **The records after `SaveSnap(m)`**: a record below the base changes nothing (the restart
opens at the highest record); otherwise they start at `m` (its index and term, the snapshot `m`
without data: the WAL keeps the metadata), the entries above it kept when `m` is within the saved
commit (a snapshot of the applied log) and dropped when above it (a received snapshot: raft
discarded its log). The hard state kept. -/
def walSaveSnap (σ : StorContents) (m : SnapshotMetadataM) : StorContents :=
  if uint.nat m.Index' < σ.b then σ else
  { σ with
    base := entryID.mk m.Term' m.Index'
    snap := some (SnapshotM.mk [] m)
    ents := if uint.nat m.Index' ≤ σ.commit then σ.ents.drop (uint.nat m.Index' - σ.b) else [] }

/-- After `SaveSnap(m)` the base is at least `m`'s index (a record below it changes nothing, above
it starts the records), and at least the old base. -/
theorem walSaveSnap_base_ge (σ : StorContents) (m : SnapshotMetadataM) :
    σ.b ≤ (walSaveSnap σ m).b ∧ (uint.nat m.Index' ≤ (walSaveSnap σ m).b ∨ uint.nat m.Index' < σ.b) := by
  unfold walSaveSnap
  split
  · next h => exact ⟨Nat.le_refl _, Or.inr h⟩
  · next h =>
    simp only [StorContents.b] at h ⊢
    exact ⟨by omega, Or.inl (Nat.le_refl _)⟩

end extract

end EtcdGrove
end Perennial
