Require Export New.proof.go_etcd_io.raft.election_proof.inv_storage.
From New.proof Require Import sync.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

(** What the lock protects, at a given abstract state, *without* the ghost
    link: the five fields other than the mutex, and everything hanging off
    them.  This is what the private helpers [lastIndex]/[firstIndex] are
    specified on -- they are called with the lock held -- and what a public
    method holds between [Lock] and [Unlock]. *)
Definition memstorage_fields (ms : loc) (prev : raft.entryID.t)
    (ents : list raftpb.Entry.t) (ss : raft.entryID.t) : iProp Σ :=
  ∃ (hs : raftpb.HardState.t) (snap : raftpb.Snapshot.t) (es : slice.t)
    (dummy : raftpb.Entry.t) (cs : raft.inMemStorageCallStats.t)
    (voters : list w64),
  "HhardState" ∷ ms.[raft.MemoryStorage.t, "hardState"] ↦ hs ∗
  "Hsnapshot" ∷ ms.[raft.MemoryStorage.t, "snapshot"] ↦ snap ∗
  "%Hsnap_id" ∷ ⌜ snap_id snap = ss ⌝ ∗
  "Hvoters" ∷ snap.(raftpb.Snapshot.Metadata').(raftpb.SnapshotMetadata.ConfState')
                .(raftpb.ConfState.Voters') ↦*□ voters ∗
  "Hents_f" ∷ ms.[raft.MemoryStorage.t, "ents"] ↦ es ∗
  "Hents" ∷ es ↦*□ (dummy :: ents) ∗
  "%Hdummy" ∷ ⌜ dummy.(raftpb.Entry.Index') = prev.(raft.entryID.index') ∧
                dummy.(raftpb.Entry.Term') = prev.(raft.entryID.term') ⌝ ∗
  "HcallStats" ∷ ms.[raft.MemoryStorage.t, "callStats"] ↦ cs.

(** The lock's invariant: the abstract state, half of the ghost variable that
    records it, and the fields at that state. *)
Definition memstorage_inv (ms : loc) (γ : gname) : iProp Σ :=
  ∃ (prev : raft.entryID.t) (ents : list raftpb.Entry.t) (ss : raft.entryID.t),
  "Hgs" ∷ ghost_var γ (1/2) (prev, ents, ss) ∗
  "Hfields" ∷ memstorage_fields ms prev ents ss.

Definition own_MemoryStorage (ms : loc) (prev : raft.entryID.t)
    (ents : list raftpb.Entry.t) (ss : raft.entryID.t) : iProp Σ :=
  ∃ (γ : gname),
  "#Hinit" ∷ is_pkg_init raft ∗
  "#Hmu" ∷ is_Mutex (ms.[raft.MemoryStorage.t, "Mutex"]) (memstorage_inv ms γ) ∗
  "Hgs" ∷ ghost_var γ (1/2) (prev, ents, ss) ∗
  "%Hbounded" ∷ ⌜ (uint.Z prev.(raft.entryID.index') + Z.of_nat (length ents) < 2^61)%Z ⌝ ∗
  "%Hss" ∷ ⌜ ss.(raft.entryID.index') ≠ W64 0 ⌝.

(** The two facts [is_Storage] wants of an ownership predicate that are not
    method specs, read out of [own_MemoryStorage] without consuming it.  The
    package initializer is in the predicate because the methods take the
    lock, which needs [is_pkg_init sync]; [is_Storage]'s method triples have
    no such premise. *)
Lemma own_MemoryStorage_init ms prev ents ss :
  own_MemoryStorage ms prev ents ss -∗
  is_pkg_init raft ∗ own_MemoryStorage ms prev ents ss.
Proof.
  iIntros "H". iNamed "H". iFrame "∗#%".
Qed.

Lemma own_MemoryStorage_bounded ms prev ents ss :
  own_MemoryStorage ms prev ents ss -∗
  ⌜ (uint.Z prev.(raft.entryID.index') + Z.of_nat (length ents) < 2^61)%Z ⌝ ∗
  own_MemoryStorage ms prev ents ss.
Proof.
  iIntros "H". iNamed "H". iFrame "∗#%".
Qed.

End proof.
