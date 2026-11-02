/-
# `MemoryStorage` at the node API (raft-final, 2026-10-29: U8 v2 step 4, the design's track P7)

The generic contract law (`memStorage_isStorageP`, `MemstorageInstance.lean`) at the API's
justifications (`memStorJ γ id`: the stored snapshots valid, `snapshotValid γ`; compaction within what
node `id` applied or a snapshot it handed out, `nodeAppliedLb`/`snapGiven`; a stored snapshot within
what was delivered, `storDL`): the storage's invariant `memStorInv ms γs γ id`, its allocation, and
`isStorage γ id` of a registered `MemoryStorage`. (A client whose `Storage` wraps a `MemoryStorage`,
kvreconf's, builds its own `StorageModel` instance over these: the design's A6, no wrapper law here.)

Stated in raft-final's phase 1, proved in its phase 2 (track P7): the allocation from
`memStorInvP_alloc` (index `0` justified by `nodeAppliedLb_zero`), the contract from
`memStorage_isStorageP` (`storBnd` is `memBnd` at `memStorJ`).
-/
module

public import Proof.go_etcd_io.raft.v3.MemstorageInstance
public import Proof.go_etcd_io.raft.v3.InvNodeRule

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section api
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
variable [MemStorReg GF]

/-- The API's justifications for the `MemoryStorage` of key `K` (`isStorage`'s pieces; 2026-11-01,
durability stage I-4: keyed by the storage's key, `snapGiven` merged into `nodeAppliedLb`). -/
def memStorJ (γ : Cluster) (K : GName) : MemJust GF where
  SV := snapshotValid γ
  B k := nodeAppliedLb γ K k
  DL := nodeCommitLb γ K
  SV_pers := fun sv => by infer_instance
  B_pers := fun k => by infer_instance
  B_timeless := fun k => by infer_instance
  DL_pers := fun i => by infer_instance

/-- **The `MemoryStorage` invariant of key `K`** (persistent): the generic one at the API's
justifications. -/
def memStorInv (ms : Loc) (γs : MemStorNames) (γ : Cluster) (K : GName) : IProp GF :=
  memStorInvP ms γs (memStorJ γ K)

instance memStorInv_persistent (ms : Loc) (γs : MemStorNames) (γ : Cluster) (K : GName) :
    Persistent (memStorInv (GF := GF) ms γs γ K) := by
  unfold memStorInv; infer_instance

/-- **The attach** (2026-11-01, durability stage I-4/I-5; until then from the fresh token at `0`):
from `NewMemoryStorage`'s detached token at the compaction point `c` and the stored snapshot `sv`,
once `InitialState` returned, with raft's bound at `c` (`nodeAppliedLb`, every lower point by
`nodeAppliedLb_mono`) and the stored snapshot's validity (the client's certificate, and raft's
commit bound at its index). It consumes the token: a storage is attached once. -/
theorem memStorInv_alloc (ms : Loc) (γs : MemStorNames) (γ : Cluster) (K : GName) (c : Nat)
    (sv : SnapshotM) (E : CoPset) :
    ⊢ memStorLock (GF := GF) ms γs -∗ memStorFresh ms γs c sv -∗ nodeAppliedLb γ K c -∗
      (⌜sv.Metadata'.Index' = W64 0⌝ ∨ snapshotValid γ sv ∗
        nodeCommitLb γ K (uint.nat sv.Metadata'.Index')) ={E}=∗
      memStorInv ms γs γ K := by
  -- PORT(durability stage II): restated (I-4: keyed by `K`, the generalized attach)
  sorry

/-- **A registered `MemoryStorage` meets the storage contract of key `K`.** -/
theorem memStorage_isStorage
    (wp_LastIndex : MemoryStorage.LastIndex.spec (GF := GF) (hG := hG))
    (wp_FirstIndex : MemoryStorage.FirstIndex.spec (GF := GF) (hG := hG))
    (wp_Term : MemoryStorage.Term.spec (GF := GF) (hG := hG))
    (wp_Entries : MemoryStorage.Entries.spec (GF := GF) (hG := hG))
    (wp_Snapshot : MemoryStorage.Snapshot.spec (GF := GF) (hG := hG))
    (ms : Loc) (γs : MemStorNames) (γ : Cluster) (K : GName) :
    ⊢ memStorInv (GF := GF) ms γs γ K -∗ memStorReg ms γs -∗ isStorage γ K (memStorIface ms) := by
  unfold memStorInv isStorage
  exact memStorage_isStorageP wp_LastIndex wp_FirstIndex wp_Term wp_Entries wp_Snapshot ms γs
    (memStorJ γ K)

end api

end EtcdGrove
end Perennial
