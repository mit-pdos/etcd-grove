/-
# `MemoryStorage` at the node API (raft-final, 2026-10-29: U8 v2 step 4, the design's track P7)

The generic contract law (`memStorage_isStorageP`, `MemstorageInstance.lean`) at the API's
justifications (`memStorJ γ id`: the stored snapshots valid, `snapshotValid γ`; compaction within what
node `id` applied or a snapshot it handed out, `nodeAppliedLb`/`snapGiven`; a stored snapshot within
what was delivered, `storDL`): the storage's invariant `memStorInv ms γs γ id`, its allocation, and
`isStorage γ id` of a registered `MemoryStorage`. (A client whose `Storage` wraps a `MemoryStorage`,
kvreconf's, builds its own `StorageModel` instance over these: the design's A6, no wrapper law here.)

Statements only in raft-final's phase 1 (`notes/raft-unified-plan.md`, "Phase 1 sorries"): proved by
phase 2's track P7.
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

/-- The API's justifications for node `id`'s `MemoryStorage` (`isStorage`'s pieces). -/
def memStorJ (γ : Cluster) (id : w64) : MemJust GF where
  SV := snapshotValid γ
  B k := iprop(nodeAppliedLb γ id k ∨ snapGiven γ id k)
  DL := storDL γ id
  SV_pers := fun sv => by infer_instance
  B_pers := fun k => by infer_instance
  B_timeless := fun k => by infer_instance
  DL_pers := fun i => by unfold storDL; infer_instance

/-- **Node `id`'s `MemoryStorage` invariant** (persistent): the generic one at the API's
justifications. -/
def memStorInv (ms : Loc) (γs : MemStorNames) (γ : Cluster) (id : w64) : IProp GF :=
  memStorInvP ms γs (memStorJ γ id)

instance memStorInv_persistent (ms : Loc) (γs : MemStorNames) (γ : Cluster) (id : w64) :
    Persistent (memStorInv (GF := GF) ms γs γ id) := by
  unfold memStorInv; infer_instance

/-- Its allocation, from `NewMemoryStorage`'s fuel (`memStorFresh`) once `InitialState` returned. -/
theorem memStorInv_alloc (ms : Loc) (γs : MemStorNames) (γ : Cluster) (id : w64) (E : CoPset) :
    ⊢ memStorLock (GF := GF) ms γs -∗ memStorFresh ms γs ={E}=∗ memStorInv ms γs γ id := by
  sorry

/-- **A registered `MemoryStorage` meets node `id`'s storage contract.** -/
theorem memStorage_isStorage
    (wp_LastIndex : MemoryStorage.LastIndex.spec (GF := GF) (hG := hG))
    (wp_FirstIndex : MemoryStorage.FirstIndex.spec (GF := GF) (hG := hG))
    (wp_Term : MemoryStorage.Term.spec (GF := GF) (hG := hG))
    (wp_Entries : MemoryStorage.Entries.spec (GF := GF) (hG := hG))
    (wp_Snapshot : MemoryStorage.Snapshot.spec (GF := GF) (hG := hG))
    (ms : Loc) (γs : MemStorNames) (γ : Cluster) (id : w64) :
    ⊢ memStorInv (GF := GF) ms γs γ id -∗ memStorReg ms γs -∗ isStorage γ id (memStorIface ms) := by
  sorry

end api

end EtcdGrove
end Perennial
