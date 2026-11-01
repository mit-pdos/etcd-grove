/- `NewMemoryStorage` (`storage.go:113`; U8 v2 step 3): the fields at the dummy alone, the ghost
state of `MemStorNames` (the map `{0 ↦ e₀}` with the dummy frozen, the end at `1`, the compaction
point `0` justified, the empty stored snapshot, the keys), the mutex allocated around them, and the
snapshot `EnsureSnapshot(nil)` makes, the allocation's fuel. -/
module

public import Spec.go_etcd_io.raft.v3.NewMemoryStorage
public import Spec.go_etcd_io.raft.v3.raftpb.EnsureSnapshot
public import Proof.go_etcd_io.raft.v3.LemmasMemstorage

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The lock's knowledge at the start: the dummy `0` alone, the map `{0 ↦ e₀}`. -/
theorem memOk_new :
    MemOk (entryID.mk (W64 0) (W64 0)) [] ((∅ : GMap Nat EntryM).insert 0 (zero_val EntryM))
      memSnapEmpty := by
  refine ⟨by simp, fun i hi => ?_, fun i h1 h2 => ?_, by simp [memSnapEmpty], by simp [memSnapEmpty],
    fun j e h => by simp at h⟩
  · simp only [List.length_nil] at hi
    rw [GMap.lookup_insert_ne _ _ (by simp at hi ⊢; omega)]
    exact GMap.lookup_empty _
  · simp at h1 h2; omega

theorem NewMemoryStorage.wp_proof
    (wp_EnsureSnapshot : raftpb.EnsureSnapshot.spec (GF := GF) (hG := hG)) :
    NewMemoryStorage.spec (GF := GF) (hG := hG) := by
  sorry -- durability stage I (I-5): statement changed (mode o / detached memStorFresh c sv)

end proof

end EtcdGrove
end Perennial
