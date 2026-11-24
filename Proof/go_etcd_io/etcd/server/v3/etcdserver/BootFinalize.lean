/-
**Pure facts for `Finalize`'s proof** (claim #34, stage 2, 2026-11-25): the new cluster's members map
(`bootGo.memMap`) holds every peer and is no larger than the initial cluster; the backend's data with
the membership buckets created (`bootGo.withMemBkts`) has the same readers' view, compaction keys
and, at the tracked buckets, the contents `MustCreateBackendBuckets` leaves in the part
(`schema.withMemBkts`). A defs module. Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BootParts
public import Proof.go_etcd_io.etcd.server.v3.storage.schema.MemberBktsFresh

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bootGo

/-- A key is in a map built by inserting the members `L` (each under its id) into `acc` iff it is
one of their ids or `acc`'s. -/
theorem foldl_insert_isSome (L : List apply.MemberM) (acc : GMap w64 apply.MemberM) (k : w64) :
    ((L.foldl (fun mem m => mem.insert m.id m) acc) !! k).isSome ↔
      (k ∈ L.map (·.id) ∨ (acc !! k).isSome) := by
  induction L generalizing acc with
  | nil => simp
  | cons x L ih =>
    rw [List.foldl_cons, ih]
    simp only [List.map_cons, List.mem_cons, GMap.lookup_insert_eq_iff]
    by_cases h : x.id = k
    · subst h; simp
    · have h' : k ≠ x.id := fun e => h e.symm
      simp [h, h']

/-- The members map's keys are the peers. -/
theorem memMap_isSome [GooseExts] (U : BootURLs) (tok : GoString) (k : w64) :
    ((memMap U tok) !! k).isSome ↔ k ∈ ps U tok := by
  unfold memMap ps
  rw [foldl_insert_isSome]
  simp [GMap.lookup_empty]

/-- The members map is no larger than the initial cluster. -/
theorem memMap_size_le [GooseExts] (U : BootURLs) (tok : GoString) :
    GMap.size (memMap U tok) ≤ GMap.size U.initMap := by
  rw [GMap.size_eq_dom_list_length, GMap.size_eq_dom_list_length U.initMap]
  have hsub : (memMap U tok).domList ⊆ ps U tok := by
    intro k hk
    rw [GMap.mem_dom_list] at hk
    exact (memMap_isSome U tok k).1 hk
  have h := List.Nodup.length_le_of_subset (GMap.nodup_dom_list _) hsub
  have hl : (ps U tok).length = U.initMap.domList.length := by
    unfold ps members; simp
  omega

/-- The data with the membership buckets created reads the same. -/
theorem dget_withMemBkts [GooseExts] (D : backend.Data) :
    backend.dget (withMemBkts D) = backend.dget D := by
  funext n k
  unfold backend.dget
  rw [withMemBkts_lookup]
  split
  · unfold backend.bktOf
    cases hD : D.lookup n with
    | none => first | rfl | simp
    | some m => rfl
  · rfl

/-- `dget_withMemBkts`, applied (for `simp` under binders and `decide`). -/
theorem dget_withMemBkts_app [GooseExts] (D : backend.Data) (n k : GoString) :
    backend.dget (withMemBkts D) n k = backend.dget D n k := by
  rw [dget_withMemBkts]

/-- The readers' view of the data with the membership buckets created is the data's. -/
theorem vData_withMemBkts [GooseExts] (P : backend.BParams) (D : backend.Data) :
    backend.vData P (withMemBkts D, ⟨∅, W64 0⟩) = backend.vData P (D, ⟨∅, W64 0⟩) := by
  apply GMap.ext
  intro nk
  simp only [backend.vData, backend.vOf, dget_withMemBkts]

/-- The tracked buckets of the data with the membership buckets created are the part's
`MustCreateBackendBuckets` leaves (the three buckets are tracked by the real backend). -/
theorem rbData_withMemBkts [GooseExts] (d : mvcc.KBReal) (D : backend.Data) (n : GoString) :
    (backend.rbData d.P (withMemBkts D)).lookup n =
      (schema.withMemBkts (backend.rbData d.P D)).lookup n := by
  rw [backend.rbData_lookup d.P (withMemBkts D) n, schema.withMemBkts_lookup, withMemBkts_lookup]
  by_cases h : n = go!"cluster" ∨ n = go!"members_removed" ∨ n = go!"members"
  · have hRB : d.P.RB n = true := by
      rcases h with rfl | rfl | rfl <;> simp [mvcc.KBReal.P, mvcc.restBuckets]
    simp only [if_pos h, if_pos hRB]
    unfold backend.bktOf
    rw [backend.rbData_lookup, if_pos hRB]
  · simp only [if_neg h]
    rw [backend.rbData_lookup]

section iprops
open Iris Iris.BI Iris.ProofMode
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- The compaction keys' state of the data with the membership buckets created is the data's. -/
theorem fkCl_withMemBkts (γ : backend.BNames) (P : backend.BParams) (D : backend.Data) :
    backend.fkCl (GF := GF) γ P (withMemBkts D) = backend.fkCl γ P D := by
  unfold backend.fkCl
  simp only [backend.fkInit, backend.fkVals, backend.fkWInit, backend.fkAbsD, backend.fkWfD,
    dget_withMemBkts_app]

end iprops

end bootGo
end EtcdGrove
end Perennial
