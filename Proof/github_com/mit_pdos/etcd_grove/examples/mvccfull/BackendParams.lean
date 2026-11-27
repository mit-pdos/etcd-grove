/-
The tester's backend parameters (`examples/mvccfull`, `runner.openBackend`): schema's `Key`, `Meta`
and `Lease` buckets (the store's and the lessor's), mvcc's layout (`bridgeParams`), the lessor's
(`leaseParams`), no hook of its own (`hookMax = 0`: the tester's backend has no `BackendHooks`),
compaction mode on (the store's `New`), the batch limit the configuration's. Lean-first (no Rocq
counterpart). Until 2026-11-25 in `examples/mvccrand`'s `RunChecksBackend.lean` (as `mvccrand.rcP`,
...), moved here when mvccrand was retired (#49).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.StopCensus
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.New
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.RdPool
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBatch
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.EtcdBackend
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorBackend
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Lemmas

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProofMode mvcc mvcc.api

section params
variable [GooseExts]

/-- The tester's bucket table: schema's `Key`, `Meta` and `Lease`. -/
def rcBT : GMap GoString w64 :=
  (((∅ : GMap GoString w64).insert keyName (W64 1)).insert
    go_etcd_io.etcd.server.v3.storage.schema.metaName (W64 2)).insert leaseName (W64 3)

/-- **The tester's backend instance** (`backend.New`'s `γB`, its `*backend`, the store's
registration name `gx`), with the batch limit `lim`. -/
abbrev rcKB (γB : backend.BNames) (be : Loc) (gx : GName) (lim : w64) : KBReal :=
  ⟨γB, rcBT, 0, lim, be, gx, true⟩

/-- **The tester's backend parameters** (`rcKB`'s, whatever its names). -/
def rcP (lim : w64) : backend.BParams :=
  { BT := rcBT, HB := fun n => decide (n ≠ keyName), SB := fun n => decide (n = keyName),
    HK := fun n k => decide (n = go_etcd_io.etcd.server.v3.storage.schema.metaName ∧
      (k = go_etcd_io.etcd.server.v3.storage.schema.ciKeyBytes ∨
        k = go_etcd_io.etcd.server.v3.storage.schema.termKeyBytes ∨
        k = go_etcd_io.etcd.server.v3.storage.schema.raftTermKeyBytes)),
    RB := fun n => decide (n ∈ restBuckets), hookMax := 0, limit := lim, FV := metaRevVal }

theorem rcKB_P (γB : backend.BNames) (be : Loc) (gx : GName) (lim : w64) :
    (rcKB γB be gx lim).P = rcP lim := rfl

theorem rcKB_γB (γB : backend.BNames) (be : Loc) (gx : GName) (lim : w64) :
    (rcKB γB be gx lim).γB = γB := rfl

theorem rcKB_be (γB : backend.BNames) (be : Loc) (gx : GName) (lim : w64) :
    (rcKB γB be gx lim).be = be := rfl

theorem rcKB_gx (γB : backend.BNames) (be : Loc) (gx : GName) (lim : w64) :
    (rcKB γB be gx lim).gx = gx := rfl

theorem rcBT_key : rcBT.lookup keyName = some (W64 1) := by
  unfold rcBT
  rw [GMap.lookup_insert_ne _ _ (by decide), GMap.lookup_insert_ne _ _ (by decide),
    GMap.lookup_insert]

theorem rcBT_meta :
    rcBT.lookup go_etcd_io.etcd.server.v3.storage.schema.metaName = some (W64 2) := by
  unfold rcBT
  rw [GMap.lookup_insert_ne _ _ (by decide), GMap.lookup_insert]

theorem rcBT_lease : rcBT.lookup leaseName = some (W64 3) := by
  unfold rcBT
  rw [GMap.lookup_insert]

theorem rcBT_lookup (n : GoString) (i : w64) (h : rcBT.lookup n = some i) :
    (n = keyName ∧ i = W64 1) ∨ (n = go_etcd_io.etcd.server.v3.storage.schema.metaName ∧ i = W64 2) ∨
      (n = leaseName ∧ i = W64 3) := by
  unfold rcBT at h
  by_cases h3 : n = leaseName
  · subst h3; rw [GMap.lookup_insert] at h; cases h; exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  rw [GMap.lookup_insert_ne _ _ (Ne.symm h3)] at h
  by_cases h2 : n = go_etcd_io.etcd.server.v3.storage.schema.metaName
  · subst h2; rw [GMap.lookup_insert] at h; cases h; exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  rw [GMap.lookup_insert_ne _ _ (Ne.symm h2)] at h
  by_cases h1 : n = keyName
  · subst h1; rw [GMap.lookup_insert] at h; cases h; exact Or.inl ⟨rfl, rfl⟩
  rw [GMap.lookup_insert_ne _ _ (Ne.symm h1)] at h
  simp at h

/-- The parameters are sane (`backend.New`'s premise), at a limit in range. -/
theorem rcP_wf (lim : w64) (h0 : 0 < sint.Z lim) (h1 : sint.Z lim ≤ 2 ^ 57) : (rcP lim).Wf := by
  refine ⟨?_, h0, h1, by simp [rcP], ?_⟩
  · intro n1 n2 i e1 e2
    rcases rcBT_lookup n1 i e1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases rcBT_lookup n2 _ e2 with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ <;>
    first | rfl | (exfalso; revert h; decide)
  · intro n h
    simp only [rcP, decide_eq_true_eq] at h ⊢
    simp [h]

/-- mvcc's layout. -/
theorem rcP_bridge (lim : w64) : bridgeParams (rcP lim) := by
  refine ⟨rcBT_key, rcBT_meta, fun _ => rfl, fun _ => rfl, ?_, ?_⟩ <;> simp only [rcP] <;> decide

/-- The lessor's layout. -/
theorem rcP_lease (lim : w64) : leaseParams (rcP lim) := by
  refine ⟨rcBT_lease, by simp only [rcP]; decide, fun k => ?_⟩
  have h : leaseName ≠ go_etcd_io.etcd.server.v3.storage.schema.metaName := by decide
  simp only [backend.BParams.hk, rcP, h, false_and, decide_false, Bool.and_false]

end params

end mvccfull
end EtcdGrove
end Perennial
