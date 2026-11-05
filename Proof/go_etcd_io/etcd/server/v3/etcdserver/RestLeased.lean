/-
**The leased rest image** (the lease-grant stage, 2026-11-02; `notes/lease-grant-plan.md`, "Design
of the server chain", 2.0 and 2.14): in a cluster that grants leases, a snapshot's other buckets
are those of the committed log `L` with a record in `lease` for each id of `L`'s lease table, at
some TTL (`bkRestAtL`; the TTLs under `∃ f`, since each member's `minLeaseTTL` is its own, B1; at
least the grant's request, the lease-expiry plan's S2–S4, Q-S6 (A-ii)). The
send window's law (`bkRestAtL_of_rb`, as `bkRestAt_of_rb`), and how a committed entry's effect
commutes with a lease record (`restEntry_restGrantT`, through `ccValidOn_restGrantT`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRest
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.CindexBackend
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AppliedTable

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open backend go_etcd_io.etcd.server.v3.storage

/-- **`D`'s other buckets are the leased image of the committed log `L`**: `restModel`'s, with
the records of `L`'s live leases at some TTLs; (the lease-expiry plan's S2–S4, Q-S6 (A-ii),
2026-11-05) each at least its grant's request (`leaseTTLsAbove`, the table's TTLs). -/
def bkRestAtL [GooseExts] (γk : KVNames) (bootLog : List EntryM) (L : List EntryModel) (D : Data) :
    Prop :=
  ∃ f : w64 → w64, leaseTTLsAbove (kvLeases γk L) f ∧ ∀ n ∈ mvcc.restBuckets,
    D.lookup n = (apply.restLeasesWith f (kvLeases γk L).ids (restModel γk.c0 bootLog L)).bk.lookup n

/-- **The leased rest buckets of a snapshot's data from its observation** (as `bkRestAt_of_rb`):
the tracked buckets `rbData P D` the leased image's. -/
theorem bkRestAtL_of_rb {P : BParams} (hRB : ∀ n ∈ mvcc.restBuckets, P.RB n = true)
    [GooseExts] {γk : KVNames} {bootLog : List EntryM} {L : List EntryModel} {D : Data}
    (f : w64 → w64) (hf : leaseTTLsAbove (kvLeases γk L) f)
    (hrb : rbData P D =
      (apply.restLeasesWith f (kvLeases γk L).ids (restModel γk.c0 bootLog L)).bk) :
    bkRestAtL γk bootLog L D := by
  refine ⟨f, hf, fun n hn => ?_⟩
  have := congrArg (fun r => GMap.lookup r n) hrb
  simp only [rbData_lookup, hRB n hn, ↓reduceIte] at this
  exact this

/-- **A lease record leaves a conf change's verdict**: `ccValidOn` reads only the `members` and
`members_removed` buckets (`membersOfBk`, since 2026-11-03 the user's (A)), and the record is in
`lease`. -/
theorem ccValidOn_restGrantT [GooseExts] (cc : ConfChangeM) (id t : w64) (r : apply.RestM) :
    membership.ccValidOn (apply.restGrantT id t r).bk cc = membership.ccValidOn r.bk cc := by
  have hm : mvcc.leaseName ≠ go!"members" := by decide
  have hr : mvcc.leaseName ≠ go!"members_removed" := by decide
  unfold membership.ccValidOn membership.membersOfBk apply.restGrantT
  rw [putIn_other _ _ _ _ _ hm, putIn_other _ _ _ _ _ hr]

/-- **A conf change commutes with a lease record**. -/
theorem ccRest_restGrantT [GooseExts] (v3 : Bool) (cc : ConfChangeM) (id t : w64) (r : apply.RestM) :
    ccRest v3 cc (apply.restGrantT id t r) = apply.restGrantT id t (ccRest v3 cc r) := by
  have hm : go!"members" ≠ mvcc.leaseName := by decide
  have hr : go!"members_removed" ≠ mvcc.leaseName := by decide
  unfold ccRest
  rw [ccValidOn_restGrantT]
  split
  · split
    · rw [apply.restGrantT_putIn _ _ _ _ _ _ hm]; rfl
    · split
      · rw [apply.restGrantT_putIn _ _ _ _ _ _ hr, apply.restGrantT_delIn _ _ _ _ _ hm]; rfl
      · rfl
  · rfl

/-- **A committed entry commutes with a lease record**: a normal entry (`restAfter_restGrantT`) and
a conf change (`ccRest_restGrantT`). -/
theorem restEntry_restGrantT [GooseExts] (c0 : w64) (m : EntryModel) (id t : w64) (r : apply.RestM) :
    restEntry c0 m (apply.restGrantT id t r) = apply.restGrantT id t (restEntry c0 m r) := by
  unfold restEntry
  split
  · split
    · rfl
    · split
      · exact apply.restAfter_restGrantT _ _ _ _ _
      · rfl
  · split
    · exact ccRest_restGrantT _ _ _ _ _
    · rfl

/-! ### Across all the records (2.14's conf-change arm, the plumbing's S2) -/

/-- **The records leave every other bucket.** -/
theorem restLeasesWith_lookup_other [GooseExts] (f : w64 → w64) (ids : List w64) (r : apply.RestM)
    (n : GoString) (hn : mvcc.leaseName ≠ n) :
    (apply.restLeasesWith f ids r).bk.lookup n = r.bk.lookup n := by
  unfold apply.restLeasesWith
  induction ids generalizing r with
  | nil => rfl
  | cons id ids ih =>
    rw [List.foldl_cons, ih]
    unfold apply.restGrantT
    exact putIn_other _ _ _ _ _ hn

theorem membersOfBk_restLeasesWith [GooseExts] (f : w64 → w64) (ids : List w64) (r : apply.RestM) :
    membership.membersOfBk (apply.restLeasesWith f ids r).bk = membership.membersOfBk r.bk := by
  unfold membership.membersOfBk
  rw [restLeasesWith_lookup_other _ _ _ _ (by decide), restLeasesWith_lookup_other _ _ _ _ (by decide)]

theorem ccValidOn_restLeasesWith [GooseExts] (f : w64 → w64) (ids : List w64) (r : apply.RestM)
    (cc : ConfChangeM) :
    membership.ccValidOn (apply.restLeasesWith f ids r).bk cc = membership.ccValidOn r.bk cc := by
  unfold membership.ccValidOn; rw [membersOfBk_restLeasesWith]

theorem ccRaftEff_restLeasesWith [GooseExts] (f : w64 → w64) (ids : List w64) (r : apply.RestM)
    (cc : ConfChangeM) :
    membership.ccRaftEff (apply.restLeasesWith f ids r).bk cc = membership.ccRaftEff r.bk cc := by
  unfold membership.ccRaftEff; rw [ccValidOn_restLeasesWith]

theorem membersDecode_restLeasesWith [GooseExts] (f : w64 → w64) (ids : List w64) (r : apply.RestM)
    (h : membership.membersDecode r.bk) :
    membership.membersDecode (apply.restLeasesWith f ids r).bk := by
  unfold membership.membersDecode
  rw [restLeasesWith_lookup_other _ _ _ _ (by decide), restLeasesWith_lookup_other _ _ _ _ (by decide)]
  exact h

theorem ccRest_restLeasesWith [GooseExts] (v3 : Bool) (cc : ConfChangeM) (f : w64 → w64)
    (ids : List w64) (r : apply.RestM) :
    ccRest v3 cc (apply.restLeasesWith f ids r) = apply.restLeasesWith f ids (ccRest v3 cc r) :=
  apply.restLeasesWith_comm _ (ccRest_restGrantT v3 cc) f ids r

end EtcdGrove
end Perennial
