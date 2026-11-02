/-
**The leased rest image** (the lease-grant stage, 2026-11-02; `notes/lease-grant-plan.md`, "Design
of the server chain", 2.0 and 2.14): in a cluster that grants leases, a snapshot's other buckets
are those of the committed log `L` with a record in `lease` for each id of `L`'s lease table, at
some TTL (`bkRestAtL`; the TTLs under `∃ f`, since each member's `minLeaseTTL` is its own, B1). The
send window's law (`bkRestAtL_of_rb`, as `bkRestAt_of_rb`), and how a committed entry's effect
commutes with a lease record (`restEntry_restGrantT`). Lean-first (no Rocq counterpart).
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
the records of `L`'s live leases at some TTLs. -/
def bkRestAtL [GooseExts] (γk : KVNames) (bootLog : List EntryM) (L : List EntryModel) (D : Data) :
    Prop :=
  ∃ f : w64 → w64, ∀ n ∈ mvcc.restBuckets,
    D.lookup n = (apply.restLeasesWith f (kvLeases γk L).ids (restModel γk.c0 bootLog L)).bk.lookup n

/-- **The leased rest buckets of a snapshot's data from its observation** (as `bkRestAt_of_rb`):
the tracked buckets `rbData P D` the leased image's. -/
theorem bkRestAtL_of_rb {P : BParams} (hRB : ∀ n ∈ mvcc.restBuckets, P.RB n = true)
    [GooseExts] {γk : KVNames} {bootLog : List EntryM} {L : List EntryModel} {D : Data}
    (f : w64 → w64)
    (hrb : rbData P D =
      (apply.restLeasesWith f (kvLeases γk L).ids (restModel γk.c0 bootLog L)).bk) :
    bkRestAtL γk bootLog L D := by
  refine ⟨f, fun n hn => ?_⟩
  have := congrArg (fun r => GMap.lookup r n) hrb
  simp only [rbData_lookup, hRB n hn, ↓reduceIte] at this
  exact this

/-- **A conf change commutes with a lease record** when the record leaves its validation (the
verdict `ccValidOn` reads the tracked buckets through the opaque `membersOfBk`, so whether a lease
record changes it is not known here: `notes/lease-grant-plan.md`, "Plumbing"). -/
theorem ccRest_restGrantT [GooseExts] (v3 : Bool) (cc : ConfChangeM) (id t : w64) (r : apply.RestM)
    (hv : membership.ccValidOn (apply.restGrantT id t r).bk cc = membership.ccValidOn r.bk cc) :
    ccRest v3 cc (apply.restGrantT id t r) = apply.restGrantT id t (ccRest v3 cc r) := by
  have hm : go!"members" ≠ mvcc.leaseName := by decide
  have hr : go!"members_removed" ≠ mvcc.leaseName := by decide
  unfold ccRest
  rw [hv]
  split
  · split
    · rw [apply.restGrantT_putIn _ _ _ _ _ _ hm]; rfl
    · split
      · rw [apply.restGrantT_putIn _ _ _ _ _ _ hr, apply.restGrantT_delIn _ _ _ _ _ hm]; rfl
      · rfl
  · rfl

/-- **A committed entry commutes with a lease record**: a normal entry always
(`restAfter_restGrantT`), a conf change when the record leaves its validation. -/
theorem restEntry_restGrantT [GooseExts] (c0 : w64) (m : EntryModel) (id t : w64) (r : apply.RestM)
    (hv : ∀ cc, membership.ccValidOn (apply.restGrantT id t r).bk cc =
      membership.ccValidOn r.bk cc) :
    restEntry c0 m (apply.restGrantT id t r) = apply.restGrantT id t (restEntry c0 m r) := by
  unfold restEntry
  split
  · split
    · rfl
    · split
      · exact apply.restAfter_restGrantT _ _ _ _ _
      · rfl
  · split
    · exact ccRest_restGrantT _ _ _ _ _ (hv _)
    · rfl

end EtcdGrove
end Perennial
