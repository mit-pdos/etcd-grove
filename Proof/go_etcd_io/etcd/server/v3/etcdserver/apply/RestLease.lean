/-
**The lessor's writes to the rest buckets** (leases T3, L3c, 2026-10-27; `notes/leases-plan.md`):
the `lease` bucket's part of the rest model (`RestModel.lean`). Lean-first (no Rocq counterpart).

A grant puts the lease's record under its key (the id's 8 big-endian bytes, `leaseIDToBytes`):
`lease.leaseEnc` of the id, the TTL the lessor gives it (`lease.grantTTL` of its minimum and the
requested TTL) and a remaining TTL of 0 (`lessor.Grant`'s spec); a revoke deletes it
(`lessor.Revoke`'s). As the tracked buckets, these are `mvcc.rbSet` and `mvcc.rbDel`, the
effects the lessor's specs state (`grant_bk`, `revoke_bk`). The apply thread's model does not use
them yet: no lease request is admitted (`rqOk`) until the apply layer threads the lease table
(L3b, L3c).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.RestModel
public import Proof.go_etcd_io.etcd.server.v3.lease.LeaseRecord
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apply

/-- **A lease's key in the `lease` bucket**: its id as 8 big-endian bytes. -/
def leaseKey (id : w64) : GoString := (u64Le id).reverse

/-- **`Grant(id, ttl)`'s write** by a lessor whose minimum TTL is `mt`: the record put. -/
def restGrant (mt id ttl : w64) (r : RestM) : RestM :=
  r.putIn mvcc.leaseName (leaseKey id) (lease.leaseEnc id (lease.grantTTL mt ttl) (W64 0))

/-- **`Revoke(id)`'s write**: the record deleted. -/
def restRevoke (id : w64) (r : RestM) : RestM :=
  r.delIn mvcc.leaseName (leaseKey id)

/-- A put into the rest model's buckets is the tracked buckets' `rbSet`. -/
theorem bkPut_rbSet (bk : GMap GoString backend.BktData) (n k v : GoString) :
    bkPut bk n k v = mvcc.rbSet bk n k v := rfl

/-- A delete is `rbDel`. -/
theorem bkDel_rbDel (bk : GMap GoString backend.BktData) (n k : GoString) :
    bkDel bk n k = mvcc.rbDel bk n k := rfl

/-- The grant's buckets are those `lessor.Grant` puts its record into. -/
theorem grant_bk (mt id ttl : w64) (r : RestM) :
    (restGrant mt id ttl r).bk =
      mvcc.rbSet r.bk mvcc.leaseName (u64Le id).reverse
        (lease.leaseEnc id (lease.grantTTL mt ttl) (W64 0)) := rfl

/-- The revoke's buckets are those `lessor.Revoke` deletes its record from. -/
theorem revoke_bk (id : w64) (r : RestM) :
    (restRevoke id r).bk = mvcc.rbDel r.bk mvcc.leaseName (u64Le id).reverse := rfl

/-- Neither changes the members. -/
theorem restGrant_mem (mt id ttl : w64) (r : RestM) : (restGrant mt id ttl r).mem = r.mem := rfl

theorem restRevoke_mem (id : w64) (r : RestM) : (restRevoke id r).mem = r.mem := rfl

/-! ## A grant's record (the lease-grant stage, 2.0; from `GrantRest.lean`) -/

/-- **A lease's record put at the granted TTL `t`** (the record `lessor.Grant` writes, with its
TTL already the lessor's `grantTTL`). -/
def restGrantT (id t : w64) (r : RestM) : RestM :=
  r.putIn mvcc.leaseName (leaseKey id) (lease.leaseEnc id t (W64 0))

theorem restGrant_eq (mt id ttl : w64) (r : RestM) :
    restGrant mt id ttl r = restGrantT id (lease.grantTTL mt ttl) r := rfl

theorem restGrantT_mem (id t : w64) (r : RestM) : (restGrantT id t r).mem = r.mem := rfl

/-- **`lessor.Grant`'s success condition** at the live set `L`: the id not `NoLease`, the TTL at
most `MaxLeaseTTL`, the id not live. -/
def grantIdsOk (L : List w64) (id ttl : w64) : Prop :=
  id ≠ W64 0 ∧ sint.Z ttl ≤ 9000000000 ∧ id ∉ L

instance (L : List w64) (id ttl : w64) : Decidable (grantIdsOk L id ttl) := by
  unfold grantIdsOk; infer_instance

/-! ## The leased rest image -/

/-- **The records of the live ids `ids` put in order**, the TTL of each `f id` (the leased rest
image: `srvRest`'s leased arm, `bkRestAtL`; the TTLs under an existential, B1). -/
def restLeasesWith (f : w64 → w64) (ids : List w64) (r : RestM) : RestM :=
  ids.foldl (fun r id => restGrantT id (f id) r) r

theorem restLeasesWith_nil (f : w64 → w64) (r : RestM) : restLeasesWith f [] r = r := rfl

/-- The records leave the members (`srvRestOwn`'s `%Hmi`). -/
theorem restLeasesWith_mem (f : w64 → w64) (ids : List w64) (r : RestM) :
    (restLeasesWith f ids r).mem = r.mem := by
  unfold restLeasesWith
  induction ids generalizing r with
  | nil => rfl
  | cons id ids ih => rw [List.foldl_cons, ih]; rfl

/-- Two TTL functions that agree on `ids` put the same records. -/
theorem restLeasesWith_congr (f f' : w64 → w64) (ids : List w64) (r : RestM)
    (h : ∀ id ∈ ids, f id = f' id) : restLeasesWith f ids r = restLeasesWith f' ids r := by
  unfold restLeasesWith
  induction ids generalizing r with
  | nil => rfl
  | cons id ids ih =>
    rw [List.foldl_cons, List.foldl_cons, h id List.mem_cons_self]
    exact ih _ (fun id' hm => h id' (List.mem_cons_of_mem _ hm))

/-- `f` updated at `id` to `t` (`Function.update`, which this repository's dependencies lack). -/
def updFn (f : w64 → w64) (id t : w64) : w64 → w64 := fun x => if x = id then t else f x

/-- **One more record** (`srvRest_applyG`): a grant of `id ∉ ids` at the TTL `t` is the leased
image of `ids ++ [id]` at `f` updated at `id`. -/
theorem restLeasesWith_snoc (f : w64 → w64) (ids : List w64) (id t : w64) (r : RestM)
    (hn : id ∉ ids) :
    restGrantT id t (restLeasesWith f ids r) =
      restLeasesWith (updFn f id t) (ids ++ [id]) r := by
  have hc := restLeasesWith_congr f (updFn f id t) ids r (fun id' hm => by
    simp [updFn, show id' ≠ id from fun h => hn (h ▸ hm)])
  unfold restLeasesWith at hc ⊢
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ← hc]
  simp [updFn]

/-- **A writer that commutes with each record commutes with all of them** (the other writers'
laws below, `restEntry_restGrantT`). -/
theorem restLeasesWith_comm (g : RestM → RestM)
    (hg : ∀ id t r, g (restGrantT id t r) = restGrantT id t (g r)) (f : w64 → w64) (ids : List w64)
    (r : RestM) : g (restLeasesWith f ids r) = restLeasesWith f ids (g r) := by
  unfold restLeasesWith
  induction ids generalizing r with
  | nil => rfl
  | cons id ids ih => rw [List.foldl_cons, List.foldl_cons, ih, hg]

/-! ## Commuting with the other writers -/

/-- A put of a record into another bucket commutes with the lease record's put. -/
theorem restGrantT_putIn (id t : w64) (r : RestM) (n k v : GoString) (hn : n ≠ mvcc.leaseName) :
    restGrantT id t (r.putIn n k v) = (restGrantT id t r).putIn n k v := by
  unfold restGrantT RestM.putIn
  simp only [RestM.mk.injEq, and_true]
  rw [GMap.lookup_insert_ne _ _ hn, GMap.lookup_insert_ne _ _ (Ne.symm hn),
    GMap.insert_commute _ _ _ (Ne.symm hn)]

/-- A delete from another bucket commutes with the lease record's put. -/
theorem restGrantT_delIn (id t : w64) (r : RestM) (n k : GoString) (hn : n ≠ mvcc.leaseName) :
    restGrantT id t (r.delIn n k) = (restGrantT id t r).delIn n k := by
  unfold restGrantT RestM.putIn RestM.delIn
  simp only [RestM.mk.injEq, and_true]
  rw [GMap.lookup_insert_ne _ _ hn, GMap.lookup_insert_ne _ _ (Ne.symm hn),
    GMap.insert_commute _ _ _ (Ne.symm hn)]

/-- The members' updates commute with the lease record's put. -/
theorem restGrantT_withMem (id t : w64) (r : RestM) (mem : GMap w64 MemberM) :
    restGrantT id t { r with mem := mem } = { restGrantT id t r with mem := mem } := rfl

/-- **`restAfter` commutes with a lease record** (the cluster version's and the member
attributes' writes are to other buckets; the attributes read only the members). -/
theorem restAfter_restGrantT [GooseExts] (rq : IRRModel) (v3 : Bool) (id t : w64) (r : RestM) :
    restAfter rq v3 (restGrantT id t r) = restGrantT id t (restAfter rq v3 r) := by
  have hc : go!"cluster" ≠ mvcc.leaseName := by decide
  have hm : go!"members" ≠ mvcc.leaseName := by decide
  unfold restAfter
  split
  · unfold restSetVersion; split
    · exact (restGrantT_putIn _ _ _ _ _ _ hc).symm
    · rfl
  · split
    · unfold restUpdateAttrs
      rw [restGrantT_mem]
      split
      · rfl
      · split
        · simp only [restGrantT, RestM.putIn, RestM.mk.injEq, and_true]
          rw [GMap.lookup_insert_ne _ _ hm, GMap.lookup_insert_ne _ _ (Ne.symm hm),
            GMap.insert_commute _ _ _ (Ne.symm hm)]
        · rfl
    · rfl

end apply
end EtcdGrove
end Perennial
