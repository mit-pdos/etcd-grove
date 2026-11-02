/-
**A grant's effect on the rest buckets and the live set** (the lease-grant stage, 2026-11-02;
`notes/lease-grant-plan.md`, "Design of the server chain", 2.0): the pure vocabulary of the grant
triple (2.11) and of the apply thread's leased rest image (2.9). Lean-first (no Rocq counterpart).

- `restGrantT id t r`: the `lease` bucket's record of `id` put at the granted TTL `t` (`restGrant mt
  id ttl` is `restGrantT id (grantTTL mt ttl)`, `restGrant_eq`);
- `grantIdsOk L id ttl`: `lessor.Grant`'s success condition at the live set `L`;
- `grantGoes c`: the chain has no capped or corrupt layer (each rejects a grant);
- `grantIds rq o L`, `grantRest t rq o r`: the live set and the rest buckets after the outcome `o`
  (`.applied` a grant's success: its id appended, its record put); the identity otherwise. Over an
  `ApplyOut` (`apply.Apply`'s outcome), `grantIdsA`/`grantRestA`;
- `restLeasesWith f ids r`: the records of `ids` put in order, the TTL of each `f id`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.InvUber
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.RestLease

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apply

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

/-- **The chain lets a grant through to the backend**: no capped and no corrupt layer (each
rejects a grant: `cappedRejects`, `corruptRejects`). -/
def grantGoes : Chain → IRRModel → Bool
  | .backend, _ => true
  | .auth _ c, rq => grantGoes c rq
  | .quota c, rq => grantGoes c rq
  | .capped _, _ => false
  | .corrupt _, _ => false

/-- **The live set after the outcome `o`** of `rq`: a grant applied appends its id. -/
def grantIds (rq : IRRModel) (o : Outcome) (L : List w64) : List w64 :=
  match o, rq.leaseGrant with
  | .applied .., some g => L ++ [g.id]
  | _, _ => L

/-- **The rest buckets after the outcome `o`** of `rq`, the record at the TTL `t`. -/
def grantRest (t : w64) (rq : IRRModel) (o : Outcome) (r : RestM) : RestM :=
  match o, rq.leaseGrant with
  | .applied .., some g => restGrantT g.id t r
  | _, _ => r

/-- `grantIds` over `apply.Apply`'s outcome: a dispatched request's. -/
def grantIdsA (rq : IRRModel) (out : ApplyOut) (L : List w64) : List w64 :=
  match out with
  | .dispatched o _ => grantIds rq o L
  | _ => L

/-- `grantRest` over `apply.Apply`'s outcome: a dispatched request's. -/
def grantRestA (t : w64) (rq : IRRModel) (out : ApplyOut) (r : RestM) : RestM :=
  match out with
  | .dispatched o _ => grantRest t rq o r
  | _ => r

theorem grantIds_rejected (rq : IRRModel) (e : RejectKind) (L : List w64) :
    grantIds rq (.rejected e) L = L := rfl

theorem grantRest_rejected (t : w64) (rq : IRRModel) (e : RejectKind) (r : RestM) :
    grantRest t rq (.rejected e) r = r := rfl

/-- No grant field: the identity. -/
theorem grantIds_none (rq : IRRModel) (o : Outcome) (L : List w64) (h : rq.leaseGrant = none) :
    grantIds rq o L = L := by
  unfold grantIds; cases o <;> simp [h]

theorem grantRest_none (t : w64) (rq : IRRModel) (o : Outcome) (r : RestM)
    (h : rq.leaseGrant = none) : grantRest t rq o r = r := by
  unfold grantRest; cases o <;> simp [h]

/-- An outcome that is not `.applied`: the identity. -/
theorem grantIds_not_applied (rq : IRRModel) (o : Outcome) (L : List w64)
    (h : ∀ log' ns, o ≠ .applied log' ns) : grantIds rq o L = L := by
  cases o with
  | rejected => rfl
  | applied log' ns => exact absurd rfl (h log' ns)

theorem grantRest_not_applied (t : w64) (rq : IRRModel) (o : Outcome) (r : RestM)
    (h : ∀ log' ns, o ≠ .applied log' ns) : grantRest t rq o r = r := by
  cases o with
  | rejected => rfl
  | applied log' ns => exact absurd rfl (h log' ns)

theorem grantIds_applied (rq : IRRModel) (g : LeaseGrantModel) (log' : mvcc.Log) (ns : Bool)
    (L : List w64) (h : rq.leaseGrant = some g) :
    grantIds rq (.applied log' ns) L = L ++ [g.id] := by
  unfold grantIds; rw [h]

theorem grantRest_applied (t : w64) (rq : IRRModel) (g : LeaseGrantModel) (log' : mvcc.Log)
    (ns : Bool) (r : RestM) (h : rq.leaseGrant = some g) :
    grantRest t rq (.applied log' ns) r = restGrantT g.id t r := by
  unfold grantRest; rw [h]

theorem grantRest_mem (t : w64) (rq : IRRModel) (o : Outcome) (r : RestM) :
    (grantRest t rq o r).mem = r.mem := by
  unfold grantRest; split <;> rfl

theorem grantIdsA_not_dispatched (rq : IRRModel) (out : ApplyOut) (L : List w64)
    (h : ∀ o sk, out ≠ .dispatched o sk) : grantIdsA rq out L = L := by
  cases out with
  | dispatched o sk => exact absurd rfl (h o sk)
  | _ => rfl

theorem grantRestA_not_dispatched (t : w64) (rq : IRRModel) (out : ApplyOut) (r : RestM)
    (h : ∀ o sk, out ≠ .dispatched o sk) : grantRestA t rq out r = r := by
  cases out with
  | dispatched o sk => exact absurd rfl (h o sk)
  | _ => rfl

theorem grantIdsA_none (rq : IRRModel) (out : ApplyOut) (L : List w64)
    (h : rq.leaseGrant = none) : grantIdsA rq out L = L := by
  unfold grantIdsA; split
  · exact grantIds_none _ _ _ h
  · rfl

theorem grantRestA_none (t : w64) (rq : IRRModel) (out : ApplyOut) (r : RestM)
    (h : rq.leaseGrant = none) : grantRestA t rq out r = r := by
  unfold grantRestA; split
  · exact grantRest_none _ _ _ _ h
  · rfl

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
