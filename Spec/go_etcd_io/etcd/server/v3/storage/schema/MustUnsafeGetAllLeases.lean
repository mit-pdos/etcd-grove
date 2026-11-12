/-
`schema.MustUnsafeGetAllLeases(tx)` (`server/storage/schema/lease.go`, translated names-only).
The trust boundary (the lease-expiry plan's step 3, 2026-11-04, the user's decision (a): a contract
over the locked batch transaction's state, as `batchTxBuffered.UnsafeRange.spec` and
`MustReadMembersFromBackend` are). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.LeaseRecord
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBackend

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

/-- **A lease's entry in the `Lease` bucket** (the record `Grant` puts, `schema.MustUnsafePutLease`):
the key the id's 8 big-endian bytes, the value `leaseEnc` of the id, the TTL and the remaining
TTL. -/
def lease.leaseRecEnc (x : w64 × w64 × w64) : backend.Ent :=
  ((u64Le x.1).reverse, lease.leaseEnc x.1 x.2.1 x.2.2)

/-- The ids of a bucket whose entries are `recs`' records are distinct (the bucket's keys are, and a
key is its id's bytes). -/
theorem lease.leaseRecs_nodup (m : backend.BktData) (recs : List (w64 × w64 × w64))
    (h : backend.bktEnts m = recs.map lease.leaseRecEnc) : (recs.map (·.1)).Nodup := by
  have hk : ((backend.bktEnts m).map Prod.fst).Nodup := by
    unfold backend.bktEnts
    exact ((List.mergeSort_perm _ _).map Prod.fst).nodup_iff.mpr (GMap.toList_keys_nodup m)
  rw [h, List.map_map] at hk
  unfold List.Nodup at hk ⊢
  refine List.pairwise_map.2 ((List.pairwise_map.1 hk).imp fun hne e => hne ?_)
  simp only [Function.comp_apply, lease.leaseRecEnc, e]

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage backend

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [backend_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-- **`MustUnsafeGetAllLeases(tx)`** on the real backend's batch transaction `t` (of the backend
`b`), under its lock at the state `st`, whose `Lease` bucket (the bucket `bi` the variable
`schema.Lease` holds, `bk`) holds exactly the records `Grant` writes (`leaseRecEnc` of each of `recs`,
in key order: `bktEnts`): the lock's state unchanged, and a fresh slice of fresh `*leasepb.Lease`,
one per record, in key order, with the record's id, TTL and remaining TTL.

What it trusts (`schema/lease.go:31-46` at the etcd pin): `tx.UnsafeForEach(Lease, f)` on the
batch transaction is `batchTx.UnsafeForEach` (`batch_tx.go:250-262`), which iterates bbolt's
writer transaction `t.tx` (the session's writes included: the writer's contents `st.S`) over the
bucket in key order and calls `f` on each entry, changing nothing; `f` decodes the value
(`proto.Unmarshal` of `leaseEnc id ttl rem`, `proto.Marshal`'s encoding of a `leasepb.Lease` with
those three `int64` fields, gives them back: `leaseEnc` is the encoding, so injective) into a fresh
message and appends its pointer to `ls` (a fresh slice). Go panics when a value does not decode
(`err != nil`, `lease.go:42-44`), which the premise excludes: every value is an encoding. The
backend's lock is not taken or released (`Unsafe`: the caller holds it); bbolt's cursor allocates
no Go memory the caller sees. -/
abbrev schema.MustUnsafeGetAllLeases.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (W Pk : IProp GF) (b t : Loc) (st : BSess) (bk : GoInterface)
    (bi : BucketInfo) (recs : List (w64 × w64 × w64)),
  bktEnts (bktOf st.S bi.name) = recs.map lease.leaseRecEnc →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isBackend γ P W Pk b ∗ bF go!"batchTx" b ↦□ t ∗ batchLocked γ P b st ∗
      globalAddr go_etcd_io.etcd.server.v3.storage.schema.Lease ↦□ bk ∗ isBucket bk bi }}
    (App (Val (@! schema.MustUnsafeGetAllLeases))
      (Val #(interface.mkOk (go.GoType.PointerType batchTxBuffered.ty) #t)))
  {{ (s : GoSlice), RET #s; batchLocked γ P b st ∗
      ∃ ps : List Loc, s ↦* ps ∗ ⌜ps.length = recs.length⌝ ∗
        [∗list] p; x ∈ ps; recs,
          ∃ v : go_etcd_io.etcd.server.v3.lease.leasepb.Lease, p ↦ v ∗
            ⌜v.ID' = x.1 ∧ v.TTL' = x.2.1 ∧ v.RemainingTTL' = x.2.2⌝ }}

end spec

end EtcdGrove
end Perennial
