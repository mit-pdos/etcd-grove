/-
**The image's lease bucket** (the lease-expiry plan's S2–S4 Draft, 2026-11-05, S3;
`notes/lease-expiry-plan.md`, "S2–S4 Draft"). Lean-first (no Rocq counterpart).

A snapshot's image in a cluster that grants leases carries, in its `lease` bucket, the records of
the live leases of its committed log (the leased rest image `bkRestAtL`, `RestLeased.lean`, which
the image certificate `imageAt` already states): one record per id of the log's lease table, at
some TTL (each member's `minLeaseTTL` is its own, B1). `imageLeasesAt` is that bucket alone, at the
receiver's names: what `lessor.Recover` reads (`imageLeasesAt_recs`: the bucket's entries are
`MustUnsafeGetAllLeases`'s record encodings, `leaseRecEnc`, so no decoding law beyond that axiom's
is needed) and what the apply thread's rest buckets hold after the restore (`srvRest`'s leased arm,
`restLeasesWith` at the snapshot's table). In a log that grants nothing it is the old `hlease`
(`imageLeasesAt_nil`).

Also the two facts S2 needs of the lease table along a prefix of the committed log, one per
lessor mode: monotone, every live lease of the applied log is live at the snapshot's
(`appliedTable_mono_sub`); revocable, an id the applied log granted that the snapshot's table has
is live at the applied log (`appliedTable_granted_live`). They give `lessor.Recover`'s mode and
ever-set premises.

Not consumed yet: the Draft stopped before the statements that would use it (the notes' section,
"Stopped"). The `sorry`s below are marked `-- DRAFT S2–S4` and are temporary.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.RestLeased
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ApplyCmpArm
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.MustUnsafeGetAllLeases

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open backend

/-- **The image `D`'s lease bucket holds the records of the live leases of its committed log**
`γr.raft.pre ++ A'` (the receiver's names `γr`, tracked through the parameters `P`): one record per
id of the log's lease table (`appliedTable γr A'`, i.e. `kvLeases γr.kv (γr.raft.pre ++ A')`), each
the record `Grant` writes (`leaseEnc id t 0`), its TTL `f id` for some `f` (TTLs differ per
member: `minLeaseTTL`; at least the table's, the grant's request: the lease-expiry plan's S2–S4,
Q-S6 (A-ii)), and no other record. Stated as `restLeasesWith`'s bucket over the rest
model's (empty) one, as `bkRestAtL` and `srvRest`'s leased arm state theirs. -/
def imageLeasesAt [GooseExts] (γr : ReadNames) (P : BParams) (D : Data) (A' : List EntryModel) :
    Prop :=
  ∃ f : w64 → w64, leaseTTLsAbove (appliedTable γr A') f ∧ ((rbData P D).lookup go!"lease").getD ∅ =
    ((apply.restLeasesWith f (appliedTable γr A').ids
      (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A'))).bk.lookup go!"lease").getD ∅

/-- **The leased rest image gives the image's lease bucket** (on a real backend, which tracks
every rest bucket): `bkRestAtL` at the receiver's raft log (what `imageAt` states, with
`L = γr.raft.pre ++ A'`). -/
theorem imageLeasesAt_of_bkRestAtL [GooseExts] (d : mvcc.KBReal) {γr : ReadNames}
    {A' : List EntryModel} {D : Data}
    (h : bkRestAtL γr.kv γr.raft.raft.boot (γr.raft.pre ++ A') D) :
    imageLeasesAt γr d.P D A' := by
  obtain ⟨f, hb, hf⟩ := h
  refine ⟨f, hb, ?_⟩
  rw [rbData_real_lookup d D go!"lease" (by decide), hf go!"lease" (by decide)]
  rfl

/-- **In a log whose table is empty, the image's lease bucket is empty** (the old `hlease`). -/
theorem imageLeasesAt_nil [GooseExts] {γr : ReadNames} {P : BParams} {D : Data}
    {A' : List EntryModel} (hn : (appliedTable γr A').ids = []) (h : imageLeasesAt γr P D A') :
    ((rbData P D).lookup go!"lease").getD ∅ = ∅ := by
  obtain ⟨f, -, hf⟩ := h
  rw [hf, hn, apply.restLeasesWith_nil]
  have := restModel_lease γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A')
  exact (congrArg (fun o => Option.getD o ∅) this).trans rfl

/-- **The image's lease bucket is `Recover`'s records** (`lease.lessor.Recover.spec`'s `recs`): its
entries in key order are `leaseRecEnc` of some records whose ids are exactly the snapshot's table's
(each with remaining TTL `0`), each record's TTL at least its table entry's (the grant's request:
`Recover`'s `rq` premise, Q-S6 (A-ii)). -/
theorem imageLeasesAt_recs [GooseExts] {γr : ReadNames} {P : BParams} {D : Data}
    {A' : List EntryModel} (h : imageLeasesAt γr P D A') :
    ∃ recs : List (w64 × w64 × w64),
      bktEnts (((rbData P D).lookup go!"lease").getD ∅) = recs.map lease.leaseRecEnc ∧
      (∀ id : w64, id ∈ recs.map (·.1) ↔ id ∈ (appliedTable γr A').ids) ∧
      (∀ x ∈ recs, x.2.2 = W64 0) ∧
      ∀ x ∈ recs, ∀ p ∈ appliedTable γr A', p.1 = x.1 → sint.Z p.2 ≤ sint.Z x.2.1 := by
  sorry -- DRAFT S2–S4

/-- **S2, the monotone mode: every live lease of the applied log is live at the snapshot's**: along
a prefix of a committed log that is plain in the monotone mode (no revocation: the lease-expiry
plan's X7, a revocation exists only in the revocable mode), the lease table only grows. What
`Recover`'s monotone premise (`mono = true → ∀ id ∈ L, id ∈ recs.map (·.1)`) takes, with the
lessor's live set the applied table (`ltHalf`). -/
theorem appliedTable_mono_sub [GooseExts] (γr : ReadNames) {A A' : List EntryModel}
    (hpre : A <+: A') (hpl : plainLogM γr.kv.cmp .mono (γr.raft.pre ++ A')) :
    ∀ id ∈ (appliedTable γr A).ids, id ∈ (appliedTable γr A').ids := by
  sorry -- DRAFT S2–S4

/-- **S2, the revocable mode: an id the applied log granted that the snapshot's table has is live
at the applied log**: with the log's revocable-mode grant ids distinct (`kvGrantIds`'s fact, E3
(b)), a revoked id is never granted again, so an id of `srvGrantLog A` (the apply thread's ever-set
bound, `srvEverOk`) live at the longer log `A'` was not revoked within `A`. What `Recover`'s
ever-set premise (`∀ id ∈ recs.map (·.1), id ∈ U → id ∈ L`) takes in the revocable mode. -/
theorem appliedTable_granted_live [GooseExts] (γr : ReadNames) {A A' : List EntryModel}
    (hpre : A <+: A') (hnd : (logRevGrantIds .revocable (γr.raft.pre ++ A')).Nodup) (u : w64)
    (hu : u ∈ srvGrantLog A) (hu' : u ∈ (appliedTable γr A').ids) :
    u ∈ (appliedTable γr A).ids := by
  sorry -- DRAFT S2–S4

end EtcdGrove
end Perennial
