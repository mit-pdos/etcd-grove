/-
`(*lease.lessor).Recover(b, rd)` (`lessor.go:600`). Lean-first (no Rocq counterpart); D22
receiver epochs, S8c (2026-10-24), for `applySnapshot`; until the lease-expiry plan's S1
(2026-11-04) an axiom at the trust boundary, now translated and proved
(`Proof/.../lease/lessor__Recover.lean`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvBoot
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorBackend
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorRecover

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`le.Recover(b, rd)`** of the lessor `lp` (its configuration `lessorCfg`, its mode `mono`) on
the real backend at `oldbe` (its user's half of `le.b`, `lessorBeOn`), the owner's half of the live
set at some `L` with its item map `I` and its close rights (`leaseOwn γl L I`, `leaseRevokers γl
L`) and of the range deleter at some `rd0` (`rdOwn`), onto the real backend `d` whose lease bucket
holds the records `recs`, in key order, each what `Grant` writes (`leaseRecEnc`; absent or empty:
`recs = []`; a part of any bucket set `S` containing `lease`, `rbPart d.γB S r`; the bucket in the
table, tracked, none of its keys a hook's, `mvcc.leaseParams d.P`), every recovered id meeting the
lessor's grant guard (`leaseGranted`; the live set's leases all do, `lessorAuth`), and in the
monotone mode every live id among the records' (a monotone history keeps every lease):
the lessor on `d`, the live set the records' ids with no item (`leaseOwn γl ids ∅`,
`leaseRevokers γl ids`), the range deleter `rd` (`rdOwn γl rd`), the lease bucket of `d` present
(created if absent) and **the part idle** (`rbOwnIn d.γB S (r.insert "lease" _)`), at two
write-back tokens; and the lessor's history has at some index the recovered snapshot: one lease per
record (fresh `*Lease`s `ls`, `recMap`), no item, each record's TTL raised to the minimum `mt`
(`recTTLs`, the lease-expiry plan's R5). (E3 (c), 2026-11-05; review r1 F5) The records' ids are
added to the ids the lessor ever had (`leaseEver γl U`); one it already had must be live (`id ∈ L`);
with no record, nothing is asked of them (`⌜recs = []⌝ ∨ …`: a cluster that grants none restores a
snapshot without the ids' half).

What Go does (`lessor.go:600-609`, `initAndRecover` `:808-835`): under `le.mu`, `le.b = b`,
`le.rd = rd`, fresh `leaseMap` and `itemMap`, then `initAndRecover`
(`lessor.initAndRecover.spec`: the lease bucket created, its records read, `MustUnsafeGetAllLeases`,
one `Lease` per record into the map, the notifier and the checkpoint heap re-initialized,
`ForceCommit`). The old leases leave the lessor: their `*Lease`s keep their item sets (frozen, as
after `Revoke`) and their close rights are dropped. (2026-11-04, the lease-expiry plan's S1:
until then an axiom taking an empty bucket and a revocable lessor, and not returning `le.rd`'s
half, which the audit flagged.) (The lease-expiry plan's S2–S4, 2026-11-05: Q-S4 (A), Q-S7, Q-S8)
A record's id need not be new to `U`: one the lessor ever had must be live (`id ∈ L`, so that each
id stays live over an interval of the history); the caller names each record's request `reqOf`
(review r1 F8: until then `rq`), at most its TTL, and for an id of `U` holds its request
(`leaseReqIs`), which every recovered lease then has; and the live set is the records' ids in the
caller's order `Lr` (a permutation of them). (Review r1 F6) A scope restriction: Go recovers any
records; this spec excludes a revoked id granted again (an explicit `ID`), which the revocable
mode's generated ids (`kvGrantIds`) and the monotone mode's `histMono` rule out. -/
abbrev lease.lessor.Recover.spec : Prop :=
  ∀ (lp : Loc) (γl : GName) (oldbe : Loc) (d : mvcc.KBReal) (W Pk : IProp GF) (qo : Qp)
    (S : GoString → Prop) (r : GMap GoString backend.BktData) (rd rd0 : GoFunc) (L : List w64)
    (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) (mono : Bool)
    (recs : List (w64 × w64 × w64)) (U : List w64) (reqOf : w64 → w64) (Lr : List w64),
  S go!"lease" → mvcc.leaseParams d.P →
  backend.bktEnts ((r.lookup go!"lease").getD ∅) = recs.map lease.leaseRecEnc →
  (mono = true → ∀ id ∈ L, id ∈ recs.map (·.1)) → (∀ id ∈ recs.map (·.1), id ∈ U → id ∈ L) →
  (∀ x ∈ recs, sint.Z (reqOf x.1) ≤ sint.Z x.2.1) → Lr.Perm (recs.map (·.1)) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗
      lease.lessorInv lp γl ∗ lease.lessorCfg lp ∗ lease.lessorModeIs γl mono ∗
      (⌜recs = []⌝ ∨ lease.leaseEver γl U) ∗
      □ ([∗list] x ∈ recs, ⌜x.1 ∉ U⌝ ∨ lease.leaseReqIs γl x.1 (reqOf x.1)) ∗
      lease.lessorBeOn lp oldbe ∗ lease.leaseOwn γl L I ∗ lease.leaseRevokers γl L ∗
      lease.rdOwn γl rd0 ∗ □ ([∗list] id ∈ recs.map (·.1), lease.leaseGranted γl id) ∗
      backend.isBackend d.γB d.P W Pk d.be ∗ backend.bOpen d.γB qo ∗ ownToks d.γB.wb 2 ∗
      backend.rbPart d.γB S r }}
    (App (App (Val (lp @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.lessor.ty @!!
      go!"Recover")) (Val #(interface.mkOk
        (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #d.be)))
      (Val #rd))
  {{ RET #(); lease.lessorBeOn lp d.be ∗ lease.leaseOwn γl Lr ∅ ∗
      (⌜recs = []⌝ ∨ lease.leaseEver γl (U ++ recs.map (·.1))) ∗
      □ ([∗list] x ∈ recs, lease.leaseReqIs γl x.1 (reqOf x.1)) ∗
      lease.leaseRevokers γl Lr ∗ lease.rdOwn γl rd ∗
      backend.bOpen d.γB qo ∗
      backend.rbOwnIn d.γB S (r.insert go!"lease" ((r.lookup go!"lease").getD ∅)) ∗
      ∃ (i : Nat) (ls : List Loc) (mt : w64), ⌜ls.length = recs.length⌝ ∗
        lease.lF go!"minLeaseTTL" lp ↦□ mt ∗
        lease.lessorAt γl i (lease.recMap (recs.zip ls), ∅, lease.recTTLs mt recs) }}

end spec

end EtcdGrove
end Perennial
