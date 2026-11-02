/-
**etcd's specs of `LeaseGrant` and `LeaseLeases` at the lessor's history** (the lease-grant plan's
D5, 2026-11-02, `notes/lease-grant-plan.md`). Lean-first (no Rocq counterpart).

The contracts of the two methods (the user's decision on the review's S6, 2026-11-02: replace, and
derive the old): stronger than the ones before (now `etcdLeaseGrantSpecAny`, `etcdLeaseLeasesSpecAny`,
`InvLease.lean`/`InvLeaseRead.lean`), which follow (`isGrpcRpc_leaseGrant_any`,
`isGrpcRpc_leaseLeases_any`: a registration at these is one at those), so their callers keep
them. For a server whose lessor `γl` is monotone (it grants leases and revokes none,
`lease.lessorModeIs γl true`, under the deployment premise `lease.leasesNoExpiry`):

* `LeaseGrant`'s reply carries the persistent fact that its lease was granted at some index of the
  lessor's history (`lease.leaseGrantedAt γl i id`): the apply thread's `Grant` appended the
  snapshot with it (`lessor.Grant.spec`'s `leaseLiveFrom`), and the reply is sent after the apply.
* `LeaseLeases`'s caller hands in the grants it knows of (a list `G`, each with its fact); the reply
  lists each of them (and no lease twice): `EtcdServer.LeaseLeases` reads the lessor's map at an index
  no older than the bound the grants give (`lessorLb`, `leaseGrantedAt_lb`), and a monotone lessor's
  later maps keep every lease granted (`leaseGrantedAt_listed`).

Why the lessor `γl` of one member, not a cluster-level certificate (review S5): Go's `LeaseLeases`
is a member-local read (`EtcdServer.LeaseLeases`, `v3_server.go:737-749`: the member's own lessor,
no read index), so a lagging member need not list a lease the cluster granted; the contracts are
registered at one member's address with its lessor. A client with several endpoints would need them
at every member, which no granting cluster gives.

What `Main` of `examples/leasegrant` checks: the lease `Grant` returns is in the `Leases` reply.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvLeaseRead
public import Proof.go_etcd_io.etcd.server.v3.lease.InvLessor

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [EM : EtcdModel GF]

/-- **etcd's spec of `LeaseGrant` at the lessor `γl`** (see the file header): any request gets a
reply whose lease ID is not `NoLease`, whose header revision etcd has reached, and whose lease was
granted at some index of the lessor's history (one member's: see the file header). -/
def etcdLeaseGrantSpec (γl : GName) :
    GrpcSpec (GF := GF) pbLeaseGrantRequest pbLeaseGrantResponse :=
  fun (_ : w64 × w64) (Φ : LeaseGrantRespM → IProp GF) =>
    iprop(∀ m : LeaseGrantRespM, ⌜m.id ≠ W64 0⌝ -∗ etcdReached m.hdr.revision -∗
      (∃ i : Nat, lease.leaseGrantedAt γl i m.id) -∗ Φ m)

end specs

section specsL
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **etcd's spec of `LeaseLeases` at the lessor `γl`** (see the file header): the caller's grants
`G` (each granted at some index of this member's lessor: the listing is member-local, see the file
header) are all listed, and no lease twice. -/
def etcdLeaseLeasesSpec (γl : GName) :
    GrpcSpec (GF := GF) pbLeaseLeasesRequest pbLeaseLeasesResponse :=
  fun (_ : Unit) (Φ : LeaseLeasesRespM → IProp GF) =>
    iprop(∃ G : List w64, ([∗list] id ∈ G, ∃ i : Nat, lease.leaseGrantedAt γl i id) ∗
      ∀ m : LeaseLeasesRespM, ⌜m.ids.Nodup ∧ ∀ id ∈ G, id ∈ m.ids⌝ -∗ Φ m)

/-- (S6) The old `LeaseGrant` contract is weaker. -/
theorem etcdLeaseGrantSpec_any [EM : EtcdModel GF] (γl : GName) (m : w64 × w64)
    (Φ : LeaseGrantRespM → IProp GF) :
    etcdLeaseGrantSpecAny (GF := GF) m Φ ⊢ etcdLeaseGrantSpec γl m Φ := by
  unfold etcdLeaseGrantSpecAny etcdLeaseGrantSpec
  iintro H %r Hid Hr -
  iapply H $$ Hid Hr

/-- (S6) The old `LeaseLeases` contract is weaker (the caller hands in no grant). -/
theorem etcdLeaseLeasesSpec_any (γl : GName) (m : Unit) (Φ : LeaseLeasesRespM → IProp GF) :
    etcdLeaseLeasesSpecAny (GF := GF) m Φ ⊢ etcdLeaseLeasesSpec γl m Φ := by
  unfold etcdLeaseLeasesSpecAny etcdLeaseLeasesSpec
  iintro H
  iexists ([] : List w64)
  isplitr
  · iapply BigSepL.bigSepL_nil.2; iempintro
  iintro %r %h
  iapply H; ipureintro; exact h.1

/-- (S6) **A registration of `LeaseGrant` at the contract is one at the old contract.** -/
theorem isGrpcRpc_leaseGrant_any [EM : EtcdModel GF] (addr : GoString) (γl : GName) :
    isGrpcRpc addr go!"/etcdserverpb.Lease/LeaseGrant" (etcdLeaseGrantSpec (GF := GF) γl) ⊢
      isGrpcRpc addr go!"/etcdserverpb.Lease/LeaseGrant" etcdLeaseGrantSpecAny :=
  isGrpcRpc_mono _ _ _ _ (etcdLeaseGrantSpec_any γl)

/-- (S6) **A registration of `LeaseLeases` at the contract is one at the old contract.** -/
theorem isGrpcRpc_leaseLeases_any (addr : GoString) (γl : GName) :
    isGrpcRpc addr go!"/etcdserverpb.Lease/LeaseLeases" (etcdLeaseLeasesSpec (GF := GF) γl) ⊢
      isGrpcRpc addr go!"/etcdserverpb.Lease/LeaseLeases" etcdLeaseLeasesSpecAny :=
  isGrpcRpc_mono _ _ _ _ (etcdLeaseLeasesSpec_any γl)

end specsL

end EtcdGrove
end Perennial
