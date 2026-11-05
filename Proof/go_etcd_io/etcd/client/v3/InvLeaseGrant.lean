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

What `Main` of `examples/etcd/leasegrant` checks: the lease `Grant` returns is in the `Leases` reply.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvLeaseRead
public import Proof.go_etcd_io.etcd.server.v3.lease.InvLessor
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LeaseRead

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

/-- **etcd's spec of `LeaseGrant` at a success fact `G`** (the lease-expiry plan's X2, 2026-11-04):
`etcdLeaseGrantSpec` with the fact the reply carries of its lease a parameter
(`etcdLeaseGrantSpec_eq`: the grant at the history; `etcdLeaseGrantSpecLive`: the lease live in it). -/
def etcdLeaseGrantSpecG (G : w64 → IProp GF) :
    GrpcSpec (GF := GF) pbLeaseGrantRequest pbLeaseGrantResponse :=
  fun (_ : w64 × w64) (Φ : LeaseGrantRespM → IProp GF) =>
    iprop(∀ m : LeaseGrantRespM, ⌜m.id ≠ W64 0⌝ -∗ etcdReached m.hdr.revision -∗ G m.id -∗ Φ m)

/-- `etcdLeaseGrantSpec` is `etcdLeaseGrantSpecG` at the grant at the history. -/
theorem etcdLeaseGrantSpec_eq (γl : GName) :
    etcdLeaseGrantSpec (GF := GF) γl =
      etcdLeaseGrantSpecG (fun id => iprop(∃ i : Nat, lease.leaseGrantedAt γl i id)) := rfl

/-- **etcd's spec of `LeaseGrant` at a success fact `G`, for the requests of a filter `R`** (the
lease-expiry plan's E3, 2026-11-04): `etcdLeaseGrantSpecG`, the caller also showing that its request
(`(TTL, ID)`) is one `R` covers. -/
def etcdLeaseGrantSpecGR (G : w64 → IProp GF) (R : w64 × w64 → Prop) :
    GrpcSpec (GF := GF) pbLeaseGrantRequest pbLeaseGrantResponse :=
  fun (m : w64 × w64) (Φ : LeaseGrantRespM → IProp GF) =>
    iprop(⌜R m⌝ ∗ etcdLeaseGrantSpecG G m Φ)

/-- **etcd's spec of `LeaseGrant` at the lessor `γl`, in any lease mode** (the lease-expiry plan's
X2, 2026-11-04): a request with `ID = 0` (E3, 2026-11-04, the user's: generated ids only, as
clientv3's `Grant` sends; in the revocable mode `EtcdServer.LeaseGrant` takes no other) gets a reply
whose lease ID is not `NoLease`, whose header revision etcd has reached, and whose lease is live in
the lessor's history from some index (`leaseLiveFrom`: a revocable lessor may revoke it later, so no
listing need list it). Until E3 it covered any request, and the old contract followed from it
(`isGrpcRpc_leaseGrantLive_any`, unused, removed). -/
def etcdLeaseGrantSpecLive (γl : GName) :
    GrpcSpec (GF := GF) pbLeaseGrantRequest pbLeaseGrantResponse :=
  etcdLeaseGrantSpecGR (fun id => iprop(∃ (i : Nat) (l : Loc), lease.leaseLiveFrom γl i id l))
    (fun m => m.2 = W64 0)

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

section specsLive
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

open Iris.ProofMode

/-- **etcd's spec of `LeaseTimeToLive` at the lessor `γl` and the server `s`, in the revocable lease
mode** (the lease-expiry plan's E3, 2026-11-05): the caller hands in a lower bound `m` of the
lessor's history (`lessorLb`), and the reply, about the asked lease, carries, under the lease-TTL row
(`leaseTTLRow s γl`: `s` its cluster's only member, in its first start), that its `GrantedTTL` is the
lease's TTL at an index `≥ m`, or that the lease is absent from `m` on (the server's
`EtcdServer.leaseTimeToLive.spec`'s answer through `LeaseServer.LeaseTimeToLive`, whose TTL `-1`
reply is the not-found arm). -/
def etcdLeaseTTLSpecLive (γl : GName) (s : Loc) :
    GrpcSpec (GF := GF) pbLeaseTimeToLiveRequest pbLeaseTimeToLiveResponse :=
  fun (req : w64 × Bool) (Φ : LeaseTTLRespM → IProp GF) =>
    iprop(∃ m : Nat, lease.lessorLb γl m ∗
      ∀ resp : LeaseTTLRespM, ⌜resp.id = req.1⌝ -∗
        □ (leaseTTLRow s γl -∗
            (∃ i : Nat, ⌜m ≤ i⌝ ∗ lease.leaseTTLAt γl i resp.id resp.grantedTtl) ∨
            lease.leaseAbsentFrom γl m resp.id) -∗
        Φ resp)

/-- **etcd's spec of `LeaseLeases` at the lessor `γl`, in the revocable lease mode** (the
lease-expiry plan's E3, 2026-11-05): the caller hands in a lower bound `m` of the lessor's history,
and the reply lists the lease ids of a snapshot of the history at an index `≥ m` (`leaseIdsAt`: the
ids of its lease map, no id twice). -/
def etcdLeaseLeasesSpecLive (γl : GName) :
    GrpcSpec (GF := GF) pbLeaseLeasesRequest pbLeaseLeasesResponse :=
  fun (_ : Unit) (Φ : LeaseLeasesRespM → IProp GF) =>
    iprop(∃ m : Nat, lease.lessorLb γl m ∗
      ∀ resp : LeaseLeasesRespM, (∃ j : Nat, ⌜m ≤ j⌝ ∗ lease.leaseIdsAt γl j resp.ids) -∗ Φ resp)

/-- A registration with `Spec` is one with `Spec'` if `Spec'` gives `Spec` with the persistent `P`
(`isGrpcRpc_mono` with a context). -/
theorem isGrpcRpc_mono_with {Req Rep : ProtoMsg GF} (addr name : GoString) (P : IProp GF)
    [Persistent P] (Spec Spec' : GrpcSpec Req Rep) (h : ∀ m Φ, P ∗ Spec' m Φ ⊢ Spec m Φ) :
    P ∗ isGrpcRpc addr name Spec ⊢ isGrpcRpc addr name Spec' := by
  iintro ⟨#HP, #H⟩
  iunfold isGrpcRpc at H
  icases H with ⟨%mh, %srv, %ics, %S, #Hs, #Hm⟩
  unfold isGrpcRpc
  iexists mh, srv, ics, S
  iframe Hs
  unfold grpcMethodOk
  iintro %m %Φ %ci %cd %dec %ui !> %Ψ ⟨HS, Hctx, Hrc, Hd, Hch, HSpec⟩ HΨ
  iapply Hm $$ %m %Φ %ci %cd %dec %ui [HS Hctx Hrc Hd Hch HSpec] HΨ
  iframe
  iapply (h m Φ)
  isplitl []
  · iexact HP
  iexact HSpec

/-- **A registration of `LeaseTimeToLive` at the revocable mode's spec is one at the old spec**,
with a lower bound of the lessor's history to hand in. -/
theorem isGrpcRpc_leaseTTL_live_any (addr : GoString) (γl : GName) (s : Loc) (m : Nat) :
    lease.lessorLb (GF := GF) γl m ∗
      isGrpcRpc addr go!"/etcdserverpb.Lease/LeaseTimeToLive" (etcdLeaseTTLSpecLive γl s) ⊢
      isGrpcRpc addr go!"/etcdserverpb.Lease/LeaseTimeToLive" etcdLeaseTTLSpec := by
  apply isGrpcRpc_mono_with
  intro r Φ
  unfold etcdLeaseTTLSpec etcdLeaseTTLSpecLive
  iintro ⟨#Hm, H⟩
  iexists m
  iframe Hm
  iintro %resp %Hid -
  iapply H $$ %resp %Hid

/-- **A registration of `LeaseLeases` at the revocable mode's spec is one at the old spec**, with a
lower bound of the lessor's history to hand in. -/
theorem isGrpcRpc_leaseLeases_live_any (addr : GoString) (γl : GName) (m : Nat) :
    lease.lessorLb (GF := GF) γl m ∗
      isGrpcRpc addr go!"/etcdserverpb.Lease/LeaseLeases" (etcdLeaseLeasesSpecLive γl) ⊢
      isGrpcRpc addr go!"/etcdserverpb.Lease/LeaseLeases" etcdLeaseLeasesSpecAny := by
  apply isGrpcRpc_mono_with
  intro r Φ
  unfold etcdLeaseLeasesSpecAny etcdLeaseLeasesSpecLive
  iintro ⟨#Hm, H⟩
  iexists m
  iframe Hm
  iintro %resp ⟨%j, -, #Hids⟩
  ihave %Hnd := lease.leaseIdsAt_nodup γl j resp.ids $$ Hids
  iapply H $$ %resp %Hnd

end specsLive

end EtcdGrove
end Perennial
