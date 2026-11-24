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

end specs

section specsHF
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF] [GoLocalContext]
variable [sem : go.Semantics]
variable [EM : EtcdModel GF]
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **etcd's spec of `LeaseGrant` at the lessor `γl`** (see the file header): any request gets a
reply whose lease ID is not `NoLease`, whose header revision etcd has reached, and whose lease was
granted at some index of the lessor's history (one member's: see the file header). -/
def etcdLeaseGrantSpecW (γl : GName) : w64 × w64 → (LeaseGrantRespM → IProp GF) → IProp GF :=
  fun (_ : w64 × w64) (Φ : LeaseGrantRespM → IProp GF) =>
    iprop(∀ m : LeaseGrantRespM, ⌜m.id ≠ W64 0⌝ -∗ etcdReached m.hdr.revision -∗
      (∃ i : Nat, lease.leaseGrantedAt γl i m.id) -∗ Φ m)

end specsHF

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [EM : EtcdModel GF]


/-- **`etcdLeaseGrantSpecW` at the messages' models** (S2, heap-free vocabulary, 2026-11-23: the
spec is `etcdLeaseGrantSpecW`, over the models alone, what a service table holds; this is its form
at the message types). -/
def etcdLeaseGrantSpec (γl : GName) :
    GrpcSpec (GF := GF) pbLeaseGrantRequest pbLeaseGrantResponse :=
  etcdLeaseGrantSpecW γl

end specs

section specsHF
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF] [GoLocalContext]
variable [sem : go.Semantics]
variable [EM : EtcdModel GF]
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **etcd's spec of `LeaseGrant` at a success fact `G`** (the lease-expiry plan's X2, 2026-11-04):
`etcdLeaseGrantSpec` with the fact the reply carries of its lease a parameter
(`etcdLeaseGrantSpec_eq`: the grant at the history; `etcdLeaseGrantSpecLive`: the lease live in it).
(2026-11-05, the lease-expiry plan's E3/R5: the granted TTL) `G` takes the request (`(TTL, ID)`)
before the lease id, so that the fact can bound the lease's TTL by the requested one. -/
def etcdLeaseGrantSpecGW (G : w64 × w64 → w64 → IProp GF) :
    w64 × w64 → (LeaseGrantRespM → IProp GF) → IProp GF :=
  fun (req : w64 × w64) (Φ : LeaseGrantRespM → IProp GF) =>
    iprop(∀ m : LeaseGrantRespM, ⌜m.id ≠ W64 0⌝ -∗ etcdReached m.hdr.revision -∗ G req m.id -∗
      Φ m)

end specsHF

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [EM : EtcdModel GF]


/-- **`etcdLeaseGrantSpecGW` at the messages' models** (S2, heap-free vocabulary, 2026-11-23: the
spec is `etcdLeaseGrantSpecGW`, over the models alone, what a service table holds; this is its form
at the message types). -/
def etcdLeaseGrantSpecG (G : w64 × w64 → w64 → IProp GF) :
    GrpcSpec (GF := GF) pbLeaseGrantRequest pbLeaseGrantResponse :=
  etcdLeaseGrantSpecGW G

/-- `etcdLeaseGrantSpec` is `etcdLeaseGrantSpecG` at the grant at the history. -/
theorem etcdLeaseGrantSpec_eq (γl : GName) :
    etcdLeaseGrantSpec (GF := GF) γl =
      etcdLeaseGrantSpecG (fun _ id => iprop(∃ i : Nat, lease.leaseGrantedAt γl i id)) := rfl

end specs

section specsHF
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF] [GoLocalContext]
variable [sem : go.Semantics]
variable [EM : EtcdModel GF]
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **etcd's spec of `LeaseGrant` at a success fact `G`, for the requests of a filter `R`** (the
lease-expiry plan's E3, 2026-11-04): `etcdLeaseGrantSpecG`, the caller also showing that its request
(`(TTL, ID)`) is one `R` covers. -/
def etcdLeaseGrantSpecGRW (G : w64 × w64 → w64 → IProp GF) (R : w64 × w64 → Prop) :
    w64 × w64 → (LeaseGrantRespM → IProp GF) → IProp GF :=
  fun (m : w64 × w64) (Φ : LeaseGrantRespM → IProp GF) =>
    iprop(⌜R m⌝ ∗ etcdLeaseGrantSpecGW G m Φ)

end specsHF

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [EM : EtcdModel GF]


/-- **`etcdLeaseGrantSpecGRW` at the messages' models** (S2, heap-free vocabulary, 2026-11-23: the
spec is `etcdLeaseGrantSpecGRW`, over the models alone, what a service table holds; this is its form
at the message types). -/
def etcdLeaseGrantSpecGR (G : w64 × w64 → w64 → IProp GF) (R : w64 × w64 → Prop) :
    GrpcSpec (GF := GF) pbLeaseGrantRequest pbLeaseGrantResponse :=
  etcdLeaseGrantSpecGRW G R

end specs

section specsHF
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF] [GoLocalContext]
variable [sem : go.Semantics]
variable [EM : EtcdModel GF]
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **etcd's spec of `LeaseGrant` at the lessor `γl`, in any lease mode** (the lease-expiry plan's
X2, 2026-11-04): a request with `ID = 0` (E3, 2026-11-04, the user's: generated ids only, as
clientv3's `Grant` sends; in the revocable mode `EtcdServer.LeaseGrant` takes no other) gets a reply
whose lease ID is not `NoLease`, whose header revision etcd has reached, and whose lease is live in
the lessor's history from some index (`leaseLiveFrom`: a revocable lessor may revoke it later, so no
listing need list it). Until E3 it covered any request, and the old contract followed from it
(`isGrpcRpc_leaseGrantLive_any`, unused, removed). (The lease-expiry plan's S2–S4, Q-S8,
2026-11-05) And the lease's request is `req.1` (`lease.leaseReqIs`): every TTL the history gives the
id is at least `req.1` (`lease.leaseTTLAt_ge_req`; until S2–S4 the history's TTL was the lease's
read-only `ttl` field itself, `lease.leaseTTLAt_ttl_agree`, which `Recover` replacing a lease's
`*Lease` breaks). (Review r1 F12, 2026-11-05: until then also that field at least `req.1`, E3/R5,
which no consumer reads since `leaseReqIs`.) (Review r1 F13) `leaseReqIs γl`, like `leaseLiveFrom
γl`, is one member's (the lessor `γl`'s) ghost state: a client asking `TimeToLive` at another member
cannot use it. The cluster-level form is the log's grant entry (`appliedTable`'s `(id, ttl)`) with a
per-member law tying each lessor's request of the id to it (the plan's `srvEver`, a Prove item). -/
def etcdLeaseGrantSpecLiveW (γl : GName) : w64 × w64 → (LeaseGrantRespM → IProp GF) → IProp GF :=
  etcdLeaseGrantSpecGRW (fun (req : w64 × w64) id => iprop(∃ (i : Nat) (l : Loc),
      lease.leaseLiveFrom γl i id l ∗ lease.leaseReqIs γl id req.1))
    (fun m => m.2 = W64 0)

end specsHF

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [EM : EtcdModel GF]


/-- **`etcdLeaseGrantSpecLiveW` at the messages' models** (S2, heap-free vocabulary, 2026-11-23: the
spec is `etcdLeaseGrantSpecLiveW`, over the models alone, what a service table holds; this is its
form at the message types). -/
def etcdLeaseGrantSpecLive (γl : GName) :
    GrpcSpec (GF := GF) pbLeaseGrantRequest pbLeaseGrantResponse :=
  etcdLeaseGrantSpecLiveW γl

end specs

section specsL
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

end specsL

section specsLHF
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF] [GoLocalContext]
variable [sem : go.Semantics]
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **etcd's spec of `LeaseLeases` at the lessor `γl`** (see the file header): the caller's grants
`G` (each granted at some index of this member's lessor: the listing is member-local, see the file
header) are all listed, and no lease twice. -/
def etcdLeaseLeasesSpecW (γl : GName) : Unit → (LeaseLeasesRespM → IProp GF) → IProp GF :=
  fun (_ : Unit) (Φ : LeaseLeasesRespM → IProp GF) =>
    iprop(∃ G : List w64, ([∗list] id ∈ G, ∃ i : Nat, lease.leaseGrantedAt γl i id) ∗
      ∀ m : LeaseLeasesRespM, ⌜m.ids.Nodup ∧ ∀ id ∈ G, id ∈ m.ids⌝ -∗ Φ m)

end specsLHF

section specsL
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]


/-- **`etcdLeaseLeasesSpecW` at the messages' models** (S2, heap-free vocabulary, 2026-11-23: the
spec is `etcdLeaseLeasesSpecW`, over the models alone, what a service table holds; this is its form
at the message types). -/
def etcdLeaseLeasesSpec (γl : GName) :
    GrpcSpec (GF := GF) pbLeaseLeasesRequest pbLeaseLeasesResponse :=
  etcdLeaseLeasesSpecW γl

/-- (S6) The old `LeaseGrant` contract is weaker. -/
theorem etcdLeaseGrantSpec_any [EM : EtcdModel GF] (γl : GName) (m : w64 × w64)
    (Φ : LeaseGrantRespM → IProp GF) :
    etcdLeaseGrantSpecAny (GF := GF) m Φ ⊢ etcdLeaseGrantSpec γl m Φ := by
  unfold etcdLeaseGrantSpecAny etcdLeaseGrantSpecAnyW etcdLeaseGrantSpec etcdLeaseGrantSpecW
  iintro H %r Hid Hr -
  iapply H $$ Hid Hr

/-- (S6) The old `LeaseLeases` contract is weaker (the caller hands in no grant). -/
theorem etcdLeaseLeasesSpec_any (γl : GName) (m : Unit) (Φ : LeaseLeasesRespM → IProp GF) :
    etcdLeaseLeasesSpecAny (GF := GF) m Φ ⊢ etcdLeaseLeasesSpec γl m Φ := by
  unfold etcdLeaseLeasesSpecAny etcdLeaseLeasesSpecAnyW etcdLeaseLeasesSpec etcdLeaseLeasesSpecW
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

end specsLive

section specsLiveHF
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF] [GoLocalContext]
variable [sem : go.Semantics]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **etcd's spec of `LeaseTimeToLive` at the lessor `γl` and the server `s`, in the revocable lease
mode** (the lease-expiry plan's E3, 2026-11-05): the caller hands in a lower bound `m` of the
lessor's history (`lessorLb`), and the reply, about the asked lease, carries, under the lease-TTL row
(`leaseTTLRow s γl`: `s` its cluster's only member, in its first start), that its `GrantedTTL` is the
lease's TTL at an index `≥ m`, or that the lease is absent from `m` on (the server's
`EtcdServer.leaseTimeToLive.spec`'s answer through `LeaseServer.LeaseTimeToLive`, whose TTL `-1`
reply is the not-found arm). -/
def etcdLeaseTTLSpecLiveW (γl : GName) (R : IProp GF) :
    w64 × Bool → (LeaseTTLRespM → IProp GF) → IProp GF :=
  fun (req : w64 × Bool) (Φ : LeaseTTLRespM → IProp GF) =>
    iprop(∃ m : Nat, lease.lessorLb γl m ∗
      ∀ resp : LeaseTTLRespM, ⌜resp.id = req.1⌝ -∗
        □ (R -∗
            (∃ i : Nat, ⌜m ≤ i⌝ ∗ lease.leaseTTLAt γl i resp.id resp.grantedTtl) ∨
            lease.leaseAbsentFrom γl m resp.id) -∗
        Φ resp)

end specsLiveHF

section specsLive
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]


/-- **`etcdLeaseTTLSpecLiveW` at the messages' models** (S2, heap-free vocabulary, 2026-11-23: the
spec is `etcdLeaseTTLSpecLiveW`, over the models alone, what a service table holds; this is its form
at the message types). -/
def etcdLeaseTTLSpecLive (γl : GName) (R : IProp GF) :
    GrpcSpec (GF := GF) pbLeaseTimeToLiveRequest pbLeaseTimeToLiveResponse :=
  etcdLeaseTTLSpecLiveW γl R

end specsLive

section specsLiveHF
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF] [GoLocalContext]
variable [sem : go.Semantics]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **etcd's spec of `LeaseLeases` at the lessor `γl`, in the revocable lease mode** (the
lease-expiry plan's E3, 2026-11-05): the caller hands in a lower bound `m` of the lessor's history,
and the reply lists the lease ids of a snapshot of the history at an index `≥ m` (`leaseIdsAt`: the
ids of its lease map, no id twice). -/
def etcdLeaseLeasesSpecLiveW (γl : GName) : Unit → (LeaseLeasesRespM → IProp GF) → IProp GF :=
  fun (_ : Unit) (Φ : LeaseLeasesRespM → IProp GF) =>
    iprop(∃ m : Nat, lease.lessorLb γl m ∗
      ∀ resp : LeaseLeasesRespM, (∃ j : Nat, ⌜m ≤ j⌝ ∗ lease.leaseIdsAt γl j resp.ids) -∗ Φ resp)

end specsLiveHF

section specsLive
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]


/-- **`etcdLeaseLeasesSpecLiveW` at the messages' models** (S2, heap-free vocabulary, 2026-11-23:
the spec is `etcdLeaseLeasesSpecLiveW`, over the models alone, what a service table holds; this is
its form at the message types). -/
def etcdLeaseLeasesSpecLive (γl : GName) :
    GrpcSpec (GF := GF) pbLeaseLeasesRequest pbLeaseLeasesResponse :=
  etcdLeaseLeasesSpecLiveW γl

/-- A registration with `Spec` is one with `Spec'` if `Spec'` gives `Spec` with the persistent `P`
(`isGrpcRpc_mono` with a context). -/
theorem isGrpcRpc_mono_with {Req Rep : ProtoMsg GF} (addr name : GoString) (P : IProp GF)
    [Persistent P] (Spec Spec' : GrpcSpec Req Rep) (h : ∀ m Φ, P ∗ Spec' m Φ ⊢ Spec m Φ) :
    P ∗ isGrpcRpc addr name Spec ⊢ isGrpcRpc addr name Spec' := by
  iintro ⟨#HP, #H⟩
  unfold isGrpcRpc
  iunfold isGrpcRpcMd at H
  icases H with ⟨%a₀, %hX, %π, %σ, #Hr, #Hs⟩
  unfold isGrpcRpcMd
  iexists a₀, hX, π, σ
  iframe Hr
  iapply (grpcSvcAt_mono_upd (Gg := hG.goose_globalGS) a₀ name Req.wire Rep.wire
    (GrpcSpec.md Spec) (GrpcSpec.md Spec')) $$ [] Hs
  imodintro
  iintro %md %m %Φ %Ψe HS
  imodintro
  simp only [GrpcSpec.md]
  icases HS with ⟨HS, #HΨe⟩
  iframe HΨe
  iapply (h m Φ)
  isplitl []
  · iexact HP
  iexact HS

/-- **A registration of `LeaseTimeToLive` at the revocable mode's spec is one at the old spec**,
with a lower bound of the lessor's history to hand in. -/
theorem isGrpcRpc_leaseTTL_live_any (addr : GoString) (γl : GName) (s : Loc) (m : Nat) :
    lease.lessorLb (GF := GF) γl m ∗
      isGrpcRpc addr go!"/etcdserverpb.Lease/LeaseTimeToLive" (etcdLeaseTTLSpecLive γl (leaseTTLRow s γl)) ⊢
      isGrpcRpc addr go!"/etcdserverpb.Lease/LeaseTimeToLive" etcdLeaseTTLSpec := by
  apply isGrpcRpc_mono_with
  intro r Φ
  unfold etcdLeaseTTLSpec etcdLeaseTTLSpecW etcdLeaseTTLSpecLive etcdLeaseTTLSpecLiveW
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
  unfold etcdLeaseLeasesSpecAny etcdLeaseLeasesSpecAnyW etcdLeaseLeasesSpecLive etcdLeaseLeasesSpecLiveW
  iintro ⟨#Hm, H⟩
  iexists m
  iframe Hm
  iintro %resp ⟨%j, -, #Hids⟩
  ihave %Hnd := lease.leaseIdsAt_nodup γl j resp.ids $$ Hids
  iapply H $$ %resp %Hnd

section monoT
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [EM : EtcdModel GF]

open Iris.ProofMode in
/-- (O2, 2026-11-23) **`LeaseTimeToLive`'s live spec is monotone in the row fact**: a registration
at the server's row `R1` (`leaseTTLRow s γl`) serves a caller at `R2` (a table's `⌜row = true⌝`)
when `□ (R2 -∗ R1)`. -/
theorem etcdLeaseTTLSpecLiveW_mono (γl : GName) (R1 R2 : IProp GF) (req : w64 × Bool)
    (Φ : LeaseTTLRespM → IProp GF) :
    iprop(□ (R2 -∗ R1)) ∗ etcdLeaseTTLSpecLiveW γl R2 req Φ ⊢ etcdLeaseTTLSpecLiveW γl R1 req Φ := by
  unfold etcdLeaseTTLSpecLiveW
  iintro ⟨#HR, %m, Hl, Hk⟩
  iexists m
  iframe Hl
  iintro %r %h #Hrow
  iapply Hk $$ %r %h
  imodintro
  iintro Hr2
  iapply Hrow
  iapply HR $$ Hr2

end monoT

end specsLive

end EtcdGrove
end Perennial
