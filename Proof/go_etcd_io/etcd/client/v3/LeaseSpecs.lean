/-
**The lease services' metadata-indexed specs** (auth-lease S4; moved out of the linking modules
`LeaseReadServed.lean` and `LeaseGrantServed.lean`, names and statements unchanged, so that specs and
definitions can name them without importing a linking module: CLAUDE.md, "Import tiers"):
`etcdLeaseTTLSpecMd`, `etcdLeaseLeasesSpecMd`, `etcdLeaseGrantSpecOn`, `etcdLeaseRevokeSpecOn`; and the
permits' unfoldings `kvOpAuOn_leaseGrant`/`kvOpAuOn_leaseRevoke` (out of `ResultsOn.lean`).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.PerTypeLease
public import Proof.go_etcd_io.etcd.client.v3.InvLeaseRead
public import Proof.go_etcd_io.etcd.client.v3.InvLeaseGrant
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvLeaseGrant
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvLeaseKeepAlive
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LeaseReqOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LeaseCheck
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LeaseRead
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ServerKVOn
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb._Lease_LeaseTimeToLive_Handler
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb._Lease_LeaseLeases_Handler

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace client

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

section specsMd
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

end specsMd

section specsMdHF
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF] [GoLocalContext]
variable [sem : go.Semantics]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- (Auth-lease S4, Freeze §4.1, rev 2's R1/R2) **etcd's `LeaseTimeToLive` at the lessor `γl`, metadata-indexed**
(new; the one spec of the handler, any auth mode): a reply's lease is the request's; its TTL row fact
(`etcdLeaseTTLSpecLive`'s, kept so that this text subsumes `etcdLeaseTTLSpec`/`…Live`); the check passed
at the token (`leaseCheckFrom`: auth off at `≥ n`, or a principal bound to the token that is an admin or,
with keys, has read on every key the lease holds from `m` on; without keys, `True`: `requireAuthInfo`'s
authentication alone, R1). An error carries nothing. -/
def etcdLeaseTTLSpecMdW (T R : IProp GF) (E : apply.AEnv GF) (γl : GName) :
    GrpcMd → w64 × Bool → (LeaseTTLRespM → IProp GF) → (GoString → IProp GF) → IProp GF :=
  fun md (req : w64 × Bool) (Φ : LeaseTTLRespM → IProp GF) (Ψe : GoString → IProp GF) =>
    iprop((□ ∀ d, Ψe d) ∗ ∃ n m : Nat, auth.authPubLbM E.authMode n ∗ lease.lessorLb γl m ∗
      ∀ r : LeaseTTLRespM, ⌜r.id = req.1⌝ -∗
        □ (R -∗
            (∃ i : Nat, ⌜m ≤ i⌝ ∗ lease.leaseTTLAt γl i r.id r.grantedTtl) ∨
            lease.leaseAbsentFrom γl m r.id) -∗
        leaseCheckFrom T E (auth.mdTokenOf md) n
          (fun info => if req.2 then leaseKeysVerdictFrom E.authMode n info γl m req.1 .read
            else iprop(True)) -∗
        Φ r)

end specsMdHF

section specsMd
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]


/-- **`etcdLeaseTTLSpecMdW` at the messages' models** (S2, heap-free vocabulary, 2026-11-23: the
spec is `etcdLeaseTTLSpecMdW`, over the models alone, what a service table holds; this is its form
at the message types). -/
def etcdLeaseTTLSpecMd (T R : IProp GF) (E : apply.AEnv GF) (γl : GName) :
    GrpcSpecMd (GF := GF) pbLeaseTimeToLiveRequest pbLeaseTimeToLiveResponse :=
  etcdLeaseTTLSpecMdW T R E γl

end specsMd

section specsMdHF
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF] [GoLocalContext]
variable [sem : go.Semantics]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- (Auth-lease S4, Freeze §4.2, rev 2's R2) **etcd's `LeaseLeases` at the lessor `γl`, metadata-indexed** (new; the one spec,
any auth mode): a listing at some lessor index `i ≥ m`, no duplicates, every listed lease's keys
verdict at the token. Subsumes `etcdLeaseLeasesSpecLive` and `…Any`. -/
def etcdLeaseLeasesSpecMdW (T : IProp GF) (E : apply.AEnv GF) (γl : GName) :
    GrpcMd → Unit → (LeaseLeasesRespM → IProp GF) → (GoString → IProp GF) → IProp GF :=
  fun md (_ : Unit) (Φ : LeaseLeasesRespM → IProp GF) (Ψe : GoString → IProp GF) =>
    iprop((□ ∀ d, Ψe d) ∗ ∃ n m : Nat, auth.authPubLbM E.authMode n ∗ lease.lessorLb γl m ∗
      ∀ r : LeaseLeasesRespM, ⌜r.ids.Nodup⌝ -∗
        (∃ i : Nat, ⌜m ≤ i⌝ ∗ lease.leaseIdsAt γl i r.ids ∗
          leaseCheckFrom T E (auth.mdTokenOf md) n
            (fun info => iprop([∗list] id ∈ r.ids, leaseKeysVerdictFrom E.authMode n info γl i id .read))) -∗
        Φ r)

end specsMdHF

section specsMd
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]


/-- **`etcdLeaseLeasesSpecMdW` at the messages' models** (S2, heap-free vocabulary, 2026-11-23: the
spec is `etcdLeaseLeasesSpecMdW`, over the models alone, what a service table holds; this is its
form at the message types). -/
def etcdLeaseLeasesSpecMd (T : IProp GF) (E : apply.AEnv GF) (γl : GName) :
    GrpcSpecMd (GF := GF) pbLeaseLeasesRequest pbLeaseLeasesResponse :=
  etcdLeaseLeasesSpecMdW T E γl

end specsMd

section specsOn
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

end specsOn

section specsOnHF
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF] [GoLocalContext]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **etcd's `LeaseGrant` with auth on, at the lessor `γl`** (auth-lease S3c, Draft §7.2; as
`etcdPutSpecOn`, metadata-indexed): a request with `ID = 0` (as `etcdLeaseGrantSpecLive`'s filter),
the caller's update `Q` handed over in the grant's permit at the token of the attempt's metadata
(`leaseGrantPermitM`, `v3rpc.hdrBoundT … (auth.mdTokenOf md)`); a reply's lease ID is not `NoLease`,
its header revision etcd has reached, its lease live in the lessor's history from some index with
the request's TTL (`etcdLeaseGrantSpecLive`'s fact), and the caller's result at the token
(`v3rpc.leaseGrantResT`: with auth on, the grant published at a log and `Q` of the model's state
after it). An error carries nothing (`□ ∀ d, Ψe d`, `etcdPutSpecOn`'s HS-4). (Auth-lease S4, D-h) For a
caller holding a lower bound `n` of the published auth index, the reply also carries `requireAuthInfo`'s
check at the attempt's token relative to `n` (`leaseCheckFrom … n (fun _ => True)`: auth disabled at a state no
older than `n`, or a principal bound to the token); `Q` is of the model's state **before** the grant. -/
def etcdLeaseGrantSpecOnW (T : IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) (γl : GName) :
    GrpcMd → w64 × w64 → (LeaseGrantRespM → IProp GF) → (GoString → IProp GF) → IProp GF :=
  fun md (req : w64 × w64) (Φ : LeaseGrantRespM → IProp GF) (Ψe : GoString → IProp GF) =>
    iprop((□ ∀ d, Ψe d) ∗ ⌜req.2 = W64 0⌝ ∗ ∃ n : Nat, auth.authPubLbM E.authMode n ∗
      ∃ Q : w64 → KVState → IProp GF,
      leaseGrantPermitM E.authOn ρ.raft ρ.kv (v3rpc.hdrBoundT T E.authMode (auth.mdTokenOf md)) req.1 Q ∗
      ∀ m : LeaseGrantRespM, ⌜m.id ≠ W64 0⌝ -∗
        etcdReached (EM := v3rpc.etcdModelOfServer E ρ.rd E.authOn) m.hdr.revision -∗
        (∃ (i : Nat) (l : Loc), lease.leaseLiveFrom γl i m.id l ∗ lease.leaseReqIs γl m.id req.1) -∗
        v3rpc.leaseGrantResT E.authOn T E ρ (auth.mdTokenOf md) req.1 m.id Q -∗
        leaseCheckFrom T E (auth.mdTokenOf md) n (fun _ => iprop(True)) -∗
        Φ m)

end specsOnHF

section specsOn
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]


/-- **`etcdLeaseGrantSpecOnW` at the messages' models** (S2, heap-free vocabulary, 2026-11-23: the
spec is `etcdLeaseGrantSpecOnW`, over the models alone, what a service table holds; this is its form
at the message types). -/
def etcdLeaseGrantSpecOn (T : IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) (γl : GName) :
    GrpcSpecMd (GF := GF) pbLeaseGrantRequest pbLeaseGrantResponse :=
  etcdLeaseGrantSpecOnW T E ρ γl

end specsOn

section specsOnHF
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF] [GoLocalContext]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **etcd's `LeaseRevoke` with auth on** (auth-lease S3c, Draft §7.2; as `etcdLeaseGrantSpecOn`):
the caller's update `Q` handed over in the revocation's permit at the token of the attempt's
metadata; a reply's header revision etcd has reached, and the caller's result at the token
(`v3rpc.leaseRevokeResT`: with auth on, the revocation granted and published at a log and `Q` of
the model's state after it). An error carries nothing. (Auth-lease S4, D-h) With the same `n`-relative
check as `etcdLeaseGrantSpecOn`. -/
def etcdLeaseRevokeSpecOnW (T : IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) :
    GrpcMd → w64 → (LeaseRevokeRespM → IProp GF) → (GoString → IProp GF) → IProp GF :=
  fun md (id : w64) (Φ : LeaseRevokeRespM → IProp GF) (Ψe : GoString → IProp GF) =>
    iprop((□ ∀ d, Ψe d) ∗ ∃ n : Nat, auth.authPubLbM E.authMode n ∗ ∃ Q : KVState → IProp GF,
      leaseRevokePermitM E.authOn ρ.raft ρ.kv (v3rpc.hdrBoundT T E.authMode (auth.mdTokenOf md)) id Q ∗
      ∀ m : LeaseRevokeRespM, etcdReached (EM := v3rpc.etcdModelOfServer E ρ.rd E.authOn) m.hdr.revision -∗
        v3rpc.leaseRevokeResT E.authOn T E ρ (auth.mdTokenOf md) id Q -∗
        leaseCheckFrom T E (auth.mdTokenOf md) n (fun _ => iprop(True)) -∗
        Φ m)

end specsOnHF

section specsOn
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]


/-- **`etcdLeaseRevokeSpecOnW` at the messages' models** (S2, heap-free vocabulary, 2026-11-23: the
spec is `etcdLeaseRevokeSpecOnW`, over the models alone, what a service table holds; this is its
form at the message types). -/
def etcdLeaseRevokeSpecOn (T : IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) :
    GrpcSpecMd (GF := GF) pbLeaseRevokeRequest pbLeaseRevokeResponse :=
  etcdLeaseRevokeSpecOnW T E ρ

end specsOn

section permits
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- A lease grant's update at a token is the grant's permit's (`opGrantT`'s lease row, Freeze C1). -/
theorem kvOpAuOn_leaseGrant (T : IProp GF) [Persistent T] (E : apply.AEnv GF) (ρ : ReqNames) (tok : Option GoString)
    (id ttl : w64) (Q : KVState → IProp GF) :
    v3rpc.kvOpAuOn (GF := GF) T E ρ tok (.leaseGrant id ttl) Q ⊢
      ∃ L₀ : List EntryModel, srvReqLogLb ρ.raft L₀ ∗
        kvAu1G ρ.kv (kvOpStep (.leaseGrant id ttl))
          (writeGrantG ρ.kv srvAuthSt0 (v3rpc.hdrBoundT T E.authMode tok) (irrLeaseGrant id ttl) L₀) Q := by
  unfold v3rpc.kvOpAuOn v3rpc.opGrantT; exact .rfl

/-- A lease revocation's update at a token is the revocation's permit's. -/
theorem kvOpAuOn_leaseRevoke (T : IProp GF) [Persistent T] (E : apply.AEnv GF) (ρ : ReqNames) (tok : Option GoString)
    (id : w64) (Q : KVState → IProp GF) :
    v3rpc.kvOpAuOn (GF := GF) T E ρ tok (.leaseRevoke id) Q ⊢
      ∃ L₀ : List EntryModel, srvReqLogLb ρ.raft L₀ ∗
        kvAu1G ρ.kv (kvOpStep (.leaseRevoke id))
          (writeGrantG ρ.kv srvAuthSt0 (v3rpc.hdrBoundT T E.authMode tok) (irrLeaseRevoke id) L₀) Q := by
  unfold v3rpc.kvOpAuOn v3rpc.opGrantT; exact .rfl

section monoT
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-! ### O2: monotonicity in the TLS and lease-TTL row facts (2026-11-23)

Each lease table spec is antitone in `T` and monotone in `R`: a registration at the server's
(`srvTLSId s`, `leaseTTLRow s γl`) serves a caller at the table's (`⌜tls = true⌝`, `⌜row = true⌝`)
when `□ (T1 -∗ T2)` and `□ (R2 -∗ R1)`. -/

open Iris.ProofMode in
theorem etcdLeaseTTLSpecMdW_mono (T1 T2 R1 R2 : IProp GF) (E : apply.AEnv GF) (γl : GName)
    (md : GrpcMd) (req : w64 × Bool) (Φ : LeaseTTLRespM → IProp GF) (Ψe : GoString → IProp GF) :
    iprop(□ (T1 -∗ T2)) ∗ iprop(□ (R2 -∗ R1)) ∗ etcdLeaseTTLSpecMdW T2 R2 E γl md req Φ Ψe ⊢
      etcdLeaseTTLSpecMdW T1 R1 E γl md req Φ Ψe := by
  unfold etcdLeaseTTLSpecMdW
  iintro ⟨#HT, #HR, He, %n, %m, Hp, Hl, Hk⟩
  iframe He
  iexists n, m
  iframe Hp Hl
  iintro %r %h #Hrow Hc
  iapply Hk $$ %r %h
  · imodintro
    iintro Hr2
    iapply Hrow
    iapply HR $$ Hr2
  iapply leaseCheckFrom_monoT T1 T2
  iframe HT Hc

open Iris.ProofMode in
theorem etcdLeaseLeasesSpecMdW_mono (T1 T2 : IProp GF) (E : apply.AEnv GF) (γl : GName)
    (md : GrpcMd) (u : Unit) (Φ : LeaseLeasesRespM → IProp GF) (Ψe : GoString → IProp GF) :
    iprop(□ (T1 -∗ T2)) ∗ etcdLeaseLeasesSpecMdW T2 E γl md u Φ Ψe ⊢
      etcdLeaseLeasesSpecMdW T1 E γl md u Φ Ψe := by
  unfold etcdLeaseLeasesSpecMdW
  iintro ⟨#HT, He, %n, %m, Hp, Hl, Hk⟩
  iframe He
  iexists n, m
  iframe Hp Hl
  iintro %r %h ⟨%i, %hi, Hids, Hc⟩
  iapply Hk $$ %r %h
  iexists i
  isplitr
  · ipureintro; exact hi
  iframe Hids
  iapply leaseCheckFrom_monoT T1 T2
  iframe HT Hc

open Iris.ProofMode in
theorem etcdLeaseGrantSpecOnW_mono (T1 T2 : IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) (γl : GName)
    (md : GrpcMd) (req : w64 × w64) (Φ : LeaseGrantRespM → IProp GF) (Ψe : GoString → IProp GF) :
    iprop(□ (T1 -∗ T2)) ∗ etcdLeaseGrantSpecOnW T2 E ρ γl md req Φ Ψe ⊢
      etcdLeaseGrantSpecOnW T1 E ρ γl md req Φ Ψe := by
  unfold etcdLeaseGrantSpecOnW
  iintro ⟨#HT, He, %h0, %n, Hp, %Q, Hpm, Hk⟩
  iframe He
  isplitr
  · ipureintro; exact h0
  iexists n
  iframe Hp
  iexists Q
  isplitl [Hpm]
  · iapply leaseGrantPermitM_mono_with _ _ _ _ _ _ _ iprop(□ (T1 -∗ T2))
      (fun hm => v3rpc.hdrBoundT_mono T1 T2 E.authMode (auth.mdTokenOf md) hm)
    iframe HT Hpm
  iintro %m Hid Hr Hlv Hres Hc
  iapply Hk $$ Hid Hr Hlv [Hres] [Hc]
  · iapply v3rpc.leaseGrantResT_mono _ T1 T2
    iframe HT Hres
  · iapply leaseCheckFrom_monoT T1 T2
    iframe HT Hc

open Iris.ProofMode in
theorem etcdLeaseRevokeSpecOnW_mono (T1 T2 : IProp GF) (E : apply.AEnv GF) (ρ : ReqNames)
    (md : GrpcMd) (id : w64) (Φ : LeaseRevokeRespM → IProp GF) (Ψe : GoString → IProp GF) :
    iprop(□ (T1 -∗ T2)) ∗ etcdLeaseRevokeSpecOnW T2 E ρ md id Φ Ψe ⊢
      etcdLeaseRevokeSpecOnW T1 E ρ md id Φ Ψe := by
  unfold etcdLeaseRevokeSpecOnW
  iintro ⟨#HT, He, %n, Hp, %Q, Hpm, Hk⟩
  iframe He
  iexists n
  iframe Hp
  iexists Q
  isplitl [Hpm]
  · iapply leaseRevokePermitM_mono_with _ _ _ _ _ _ _ iprop(□ (T1 -∗ T2))
      (fun hm => v3rpc.hdrBoundT_mono T1 T2 E.authMode (auth.mdTokenOf md) hm)
    iframe HT Hpm
  iintro %m Hr Hres Hc
  iapply Hk $$ Hr [Hres] [Hc]
  · iapply v3rpc.leaseRevokeResT_mono _ T1 T2
    iframe HT Hres
  · iapply leaseCheckFrom_monoT T1 T2
    iframe HT Hc

end monoT

end permits

end client
end EtcdGrove
end Perennial
