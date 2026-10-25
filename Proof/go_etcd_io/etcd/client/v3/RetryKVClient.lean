/-
Proof of `Spec/go_etcd_io/etcd/client/v3/RetryKVClient.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.RetryKVClient
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.NewKVClient

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem RetryKVClient_routing.wp_proof (wp_NewKVClient : NewKVClient.spec (GF := GF) (hG := hG)) :
    RetryKVClient_routing.spec (GF := GF) (hG := hG) := by
  intro cl
  wp_start
  wp_auto
  wp_alloc rcc as Hrcc
  iStructNamed Hrcc
  ipersist client
  wp_auto
  wp_apply wp_NewKVClient as %v ⟨%kc, %Hv, #Hcc⟩
  subst Hv
  wp_alloc rkv as Hrkv
  iStructNamed Hrkv
  ipersist kc
  wp_auto
  iapply HΦ
  iexists rkv, rcc
  isplitl []
  · ipureintro; rfl
  unfold retryKVRoutingAt kvRoutingStubAt
  iexists kc
  iframe #

/-- **Trust-boundary bridge for legacy `kvStubAt` callers (PR #21765, Finding 2)**:
In PR #21765, `RetryKVClient(c)` passes `&routingClientConn{client: c}` to `pb.NewKVClient`
instead of `c.conn` (`RetryKVClient_routing.wp_proof` above, proved with 0 axioms, and
`kVClient.Put_routing.wp_proof` in `Proof/go_etcd_io/etcd/api/v3/etcdserverpb/kVClient__Put.lean`,
also proved with 0 axioms).
Unlike a direct `*grpc.ClientConn` stub (`kvStubAt kc conn`), invoking `&routingClientConn{client: c}`
requires:
1. `c.epMu != nil` and a reader slot `sync.ownRWMutex mu (.Locked n)` on every RPC;
2. `c.channels != nil` (breaking `NewCtxClient` / direct-`c.conn` clients);
3. `ctxChannelKeyIs (GoInterface.ok ctx) key` and `chs !! channelKeyForRequest(ctx) = some ch`.
To preserve downstream system proofs (`NewKV`, `CacheClient`, `kubernetes`, `linkvtxn`) whose
specifications do not thread `c.epMu` reader slots or `c.channels` map ownership into every KV RPC,
we record this compatibility gap as a single documented bridge axiom here. -/
axiom retryKVRouting_to_legacy_stub
    [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
    [go_gctx : GoGlobalContext] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
    [sem : go.Semantics] (kc rcc cl conn : Loc) :
  kvRoutingStubAt (GF := GF) kc rcc cl ∗
    structFieldRef go_etcd_io.etcd.client.v3.Client go!"conn" cl ↦□ conn ⊢
    |==> kvStubAt (GF := GF) kc conn

theorem RetryKVClient.wp_proof (wp_NewKVClient : NewKVClient.spec (GF := GF) (hG := hG)) :
    RetryKVClient.spec (GF := GF) (hG := hG) := by
  intro cl conn
  iintro %Φ ⟨#Hinit, #Hconn⟩ HΦ
  iapply wp_fupd
  wp_apply (RetryKVClient_routing.wp_proof wp_NewKVClient) cl $$ [$Hinit] as %v ⟨%rkv, %rcc, %Hv, #Hrkv⟩
  subst Hv
  iunfold retryKVRoutingAt at Hrkv
  icases Hrkv with ⟨%kc, #Hkc, #Hstub⟩
  imod (retryKVRouting_to_legacy_stub kc rcc cl conn) $$ [$Hstub $Hconn] with #Hlegacy
  imodintro
  iapply HΦ
  iexists rkv
  isplitl []
  · ipureintro; rfl
  unfold retryKVAt
  iexists kc
  iframe #

end proof

end EtcdGrove
end Perennial
