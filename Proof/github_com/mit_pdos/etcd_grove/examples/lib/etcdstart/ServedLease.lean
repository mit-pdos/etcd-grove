/-
**etcd's KV calls and lease reads registered at a served member's address** (the closed lease
example, 2026-11-02, `notes/lease-ex-plan.md`). Lean-first (no Rocq counterpart).

`kv_lease_served`: `kv_served`'s ghost step, with the Lease service's reads served too
(`client.etcdLeaseReadAt`: `LeaseTimeToLive`, `LeaseLeases` at etcd's specs), from `grpcUp`'s
Lease service (`grpcLeaseUp`) and the member's lessor reader side (`memberUp`'s `srvLeaseRd`). One
`grpc.serve` serves every method, with one slot: the KV's run resources and the level-0 token
(`etcdGrpcSlot s E γr`, the token among the interceptors' lent resources since prove-ps2-cap,
2026-11-23; a run's bundle `srvRunBundle` by `client.etcdGrpcSlot_bundle`),
which each run borrows from the server's run pools, built here from `memberUp`'s stocks
(`kvServeStocks_pools`; per-type stage B3: until then a thread token the caller gave). The lease
reads take the token with `E.RD` and the store's reader (`raftLeaseRead_server`'s
`E.RD ∗ levelTok 0`); the KV's runs frame it through.

In a cluster that grants leases (the KV names' `lg`; the lease-grant plan's 2.2, 2026-11-03: one lemma
taking `lg`, which replaced the draft `kv_lease_grant_served`), `LeaseGrant` and `LeaseLeases` are
registered at the specs at the lessor's history instead (`etcdLeaseGrantAt`): a grant's reply carries
its lease's grant (`etcdLeaseGrantSpec`), and a listing lists every grant the caller hands in
(`etcdLeaseLeasesSpec`); the KV's registrations are not passed on (the KV service makes no claim in
that cluster, the plan's Q1). The grant handler calls the server's (`v3rpc.lessorGrantOkLM_server`).
`kv_lease_served_false`: the post at `lg = false`, as before. `kv_lease_served_watch` (lease-mono3's
pass 2(c), 2026-11-06): the same, with the member's `Watch` stream served at the address,
`noRefusalAt` and `srvGoRes` (what `cluster3.memberServed` keeps in every lease mode).

Why one member's lessor (review S5): the contracts name `(mvcc.api.mvccLeases E.γ)`, this member's, not a
cluster-level certificate, because Go's listing is member-local: `LeaseLeases` reads the member's
own lessor without a read index (`v3_server.go:737-749`), so a lagging member need not list a lease
the cluster granted, and a cluster-level contract would be false. With several endpoints the client
would need the contracts at every member, which no granting cluster gives.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Served
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LeaseSrc
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb._Lease_LeaseTimeToLive_Handler
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb._Lease_LeaseLeases_Handler
public import Proof.go_etcd_io.etcd.client.v3.InvLeaseGrant
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcdstart

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section served
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- **`LeaseGrant` and `LeaseLeases` registered at the specs at the lessor `(mvcc.api.mvccLeases E.γ)`'s
history** (persistent). Per member, not per cluster: `LeaseLeases` is a member-local read (see
the file header). -/
def etcdLeaseGrantAt (addr : GoString) (E : apply.AEnv GF) (γr : ReadNames) : IProp GF :=
  iprop(isGrpcRpc addr go!"/etcdserverpb.Lease/LeaseGrant"
      (etcdLeaseGrantSpec (EM := v3rpc.etcdModelOfServer E γr false) (mvcc.api.mvccLeases E.γ)) ∗
    isGrpcRpc addr go!"/etcdserverpb.Lease/LeaseLeases" (etcdLeaseLeasesSpec (mvcc.api.mvccLeases E.γ)))

instance etcdLeaseGrantAt_persistent (addr : GoString) (E : apply.AEnv GF) (γr : ReadNames) :
    Persistent (etcdLeaseGrantAt addr E γr) := by
  unfold etcdLeaseGrantAt; infer_instance

omit [HasExt idIssueExt] cache_sem in
/-- **`etcdLeaseGrantAt` gives its two registrations** (lease-mono3's review r2, N1: the
elimination a client uses in place of unfolding the definition). -/
theorem etcdLeaseGrantAt_elim (addr : GoString) (E : apply.AEnv GF) (γr : ReadNames) :
    etcdLeaseGrantAt addr E γr ⊢
      isGrpcRpc addr go!"/etcdserverpb.Lease/LeaseGrant"
          (etcdLeaseGrantSpec (EM := v3rpc.etcdModelOfServer E γr false) (mvcc.api.mvccLeases E.γ)) ∗
        isGrpcRpc addr go!"/etcdserverpb.Lease/LeaseLeases" (etcdLeaseLeasesSpec (mvcc.api.mvccLeases E.γ)) := by
  iintro #H
  iunfold etcdLeaseGrantAt at H
  iexact H

/-- **`LeaseGrant`, `LeaseTimeToLive` and `LeaseLeases` registered at the revocable mode's specs**
(persistent; the lease-expiry plan's X2, 2026-11-04, the reads since E3, 2026-11-05): a grant's reply
carries its lease live in the lessor `(mvcc.api.mvccLeases E.γ)`'s history and its request, the requested TTL
(`etcdLeaseGrantSpecLive`; the lease-expiry plan's S2–S4, Q-S8; review r1 F12: until then the
lease's read-only `ttl` field at least the request); a TTL reply, at the caller's lower bound of the history, the lease's TTL there or its absence, under the
lease-TTL row of the server `s` (`etcdLeaseTTLSpecLive`); a listing, the lease ids of a snapshot no
older than the caller's lower bound (`etcdLeaseLeasesSpecLive`: no grant listed, the lessor may have
revoked it). -/
def etcdLeaseGrantLiveAt (addr : GoString) (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) : IProp GF :=
  iprop(isGrpcRpc addr go!"/etcdserverpb.Lease/LeaseGrant"
      (etcdLeaseGrantSpecLive (EM := v3rpc.etcdModelOfServer E γr false) (mvcc.api.mvccLeases E.γ)) ∗
    isGrpcRpc addr go!"/etcdserverpb.Lease/LeaseTimeToLive" (etcdLeaseTTLSpecLive (mvcc.api.mvccLeases E.γ) s) ∗
    isGrpcRpc addr go!"/etcdserverpb.Lease/LeaseLeases" (etcdLeaseLeasesSpecLive (mvcc.api.mvccLeases E.γ)))

instance etcdLeaseGrantLiveAt_persistent (addr : GoString) (s : Loc) (E : apply.AEnv GF)
    (γr : ReadNames) : Persistent (etcdLeaseGrantLiveAt addr s E γr) := by
  unfold etcdLeaseGrantLiveAt; infer_instance

/-- **What a served member registers besides the lease reads, by its lease mode `m`** (the
lease-expiry plan's X2, 2026-11-04): the KV calls in the mode `none` (a cluster that grants no
lease); the grant and the listing at the lessor's history in the monotone mode (`etcdLeaseGrantAt`);
the grant at the live spec and the reads at the server `s`'s lessor in the revocable mode
(`etcdLeaseGrantLiveAt`). -/
def etcdLeaseServedAt (m : lease.Mode) (addr : GoString) (s : Loc) (E : apply.AEnv GF)
    (ρ : ReqNames) (γr : ReadNames) (cid mid : w64) : IProp GF :=
  match m with
  | .none => etcdKVAt addr E ρ γr cid mid
  | .mono => etcdLeaseGrantAt addr E γr
  | .revocable => etcdLeaseGrantLiveAt addr s E γr

instance etcdLeaseServedAt_persistent (m : lease.Mode) (addr : GoString) (s : Loc)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (cid mid : w64) :
    Persistent (etcdLeaseServedAt m addr s E ρ γr cid mid) := by
  cases m <;> unfold etcdLeaseServedAt <;> infer_instance

omit [HasExt idIssueExt] cache_sem in
/-- **`etcdLeaseServedAt` in the mode `none` is the KV calls** (`rfl`; lease-mono3's review r2,
N1). -/
theorem etcdLeaseServedAt_none (addr : GoString) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (γr : ReadNames) (cid mid : w64) :
    etcdLeaseServedAt .none addr s E ρ γr cid mid = etcdKVAt addr E ρ γr cid mid := rfl

omit [HasExt idIssueExt] cache_sem in
/-- **`etcdLeaseServedAt` in the monotone mode is the grant and the listing at the lessor's
history** (`rfl`; lease-mono3's review r2, N1). -/
theorem etcdLeaseServedAt_mono (addr : GoString) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (γr : ReadNames) (cid mid : w64) :
    etcdLeaseServedAt .mono addr s E ρ γr cid mid = etcdLeaseGrantAt addr E γr := rfl

end served

end etcdstart
end EtcdGrove
end Perennial
