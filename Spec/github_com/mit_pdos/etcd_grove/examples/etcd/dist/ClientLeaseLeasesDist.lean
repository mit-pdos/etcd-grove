/-
`cli.Lease.Leases(ctx)` by `New`'s client of a member at another machine (#50 N9b, 2026-11-25;
`notes/etcd-dist-n9b.md` §6). Lean-first (no Rocq counterpart).

**A DRAFT OF N2's INTERFACE, pending the `etcd_safe` lead** (N2/I-1, `notes/etcd-dist-plan.md` §17.2): a
statement only, with no proof and no axiom. N9b's proofs (`dist/client`'s `leaseList`, `leaseReadCheck`,
`RunLeaseRead`) take it as a callee hypothesis; it becomes a theorem when N2 gives the lease entries of etcd's
service table (`etcdSvc`) a law and #24's S2 re-proves clientv3's lease calls over the grpc model, or the lead
adds it as a reviewed interim axiom (as `Client_Get_dist`). The lead may reshape it.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.S2Interim
public import Proof.go_etcd_io.etcd.client.v3.InvClientNewResult
public import Proof.go_etcd_io.etcd.client.v3.InvLeaseRead

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Net client go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **`cli.Lease.Leases(ctx)` by `New`'s client of a member at another machine** (DRAFT, N2-owned: see the
file header): the client's `Lease` is the `*lessor` `lp`, called with a context the client accepts; the
member at `ep` serves etcd's table. `nil` and a listing that names no lease twice
(`etcdLeaseLeasesSpecAnyW`: what the member's `LeaseLeases` answers, about any of its lessor's states, so
nothing of the member's view is read); or an error.

The caller's `levelTok 0` is lent and returned (review N9b, `notes/axiom-review/n9b-lease-leases.md`): as in the proved in-process `lessor.Leases.spec`/`lessor.TimeToLive.spec`, the retry interceptor's backoff reads `c.Endpoints()` under `epMu`'s read lock (`backoffOkT`), a reader slot the bounds discipline pays with the token (CLAUDE.md, "Bounds"). Its member side: the call reaches a member's `LeaseLeases`/`LeaseTimeToLive` handler, proved in one process against `etcdLeaseLeasesSpecAny`/`etcdLeaseTTLSpec` (`LeaseReadServed.lean`); when this becomes an axiom, `etcdSvc`'s and `Serve_dist`'s docstrings (which name only the KV calls, review F4) must list these entries. -/
abbrev Client_LeaseLeases_dist.spec : Prop :=
  ∀ [π : NetProtoGS] (cl lp : Loc) (ep : GoString) (V : WEnv GF) (γE : GName) (mid : w64)
    (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
      isNewClient cl [ep] V ∗
      clientNoProxy cl ∗
      clientF cl go!"Lease" ↦□
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty) #lp : GoInterface) ∗
      etcdAddrAt (Gg := hG.goose_globalGS) ep γE mid ∗
      ctxOk ci cd ∗ ctxErrClient ci cd }}
    (App (Val (lp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty @!! go!"Leases"))
      (Val #(GoInterface.ok ci)))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (ids : List w64) (sl : GoSlice),
          structFieldRef go_etcd_io.etcd.client.v3.LeaseLeasesResponse go!"Leases" resp ↦□ sl ∗
          sl ↦* (ids.map (fun id => (go_etcd_io.etcd.client.v3.LeaseStatus.mk id))) ∗ ⌜ids.Nodup⌝) ∨
        ⌜err ≠ GoInterface.nil ∧ resp = null⌝) }}

end spec

end etcd_dist
end EtcdGrove
end Perennial
