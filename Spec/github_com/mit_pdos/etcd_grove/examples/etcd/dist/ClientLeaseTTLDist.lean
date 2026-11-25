/-
`cli.Lease.TimeToLive(ctx, id)` by `New`'s client of a member at another machine (#50 N9b, 2026-11-25;
`notes/etcd-dist-n9b.md` §6). Lean-first (no Rocq counterpart).

**A DRAFT OF N2's INTERFACE, pending the `etcd_safe` lead** (N2/I-1, `notes/etcd-dist-plan.md` §17.2): a
statement only, with no proof and no axiom, as `ClientLeaseLeasesDist.lean` (see there).
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

/-- **`cli.Lease.TimeToLive(ctx, id)` (no options) by `New`'s client of a member at another machine**
(DRAFT, N2-owned: see the file header): `nil` and a reply about the lease asked, its `ID` field `id`
(`etcdLeaseTTLSpecW`: the member's answer for any of its lessor's states, so nothing of its view is read); or
an error. Only the call without options (`slice.nil`), the one the dist workloads make. -/
abbrev Client_LeaseTimeToLive_dist.spec : Prop :=
  ∀ [π : NetProtoGS] (cl lp : Loc) (ep : GoString) (V : WEnv GF) (γE : GName) (mid : w64)
    (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isNewClient cl [ep] V ∗
      clientNoProxy cl ∗
      clientF cl go!"Lease" ↦□
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty) #lp : GoInterface) ∗
      etcdAddrAt (Gg := hG.goose_globalGS) ep γE mid ∗
      ctxOk ci cd ∗ ctxErrClient ci cd }}
    (App (App (App (Val (lp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty @!!
        go!"TimeToLive")) (Val #(GoInterface.ok ci))) (Val #id)) (Val #slice.nil))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (⌜err = GoInterface.nil⌝ ∗
          structFieldRef go_etcd_io.etcd.client.v3.LeaseTimeToLiveResponse go!"ID" resp ↦□ id) ∨
        ⌜err ≠ GoInterface.nil ∧ resp = null⌝ }}

end spec

end etcd_dist
end EtcdGrove
end Perennial
