/-
`(*lessor).TimeToLive(ctx, id)` (no options) at a member (view-free), by a client of a member at another machine, at the cluster view (`notes/etcd-dist-plan.md` §18.4; an
interim trust-boundary axiom until #24's S2 client side: `Proof/.../etcd/dist/ClientLeaseTTLDist.lean`). Lean-first (no Rocq
counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.ClientViewDist

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist
namespace view

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

/-- **`Client_LeaseTimeToLive_dist` (etcd-grove-03's draft) re-indexed by the view**, as
`Client_LeaseLeases_dist` above. View-free (`etcdLeaseTTLSpecW`), the call without options. -/
abbrev Client_LeaseTimeToLive_dist.spec : Prop :=
  ∀ [π : NetProtoGS] (cl lp : Loc) (ep : GoString) (V : WEnv GF) (Γ : DistView) (mid : w64)
    (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
      leaseClientAt cl lp ep V Γ mid ∗ ctxOk ci cd ∗ ctxErrClient ci cd }}
    (App (App (App (Val (lp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty @!!
        go!"TimeToLive")) (Val #(GoInterface.ok ci))) (Val #id)) (Val #slice.nil))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
      ((⌜err = GoInterface.nil⌝ ∗
          structFieldRef go_etcd_io.etcd.client.v3.LeaseTimeToLiveResponse go!"ID" resp ↦□ id) ∨
        ⌜err ≠ GoInterface.nil ∧ resp = null⌝) }}

end spec

end view
end etcd_dist
end EtcdGrove
end Perennial
