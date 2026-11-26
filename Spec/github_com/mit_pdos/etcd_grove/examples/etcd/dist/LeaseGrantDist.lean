/-
`(*lessor).Grant(ctx, ttl)` at a member, monotone lease mode, by a client of a member at another machine, at the cluster view (`notes/etcd-dist-plan.md` §18.4; an
interim trust-boundary axiom until #24's S2 client side: `Proof/.../etcd/dist/LeaseGrantDist.lean`). Lean-first (no Rocq
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

/-- **`Lease_Grant_dist`: `(*lessor).Grant(ctx, ttl)` at member `mid`, monotone lease mode**
(mirrors `lessor.Grant.spec` at `etcdLeaseGrantSpec γl`, i.e. `etcdLeaseGrantSpecW`, `γl := Γ.ls mid`;
`etcdReached` dropped: no workload reads it). Reads the lessor name: an axiom only after P-L1. -/
abbrev Lease_Grant_dist.spec : Prop :=
  ∀ [π : NetProtoGS] (cl lp : Loc) (ep : GoString) (V : WEnv GF) (Γ : DistView) (mid : w64)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (ttl : w64),
  Γ.kv.lm = .mono →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
      leaseClientAt cl lp ep V Γ mid ∗ ctxOk ctx cd ∗ ctxErrClient ctx cd }}
    (App (App (Val (lp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty @!! go!"Grant"))
      (Val #(GoInterface.ok ctx))) (Val #ttl))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ m : LeaseGrantRespM,
        structFieldRef go_etcd_io.etcd.client.v3.LeaseGrantResponse go!"ID" resp ↦□ m.id ∗
        structFieldRef go_etcd_io.etcd.client.v3.LeaseGrantResponse go!"TTL" resp ↦□ m.ttl ∗
        ⌜m.id ≠ W64 0⌝ ∗ ∃ i : Nat, lease.leaseGrantedAt (Γ.ls mid) i m.id) ∨
      ⌜err ≠ GoInterface.nil ∧ resp = null⌝) }}

end spec

end view
end etcd_dist
end EtcdGrove
end Perennial
