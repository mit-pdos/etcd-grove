/-
`(*lessor).Leases(ctx)` at a member, monotone lease mode, by a client of a member at another machine, at the cluster view (`notes/etcd-dist-plan.md` §18.4; an
interim trust-boundary axiom until #24's S2 client side: `Proof/.../etcd/dist/LeaseLeasesGrantedDist.lean`). Lean-first (no Rocq
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

/-- **`Lease_LeasesGranted_dist`: `(*lessor).Leases(ctx)` at member `mid`, monotone mode**
(mirrors `lessor.Leases.spec` at `etcdLeaseLeasesSpec γl`, i.e. `etcdLeaseLeasesSpecW`): the caller's
grants `G` at this member's lessor are all listed, no id twice. After P-L1 only. -/
abbrev Lease_LeasesGranted_dist.spec : Prop :=
  ∀ [π : NetProtoGS] (cl lp : Loc) (ep : GoString) (V : WEnv GF) (Γ : DistView) (mid : w64)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (G : List w64),
  Γ.kv.lm = .mono →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
      leaseClientAt cl lp ep V Γ mid ∗ ctxOk ctx cd ∗ ctxErrClient ctx cd ∗
      [∗list] id ∈ G, ∃ i : Nat, lease.leaseGrantedAt (Γ.ls mid) i id }}
    (App (Val (lp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty @!! go!"Leases"))
      (Val #(GoInterface.ok ctx)))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (ids : List w64) (sl : GoSlice),
          structFieldRef go_etcd_io.etcd.client.v3.LeaseLeasesResponse go!"Leases" resp ↦□ sl ∗
          sl ↦* (ids.map (fun id => (go_etcd_io.etcd.client.v3.LeaseStatus.mk id))) ∗
          ⌜ids.Nodup ∧ ∀ id ∈ G, id ∈ ids⌝) ∨
        ⌜err ≠ GoInterface.nil ∧ resp = null⌝) }}

end spec

end view
end etcd_dist
end EtcdGrove
end Perennial
