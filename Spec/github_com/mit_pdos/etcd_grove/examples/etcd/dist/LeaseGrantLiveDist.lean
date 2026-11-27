/-
`(*lessor).Grant(ctx, ttl)` at a member, revocable lease mode, by a client of a member at another machine, at the cluster view (`notes/etcd-dist-plan.md` §18.4; an
interim trust-boundary axiom until #24's S2 client side: `Proof/.../etcd/dist/LeaseGrantLiveDist.lean`). Lean-first (no Rocq
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

/-- **`Lease_GrantLive_dist`: `(*lessor).Grant(ctx, ttl)` at member `mid`, revocable lease
mode** (mirrors `lessor.Grant.spec` at `etcdLeaseGrantSpecLive γl`, i.e. `etcdLeaseGrantSpecLiveW`;
clientv3's `Grant` sends `ID = 0`, the filter's request). After P-L1 only. Its premise `(∀ a b, Γ.ls a = Γ.ls b → a = b)`
(F2 axiom review, 2026-11-26, `notes/axiom-review/f2-lease-axioms.md`; ledger 2026-11-26): the members' lessor
names distinct, so that one member's lessor facts are not another's (`LeaseLeases` reads the member's own
lessor, with no read index); the view has no member set, so the premise is over every id. `DistView.ofKV`
(`ls := fun _ => 0`) fails it; P-L1 discharges it: the start allocates a distinct lessor name per member
(`ClusterNames.ls`) and `NewServer` makes that member's lessor at exactly that name. In monotone mode the member's
start must also run it with `lease.leasesNoExpiry` (`lease.runCfg _ .mono`, through `kvCongr`'s `lm`); a run
without it is outside every closed theorem. -/
abbrev Lease_GrantLive_dist.spec : Prop :=
  ∀ [π : NetProtoGS] (cl lp : Loc) (ep : GoString) (V : WEnv GF) (Γ : DistView) (mid : w64)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (ttl : w64),
  Γ.kv.lm = .revocable →
  -- (F2 axiom review, 2026-11-26) the members' lessor names distinct (see the docstring)
  (∀ a b : w64, Γ.ls a = Γ.ls b → a = b) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
      leaseClientAt cl lp ep V Γ mid ∗ ctxOk ctx cd ∗ ctxErrClient ctx cd }}
    (App (App (Val (lp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty @!! go!"Grant"))
      (Val #(GoInterface.ok ctx))) (Val #ttl))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ m : LeaseGrantRespM,
        structFieldRef go_etcd_io.etcd.client.v3.LeaseGrantResponse go!"ID" resp ↦□ m.id ∗
        structFieldRef go_etcd_io.etcd.client.v3.LeaseGrantResponse go!"TTL" resp ↦□ m.ttl ∗
        ⌜m.id ≠ W64 0⌝ ∗ ∃ (i : Nat) (l : Loc),
          lease.leaseLiveFrom (Γ.ls mid) i m.id l ∗ lease.leaseReqIs (Γ.ls mid) m.id ttl) ∨
      ⌜err ≠ GoInterface.nil ∧ resp = null⌝) }}

end spec

end view
end etcd_dist
end EtcdGrove
end Perennial
