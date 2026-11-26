/-
`gone(cli, id)` (`examples/etcd/dist/client/lease.go`; leaseexpiryN's, copied, but a listing's error does
not end the polling): polls `cli`'s member's listing until it does not list `id`. The triple, in revocable
lease mode, for a client of member `mid` of the view and a lower bound `m` of its lessor's history: if it
returns `true`, the lease `id` is absent from that history at an index no earlier than `m`
(`leaseAbsentFrom`, leaseexpiryN's `gone.spec` at the member's lessor name `Γ.ls mid`).
Lean-first (no Rocq counterpart); #50 N9b (`notes/etcd-dist-n9b.md`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.LeaseDefs
public import Proof.go_etcd_io.etcd.client.v3.InvClientNew

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Net client
open github_com.mit_pdos.etcd_grove.examples.etcd.dist
open etcd_dist etcd_dist.view

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [esrv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- See the file header. -/
abbrev gone.spec : Prop :=
  ∀ [π : NetProtoGS] (cl : Loc) (ep : GoString) (V : WEnv GF) (Γ : DistView) (mid : w64) (m : Nat)
    (id : w64),
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  Γ.kv.lm = .revocable →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client ∗
      levelTok 0 ∗ memberCli cl ep V Γ mid ∗ lease.lessorLb (Γ.ls mid) m }}
    (App (App (Val (@! client.gone)) (Val #cl)) (Val #id))
  {{ (b : Bool), RET #b; levelTok 0 ∗ (if b then lease.leaseAbsentFrom (Γ.ls mid) m id else True) }}

end spec

end etcd_dist_client
end EtcdGrove
end Perennial
