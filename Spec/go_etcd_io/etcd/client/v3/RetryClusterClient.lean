/-
`clientv3.RetryClusterClient` (`client/v3/retry.go`, translated 2026-11-22 for `NewCluster`).
Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvAuthConn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `RetryClusterClient(c)` on a `*Client` whose connection is `conn` (read-only): a new
`*retryClusterClient` (over the generated stub on `conn`), as a `ClusterClient`. -/
abbrev RetryClusterClient.spec : Prop :=
  ∀ (cl conn : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      structFieldRef go_etcd_io.etcd.client.v3.Client go!"conn" cl ↦□ conn }}
    (App (Val (@! go_etcd_io.etcd.client.v3.RetryClusterClient)) (Val #cl))
  {{ (v : GoInterface), RET #v; ∃ r : Loc,
      ⌜v = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.retryClusterClient.ty) #r⌝ }}

end spec

end EtcdGrove
end Perennial
