/-
`clientv3.RetryClusterClient(c)` (`client/v3/retry.go`: `&retryClusterClient{cc:
pb.NewClusterClient(c.conn)}`). Lean-first (axiom-triage, 2026-11-18: `NewCluster` calls it).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvClientNew

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

/-- `RetryClusterClient(c)` on a `*Client` whose connection is `conn` (read-only) returns. -/
abbrev RetryClusterClient.spec : Prop :=
  ∀ (cl conn : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      structFieldRef go_etcd_io.etcd.client.v3.Client go!"conn" cl ↦□ conn }}
    (App (Val (@! go_etcd_io.etcd.client.v3.RetryClusterClient)) (Val #cl))
  {{ (v : GoInterface), RET #v; True }}

end spec

end EtcdGrove
end Perennial
