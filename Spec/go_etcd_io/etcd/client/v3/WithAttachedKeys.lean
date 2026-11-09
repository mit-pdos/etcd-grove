/-
`clientv3.WithAttachedKeys` (`client/v3/op.go`).

Users: `lessor.TimeToLive`'s callers (1c): `etcdctl lease timetolive --keys`, Kubernetes' lease manager.

Proof sketch: a closure setting `attachedKeys`.

Changes: none (no old spec): added for the users named above.

Margin: none.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ClientV3

open Iris Iris.BI EtcdModel EtcdWire
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `WithAttachedKeys()`: an option that asks for the attached keys. -/
def WithAttachedKeys.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 }}
    (App (Val (@! go_etcd_io.etcd.client.v3.WithAttachedKeys)) (Val #()))
  {{ (f : GoFunc), RET #f; leaseOptAt f (fun _ => true) }}

end spec

end ClientV3
end EtcdGrove
end Perennial
