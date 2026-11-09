/-
`clientv3.WithCompactPhysical` (`client/v3/compact_op.go`).

Users: Kubernetes' compactor? no (it compacts without); `etcdctl compaction --physical`, the cache's tests.

Proof sketch: a closure setting `physical`.

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

/-- `WithCompactPhysical()`: an option that sets `physical`. -/
def WithCompactPhysical.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 }}
    (App (Val (@! go_etcd_io.etcd.client.v3.WithCompactPhysical)) (Val #()))
  {{ (f : GoFunc), RET #f; compactOptAt f (fun o => { o with physical := true }) }}

end spec

end ClientV3
end EtcdGrove
end Perennial
