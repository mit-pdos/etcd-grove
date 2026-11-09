/-
`(*clientv3.Client).RequestProgress` (promoted from the embedded `Watcher`).

**Users**: the cache (`E cache/v3/progress_requestor.go:94` on `client.Watcher`), Kubernetes'
store (on its `*Client`). **Proof sketch**: `isClient_fields`, `watcherAt_methods`. **Changes**:
new. **Margin**: as `watcher.RequestProgress.spec`.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.ApiWatch

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

/-- `Client.RequestProgress` meets `Watcher.RequestProgressTriple`. -/
def Client.RequestProgress.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who : Principal),
  Watcher.RequestProgressTriple (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!! go!"RequestProgress")
    (iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isClient c γ who))

end spec

end ClientV3
end EtcdGrove
end Perennial
