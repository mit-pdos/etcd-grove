/-
## `firstCompareKey(c)` (`tracing.go:20-28`)

**Users.** `EtcdServer.Txn`'s trace (2c).

**Proof sketch.** A loop over the compares' pointers (`EtcdWire.msgsOwn compareOwn`, read at any
fraction), `GetKey`. **Changes**: from `specs-ref`'s `firstCompareKey.lean`. **Margin.** Exact.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiBoot
public import SpecPlan.Spec.go_etcd_io.etcd.api.v3.Wire

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI EtcdModel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`firstCompareKey(cs)`**: the first non-empty key of the compares, or `""`. -/
def firstCompareKey.spec : Prop :=
  ∀ (sl : GoSlice) (dq : DFrac) (cs : List Compare),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ EtcdWire.msgsOwn EtcdWire.compareOwn sl dq cs }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.firstCompareKey)) (Val #sl))
  {{ RET #(((cs.map (·.key)).find? (fun k => decide (k ≠ []))).getD []);
      EtcdWire.msgsOwn EtcdWire.compareOwn sl dq cs }}

end spec

end EtcdServer
end EtcdGrove
end Perennial
