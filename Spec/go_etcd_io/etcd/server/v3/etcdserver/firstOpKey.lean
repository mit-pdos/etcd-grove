/-
## `firstOpKey(ops)` (`tracing.go:31-47`)

**Users.** `EtcdServer.Txn`'s trace (2c).

**Proof sketch.** A loop over the operations (`EtcdWire.msgsOwn requestOpOwn`), the oneof's type
switch. **Changes**: from `specs-ref`'s `firstOpKey.lean`. **Margin.** Exact.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiBoot
public import Spec.go_etcd_io.etcd.api.v3.Wire

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

/-- **`firstOpKey(ops)`**: the first non-empty key of a put, range or delete, or `""`. -/
def firstOpKey.spec : Prop :=
  ∀ (sl : GoSlice) (dq : DFrac) (ops : List RequestOp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ EtcdWire.msgsOwn EtcdWire.requestOpOwn sl dq ops }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.firstOpKey)) (Val #sl))
  {{ RET #(((ops.map (fun o => match o with
          | .put p => p.key | .range r => r.key | .deleteRange d => d.key | _ => [])).find?
          (fun k => decide (k ≠ []))).getD []);
      EtcdWire.msgsOwn EtcdWire.requestOpOwn sl dq ops }}

end spec

end EtcdServer
end EtcdGrove
end Perennial
