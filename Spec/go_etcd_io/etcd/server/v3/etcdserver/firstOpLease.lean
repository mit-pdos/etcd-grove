/-
## `firstOpLease(ops)` (`tracing.go:67-74`)

**Users.** `EtcdServer.Txn`'s trace (2c).

**Proof sketch.** As `firstOpKey`. **Changes**: from `specs-ref`'s `firstOpLease.lean`.
**Margin.** Exact.
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

/-- **`firstOpLease(ops)`**: the lease of the first put, or `-1`. -/
def firstOpLease.spec : Prop :=
  ∀ (sl : GoSlice) (dq : DFrac) (ops : List RequestOp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ EtcdWire.msgsOwn EtcdWire.requestOpOwn sl dq ops }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.firstOpLease)) (Val #sl))
  {{ RET #(W64 (((ops.filterMap (fun o => match o with
          | .put p => some p.lease | _ => none)).head?).getD (-1)));
      EtcdWire.msgsOwn EtcdWire.requestOpOwn sl dq ops }}

end spec

end EtcdServer
end EtcdGrove
end Perennial
