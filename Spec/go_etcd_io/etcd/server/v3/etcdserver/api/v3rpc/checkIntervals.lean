/-
`v3rpc.checkIntervals` (`server/etcdserver/api/v3rpc/`).

Users: `kvServer.Txn` (each branch), itself (nested transactions).

Proof sketch: the interval tree of the level's deletes (3f's `adt.IntervalTree`: `NewIntervalTree`, `Insert`, `Intersects`, `Union`), the recursive calls on nested transactions' branches, a fresh map of the puts; `ErrGRPCDuplicateKey` on a conflict.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/checkIntervals.lean`: the verdict as `intervalsOk` (opaque; its realization mirrors the code).

Margin: the returned puts and deletes are what the recursion needs (the realization's internal spec states them); the client-visible statement says only the verdict.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace V3rpc

open Iris Iris.BI EtcdModel EtcdWire ClientV3 Grpc Proto EtcdServer

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `checkIntervals(reqs)`: no error exactly when `intervalsOk`, else `ErrGRPCDuplicateKey`. The
operations are read and given back. -/
def checkIntervals.spec : Prop :=
  ∀ (sl : GoSlice) (dq : DFrac) (ops : List RequestOp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ msgsOwn requestOpOwn sl dq ops }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.checkIntervals)) (Val #sl))
  {{ (puts : Loc) (dels : GoInterface) (err : GoInterface), RET (PairV #puts (PairV #dels #err));
      msgsOwn requestOpOwn sl dq ops ∗
      (⌜err = GoInterface.nil ∧ intervalsOk ops⌝ ∨
       (⌜¬ intervalsOk ops⌝ ∗ statusErr err (Rpctypes.code .duplicateKey) (Rpctypes.desc .duplicateKey))) }}

end spec

end V3rpc
end EtcdGrove
end Perennial
