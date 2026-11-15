/-
`kubernetes.kvFromTxnResponse` (`client/v3/kubernetes/client.go`).

Users: `OptimisticPut`, `OptimisticDelete` (the failure branch's get).

Proof sketch: `resp.GetResponseRange()` (3h's getter over `responseOpOwn`: the range message, which
the premise says it is: on another kind it is `nil` and `.Kvs` panics), the one key-value or `nil`.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/kubernetes/kvFromTxnResponse.lean`.

Margin: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.kubernetes.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Kubernetes

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.kubernetes.Assumptions]

/-- `kvFromTxnResponse(p)` of a range response: its one key-value, or `nil`. -/
def kvFromTxnResponse.spec : Prop :=
  ∀ (p : Loc) (m : RangeRespM) (rev : Nat) (a : RangeAns),
  ResponseOpM.ofResp (.range m) (.range rev a) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.kubernetes ∗ responseOpOwn p (DFrac.own 1) (.range m) }}
    (App (Val (@! go_etcd_io.etcd.client.v3.kubernetes.kvFromTxnResponse)) (Val #p))
  {{ (kv : Loc), RET #kv; singleKV a kv }}

end spec

end Kubernetes
end EtcdGrove
end Perennial
