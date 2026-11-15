/-
`(clientv3.retryPolicy).String` (`client/v3/retry.go`).

Users: the retry interceptor's logging (1c).

Proof sketch: a `switch`.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/retryPolicy__String.lean`: restated over this branch's vocabulary (the `OpM` model, `opAt`, `optsAt`); otherwise unchanged.

Margin: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.Api

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

/-- `rp.String()`: the policy's name. -/
def retryPolicy.String.spec : Prop :=
  ∀ (rp : w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 }}
    (App (Val (rp @!! go_etcd_io.etcd.client.v3.retryPolicy.ty @!! go!"String")) (Val #()))
  {{ RET #(if rp = W8 0 then go!"repeatable" else if rp = W8 1 then go!"nonRepeatable"
           else go!"UNKNOWN"); True }}

end spec

end ClientV3
end EtcdGrove
end Perennial
