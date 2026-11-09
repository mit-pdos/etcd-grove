/-
`clientv3.withTop` (`client/v3/op.go`).

Users: `WithFirstCreate`, ..., `WithLastRev`.

Proof sketch: `WithPrefix.spec`, `WithSort.spec`, `WithLimit.spec`, a slice literal.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/withTop.lean`: restated over this branch's vocabulary (the `OpM` model, `opAt`, `optsAt`); otherwise unchanged.

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

/-- `withTop(target, order)`: three options. -/
def withTop.spec : Prop :=
  ∀ (target order : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.withTop)) (Val #target)) (Val #order))
  {{ (sl : GoSlice), RET #sl; optsAt sl (withTopM target order) }}

end spec

end ClientV3
end EtcdGrove
end Perennial
