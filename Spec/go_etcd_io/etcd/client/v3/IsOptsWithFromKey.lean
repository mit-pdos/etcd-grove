/-
`clientv3.IsOptsWithFromKey` (`client/v3/op.go`).

Users: `OpGet`, `OpDelete`; Kubernetes' store (`etcd3/store.go`: `IsOptsWithPrefix` of its own options).

Proof sketch: `NewOp.spec`, then each closure (`optAt_call`), the flag read.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/IsOptsWithFromKey.lean`: restated over this branch's vocabulary (the `OpM` model, `opAt`, `optsAt`); otherwise unchanged.

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

/-- `IsOptsWithFromKey(opts)`: the options applied to `NewOp()` set the flag. -/
def IsOptsWithFromKey.spec : Prop :=
  ∀ (sl : GoSlice) (gs : List (OpM → OpM)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ optsAt sl gs }}
    (App (Val (@! go_etcd_io.etcd.client.v3.IsOptsWithFromKey)) (Val #sl))
  {{ RET #(optsWithFromKey gs); optsAt sl gs }}

end spec

end ClientV3
end EtcdGrove
end Perennial
