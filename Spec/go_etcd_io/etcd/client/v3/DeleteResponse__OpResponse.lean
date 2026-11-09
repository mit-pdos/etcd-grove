/-
`(*clientv3.DeleteResponse).OpResponse` (`client/v3/kv.go`).

Users: leasing (`leasing/kv.go`, `leasing/txn.go`: its replies as `OpResponse`s).

Proof sketch: a struct literal.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/DeleteResponse__OpResponse.lean`: restated over this branch's vocabulary (the `OpM` model, `opAt`, `optsAt`); otherwise unchanged.

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

/-- `resp.OpResponse()`: an `OpResponse` holding `resp` alone. -/
def DeleteResponse.OpResponse.spec : Prop :=
  ∀ (resp : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 }}
    (App (Val (resp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.DeleteResponse.ty @!! go!"OpResponse")) (Val #()))
  {{ RET #(go_etcd_io.etcd.client.v3.OpResponse.mk null null resp null); True }}

end spec

end ClientV3
end EtcdGrove
end Perennial
