/-
`clientv3.FromCompare` (`client/v3/compare.go`).

Users: the gRPC proxy and leasing (comparisons from a `TxnRequest`).

Proof sketch: `cloneCompare.spec`.

Changes: none (no old spec): added for the users named above.

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

/-- `FromCompare(c)`: a `Cmp` of a copy of the message (a zero `Cmp` for `nil`). -/
def FromCompare.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (m : Option EtcdModel.Compare),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ optOwn compareOwn p dq m }}
    (App (Val (@! go_etcd_io.etcd.client.v3.FromCompare)) (Val #p))
  {{ (c : go_etcd_io.etcd.client.v3.Cmp), RET #c; optOwn compareOwn p dq m ∗ cmpAt c m }}

end spec

end ClientV3
end EtcdGrove
end Perennial
