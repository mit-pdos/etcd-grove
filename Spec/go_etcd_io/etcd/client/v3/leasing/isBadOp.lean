/-
`isBadOp` (`cache.go`): a revision or a range end set. Changes: over W0's `opAt` (was `opFullAt`).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.Internal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Leasing

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

def isBadOp.spec : Prop :=
  ∀ (op : go_etcd_io.etcd.client.v3.Op) (o : OpM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ opAt op o }}
    (App (Val (@! go_etcd_io.etcd.client.v3.leasing.isBadOp)) (Val #op))
  {{ RET #(isBadOpM o); True }}

end spec

end Leasing
end EtcdGrove
end Perennial
