/-
`gatherOps` (`util.go`): the operations with each transaction replaced by its branches', at any
depth (`gatherL`); `append(thenOps, elseOps...)` writes no caller memory as the nested branch slices
have no spare capacity (`opsCapOk`; `nonissues/leasing-gatherops-spare-capacity.md`). Changes: the
old spec took the capacities owned (`opTAtC`).
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.leasing.Internal

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

/-- `gatherOps(ops)`. -/
def gatherOps.spec : Prop :=
  ∀ (ops : GoSlice) (os : List OpM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ opsAt ops os ∗ opsCapOk ops }}
    (App (Val (@! go_etcd_io.etcd.client.v3.leasing.gatherOps)) (Val #ops))
  {{ (ret : GoSlice), RET #ret; opsAt ret (gatherL os) ∗ opsCapOk ret }}

end spec

end Leasing
end EtcdGrove
end Perennial
