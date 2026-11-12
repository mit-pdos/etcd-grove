/-
`isPrefixScan` (`cache/*.go`), an internal helper.
Users: `snapshot.Range`.
Proof sketch: the slice's length and first byte.
Changes: unchanged.
Margin: none known.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.cache.v3.Internal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Cache

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `isPrefixScan(end)`: whether `end` is `"\x00"` (a from-key range). -/
def isPrefixScan.spec : Prop :=
  ∀ (sl : GoSlice) (key : GoString) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ sl ↦*{dq} key }}
    (App (Val (@! go_etcd_io.etcd.cache.v3.isPrefixScan)) (Val #sl))
  {{ RET #(decide (key = [W8 0])); sl ↦*{dq} key }}

end spec

end Cache
end EtcdGrove
end Perennial
