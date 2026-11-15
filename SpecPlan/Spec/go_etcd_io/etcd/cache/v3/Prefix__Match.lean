/-
`Prefix.Match` (`cache/*.go`).
Users: no caller in the cache (exported; kept: verified before).
Proof sketch: string comparison of the slice's prefix.
Changes: unchanged.
Margin: none known.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.cache.v3.Api

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

/-- `Prefix(pfx).Match(key)`: whether `pfx` is a prefix of `key`. -/
def Prefix.Match.spec : Prop :=
  ∀ (pfx : GoString) (sl : GoSlice) (key : GoString) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ sl ↦*{dq} key }}
    (App (Val (pfx @!! go_etcd_io.etcd.cache.v3.Prefix.ty @!! go!"Match")) (Val #sl))
  {{ RET #(decide (pfx <+: key)); sl ↦*{dq} key }}

end spec

end Cache
end EtcdGrove
end Perennial
