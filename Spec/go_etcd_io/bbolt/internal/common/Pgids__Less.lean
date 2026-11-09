/-
## `Pgids.Less(i, j)` (`internal/common/page.go`)

**Users.** as `Pgids.Len`.
**Proof sketch.** two loads.
**Changes.** new.
**Margin.** none: the post is what the code computes.
-/
module

public import Spec.go_etcd_io.bbolt.internal.common.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace BboltCommon

open Iris Iris.BI go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

/-- `s.Less(i, j)`: whether id `i` is below id `j` (unsigned). -/
def Pgids.Less.spec : Prop :=
  ∀ (s : GoSlice) (xs : List Pgid) (dq : DFrac) (i j : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ s ↦*{dq} xs ∗ ⌜sint.nat i < xs.length ∧ sint.nat j < xs.length ∧ 0 ≤ sint.Z i ∧ 0 ≤ sint.Z j⌝ }}
    (App (App (Val (s @!! go_etcd_io.bbolt.internal.common.Pgids.ty @!! go!"Less")) (Val #i)) (Val #j))
  {{ RET #(decide (uint.Z xs[sint.nat i]! < uint.Z xs[sint.nat j]!)); s ↦*{dq} xs }}

end spec

end BboltCommon
end EtcdGrove
end Perennial
