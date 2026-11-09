/-
## `Pages.Swap(i, j)` (`internal/common/page.go`)

**Users.** tx.go:535.
**Proof sketch.** two loads, two stores.
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

/-- `s.Swap(i, j)`: pointers `i` and `j` exchanged. -/
def Pages.Swap.spec : Prop :=
  ∀ (s : GoSlice) (ps : List Loc) (i j : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ s ↦* ps ∗ ⌜sint.nat i < ps.length ∧ sint.nat j < ps.length ∧ 0 ≤ sint.Z i ∧ 0 ≤ sint.Z j⌝ }}
    (App (App (Val (s @!! go_etcd_io.bbolt.internal.common.Pages.ty @!! go!"Swap")) (Val #i)) (Val #j))
  {{ RET #(); s ↦* ((ps.set (sint.nat i) ps[sint.nat j]!).set (sint.nat j) ps[sint.nat i]!) }}

end spec

end BboltCommon
end EtcdGrove
end Perennial
