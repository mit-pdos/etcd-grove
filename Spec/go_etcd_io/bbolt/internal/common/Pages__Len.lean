/-
## `Pages.Len()` (`internal/common/page.go`)

**Users.** tx.go:535 (`Tx.write`: `sort.Sort(pages)`).
**Proof sketch.** `len(s)`.
**Changes.** new (no old spec).
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

/-- `s.Len()`: the slice's length. -/
def Pages.Len.spec : Prop :=
  ∀ (s : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common }}
    (App (Val (s @!! go_etcd_io.bbolt.internal.common.Pages.ty @!! go!"Len")) (Val #()))
  {{ RET #(s.len); True }}

end spec

end BboltCommon
end EtcdGrove
end Perennial
