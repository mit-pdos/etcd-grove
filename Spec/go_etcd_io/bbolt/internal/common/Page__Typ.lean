/-
## `(*Page).Typ()` (`internal/common/page.go`)

**Users.** tx.go:697 (`Tx.Page`: the page's type name in its `PageInfo`); tx_check.go:173 and freelist `Read`'s panic message (paths their premises exclude).
**Proof sketch.** the four `Is*Page` specs; for unknown flags `fmt.Sprintf("unknown<%02x>", flags)` (`Spec/fmt`: returns some string).
**Changes.** new (round 1, S5: no old spec).
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

/-- `p.Typ()`: a name of the page's kind (some string: a debugging aid); it reads the header only. -/
def Page.Typ.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (bs : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ bytesPointsto p dq bs ∗ ⌜pageHeaderSize ≤ bs.length⌝ }}
    (App (Val (p @!! go.GoType.PointerType Page.ty @!! go!"Typ")) (Val #()))
  {{ (s : GoString), RET #s; bytesPointsto p dq bs }}

end spec

end BboltCommon
end EtcdGrove
end Perennial
