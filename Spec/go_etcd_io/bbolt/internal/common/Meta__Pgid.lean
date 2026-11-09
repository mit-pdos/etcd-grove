/-
## `(*Meta).Pgid()` (`internal/common/meta.go`)

**Users.** db.go:1257-1290 (`allocate`), db.go:1379 (`freepages`), tx.go:677 (`Page`), bucket.go. Snippet `ReqMetaRoundTrip`.
**Proof sketch.** one field load.
**Changes.** from `specs-ref`'s file of the same name (unchanged; a meta in a page is reached by `meta_view`).
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

/-- `m.Pgid()`: the field `pgid`. -/
def Meta.Pgid.spec : Prop :=
  ∀ (l : Loc) (v : Meta) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ l ↦{dq} v }}
    (App (Val (l @!! go.GoType.PointerType Meta.ty @!! go!"Pgid")) (Val #()))
  {{ RET #(v.pgid'); l ↦{dq} v }}

end spec

end BboltCommon
end EtcdGrove
end Perennial
