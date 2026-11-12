/-
## `(*Meta).SetPgid(x)` (`internal/common/meta.go`)

**Users.** db.go:701 (`init`), db.go:1290 (`allocate`). Snippet `ReqMetaRoundTrip`.
**Proof sketch.** one field store.
**Changes.** from `specs-ref`'s file of the same name (unchanged).
**Margin.** none: the post is what the code computes.
-/
module

public import SpecPlan.Spec.go_etcd_io.bbolt.internal.common.Api

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

/-- `m.SetPgid(x)` writes the field `pgid`. -/
def Meta.SetPgid.spec : Prop :=
  ∀ (l : Loc) (v : Meta) (x : Pgid),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ l ↦ v }}
    (App (Val (l @!! go.GoType.PointerType Meta.ty @!! go!"SetPgid")) (Val #x))
  {{ RET #(); l ↦ ({ v with pgid' := x } : Meta) }}

end spec

end BboltCommon
end EtcdGrove
end Perennial
