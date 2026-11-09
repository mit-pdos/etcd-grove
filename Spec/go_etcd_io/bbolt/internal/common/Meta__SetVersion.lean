/-
## `(*Meta).SetVersion(x)` (`internal/common/meta.go`)

**Users.** db.go:697 (`init`). Snippet `ReqMetaRoundTrip`.
**Proof sketch.** one field store.
**Changes.** from `specs-ref`'s file of the same name (unchanged).
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

/-- `m.SetVersion(x)` writes the field `version`. -/
def Meta.SetVersion.spec : Prop :=
  ∀ (l : Loc) (v : Meta) (x : w32),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ l ↦ v }}
    (App (Val (l @!! go.GoType.PointerType Meta.ty @!! go!"SetVersion")) (Val #x))
  {{ RET #(); l ↦ ({ v with version' := x } : Meta) }}

end spec

end BboltCommon
end EtcdGrove
end Perennial
