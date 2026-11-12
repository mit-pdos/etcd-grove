/-
## `(*Meta).RootBucket()` (`internal/common/meta.go`)

**Users.** tx.go:58 (`init`: `*tx.meta.RootBucket()` copied), tx.go:213 (`Commit`: `RootBucket().SetRootPage(...)`).
**Proof sketch.** `&m.root`.
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

/-- `m.RootBucket()`: the address of the field `root` (Perennial's struct field access splits `l ↦ v` there). -/
def Meta.RootBucket.spec : Prop :=
  ∀ (l : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common }}
    (App (Val (l @!! go.GoType.PointerType Meta.ty @!! go!"RootBucket")) (Val #()))
  {{ RET #(structFieldRef Meta go!"root" l); True }}

end spec

end BboltCommon
end EtcdGrove
end Perennial
