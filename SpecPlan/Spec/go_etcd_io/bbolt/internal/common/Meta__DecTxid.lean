/-
## `(*Meta).DecTxid()` (`internal/common/meta.go`)

**Users.** tx.go:451 (`writeMeta`: the other slot's meta).
**Proof sketch.** a load and a store (wrapping).
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

/-- `m.DecTxid()`: the txid minus one (wrapping). -/
def Meta.DecTxid.spec : Prop :=
  ∀ (l : Loc) (v : Meta),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ l ↦ v }}
    (App (Val (l @!! go.GoType.PointerType Meta.ty @!! go!"DecTxid")) (Val #()))
  {{ RET #(); l ↦ ({ v with txid' := v.txid' - W64 1 } : Meta) }}

end spec

end BboltCommon
end EtcdGrove
end Perennial
