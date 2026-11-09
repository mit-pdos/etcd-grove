/-
## `(*Meta).SetTxid(x)` (`internal/common/meta.go`)

**Users.** db.go:702 (`init`). Snippet `ReqMetaRoundTrip`.
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

/-- `m.SetTxid(x)` writes the field `txid`. -/
def Meta.SetTxid.spec : Prop :=
  ∀ (l : Loc) (v : Meta) (x : Txid),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ l ↦ v }}
    (App (Val (l @!! go.GoType.PointerType Meta.ty @!! go!"SetTxid")) (Val #x))
  {{ RET #(); l ↦ ({ v with txid' := x } : Meta) }}

end spec

end BboltCommon
end EtcdGrove
end Perennial
