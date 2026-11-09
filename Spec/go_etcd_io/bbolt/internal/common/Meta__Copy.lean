/-
## `(*Meta).Copy(dest)` (`internal/common/meta.go`)

**Users.** tx.go:53 (`Tx.init`: `db.meta().Copy(tx.meta)`, from the mmap's meta to the heap); `Meta.Write`. Snippet `ReqMetaRoundTrip`.
**Proof sketch.** a whole-struct load into a local and a store.
**Changes.** from `specs-ref`'s file of the same name (unchanged; separate points-tos, as the fork copies through a local).
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

/-- `m.Copy(dest)`: `*dest` becomes `*m`. -/
def Meta.Copy.spec : Prop :=
  ∀ (l dest : Loc) (v w : Meta) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ l ↦{dq} v ∗ dest ↦ w }}
    (App (Val (l @!! go.GoType.PointerType Meta.ty @!! go!"Copy")) (Val #dest))
  {{ RET #(); l ↦{dq} v ∗ dest ↦ v }}

end spec

end BboltCommon
end EtcdGrove
end Perennial
