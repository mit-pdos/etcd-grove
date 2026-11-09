/-
## `(*Meta).Validate()` (`internal/common/meta.go`)

**Users.** db.go:396,436 (`getPageSize`: `== nil` picks the page size), db.go:585-586 (`mmap`: both invalid is an error returned by `Open`), db.go:1226,1228 (`meta()`: the valid one with the higher txid). Snippet `ReqMetaRoundTrip`.
**Proof sketch.** magic, version, `Sum64`; the error values are `bbolt/errors`' package variables, non-nil by its `init` (`req/go_etcd_io_bbolt_errors.md`).
**Changes.** from `specs-ref`'s file of the same name: the error named (`metaErr`), and non-nil, which `Open`'s callers inspect.
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

/-- `m.Validate()`: `nil` exactly for a valid meta; otherwise the value of the `bbolt/errors` variable `metaErr` names (`ErrInvalid`, `ErrVersionMismatch`, `ErrChecksum`), not `nil`. -/
def Meta.Validate.spec : Prop :=
  ∀ (l : Loc) (v : Meta) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ l ↦{dq} v ∗ ⌜0 < l.addr⌝ }}
    (App (Val (l @!! go.GoType.PointerType Meta.ty @!! go!"Validate")) (Val #()))
  {{ (err : GoInterface), RET #err; l ↦{dq} v ∗
      (⌜metaErr v = none ∧ err = GoInterface.nil⌝ ∨
        ∃ g, ⌜metaErr v = some g ∧ err ≠ GoInterface.nil⌝ ∗ globalAddr g ↦□ err) }}

end spec

end BboltCommon
end EtcdGrove
end Perennial
