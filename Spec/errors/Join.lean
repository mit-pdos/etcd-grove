/-
`errors.Join(errs...)` of errors that are trees of `status` errors and joins
(`joinedStatusErrOk`, `Proof/errors/JoinedStatusErr.lean`): etcd#19935's `watcher.Close` joins
the errors of its streams' `close`. The trust boundary: `errors.Join` is not translated (Perennial
translates `errors`'s names only for `join.go`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.errors.JoinedStatusErr

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.errors.Assumptions]

/-- `errors.Join(errs...)` (Go's `errors/join.go`), with every element of `errs` a tree of
`status` errors and joins, returns `nil` exactly when every element is `nil`, and otherwise a
`*joinError` holding the non-`nil` elements, again such a tree (the union of the elements' trees
and the new node, whose `Unwrap() []error` returns those elements and which has no `Is` or `As`
method); it only reads the slice. -/
abbrev errors.Join.spec : Prop :=
  ∀ (errs : GoSlice) (es : List GoInterface) (dq : DFrac),
    {{ isPkgInit (PROP := IProp GF) pkg_id.errors ∗ errs ↦*{dq} es ∗
        [∗list] _k ↦ e ∈ es, joinedStatusErrOk (GF := GF) e }}
      (App (Val #(functions _root_.Perennial.errors.Join [])) (Val #errs))
    {{ (err : GoInterface), RET #err; errs ↦*{dq} es ∗
        ⌜err = GoInterface.nil ↔ ∀ e ∈ es, e = GoInterface.nil⌝ ∗ joinedStatusErrOk (GF := GF) err }}

end spec

end EtcdGrove
end Perennial
