module
public import Proof.go_etcd_io.bbolt.WriteCursorLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `c.search(key, pid)` of a writer's cursor (its bucket `bl`, clean): from position `pid`
down to a leaf, through the bucket's nodes and pages (`wpath`), each element at the index of
`key`; the stack grows by the path. -/
abbrev Cursor.search.wspec : Prop :=
  ∀ (cl : Loc) (cv : Cursor) (es : List elemRef) (W : WView) (hwm : Nat) (bl : Loc)
    (B : BRec) (txl : Loc) (pmap : GoMap) (pm : GMap w64 Loc) (dqp : DFrac) (pid : w64)
    (key : GoSlice) (kb : List w8) (dk : DFrac),
  cv.bucket' = bl → wctxOK W hwm bl B txl pm → posOK W hwm B pid →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ cl ↦ cv ∗ cv.stack' ↦* es ∗
      ownSliceCap elemRef cv.stack' (DFrac.own 1) ∗ wctx W bl B txl pmap pm dqp ∗ key ↦*{dk} kb }}
    (App (App (Val (cl @!! go.GoType.PointerType Cursor.ty @!! go!"search")) (Val #key)) (Val #pid))
  {{ (cv' : Cursor) (path : List elemRef), RET #();
      ⌜cv'.bucket' = bl ∧ wpath W B pid path⌝ ∗
      cl ↦ cv' ∗ cv'.stack' ↦* (es ++ path) ∗ ownSliceCap elemRef cv'.stack' (DFrac.own 1) ∗
      wctx W bl B txl pmap pm dqp ∗ key ↦*{dk} kb }}

end spec

end bbolt
end EtcdGrove
end Perennial
