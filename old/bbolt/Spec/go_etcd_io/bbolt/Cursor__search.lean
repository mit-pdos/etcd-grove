module
public import Proof.go_etcd_io.bbolt.CursorModel
public import Proof.go_etcd_io.bbolt.PageView

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

/-- `c.search(key, pgid)` on the read path: pushes the path from page `pgid` down to a leaf,
choosing at each branch one of its elements, and at the leaf the first element whose key is
not below `key` (`leafSeekAt`). -/
abbrev Cursor.search.spec : Prop :=
  ∀ (cl : Loc) (cv : Cursor) (es : List elemRef) (V : BktView) (q : Qp) (pid : w64)
    (key : GoSlice) (kb : List w8) (dk : DFrac),
  V.ok → V.wfAt pid →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ cl ↦ cv ∗ cv.stack' ↦* es ∗
      ownSliceCap elemRef cv.stack' (DFrac.own 1) ∗ bktCtx cv.bucket' V q ∗ bktPages V q ∗
      key ↦*{dk} kb }}
    (App (App (Val (cl @!! go.GoType.PointerType Cursor.ty @!! go!"search")) (Val #key)) (Val #pid))
  {{ (cv' : Cursor) (path : List elemRef) (pg : List w8) (idx : w64), RET #();
      ⌜cv'.bucket' = cv.bucket' ∧ stackOK V pid path ∧ stackLeaf V pid path pg idx ∧ leafOK pg ∧
        leafSeekAt pg kb idx⌝ ∗
      cl ↦ cv' ∗ cv'.stack' ↦* (es ++ path) ∗ ownSliceCap elemRef cv'.stack' (DFrac.own 1) ∗
      bktCtx cv.bucket' V q ∗ bktPages V q ∗ key ↦*{dk} kb }}

end spec

end bbolt
end EtcdGrove
end Perennial
