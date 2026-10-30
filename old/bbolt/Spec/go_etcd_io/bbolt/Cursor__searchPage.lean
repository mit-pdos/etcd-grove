module
public import Proof.go_etcd_io.bbolt.CursorModel
public import Proof.go_etcd_io.bbolt.PageView
public import Spec.go_etcd_io.bbolt.Cursor__search

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

/-- `c.searchPage(key, p)` with the top of the stack a reference to the branch page `p` (page
`pid`, bytes `pg`), on the read path: its index becomes one of the page's elements and the
search goes on in that element's child. -/
abbrev Cursor.searchPage.spec : Prop :=
  ∀ (cl : Loc) (cv : Cursor) (es : List elemRef) (rv : elemRef) (V : BktView) (q : Qp)
    (pid : w64) (pg : List w8) (key : GoSlice) (kb : List w8) (dk : DFrac),
  V.ok → es.getLast? = some rv → rv.node' = null → V.pageAt pid = some (rv.page', pg) →
  pageFlags pg = branchPageFlag → branchWF pg pg.length V.hwm → 16 ≤ pg.length →
  (∀ i < pageCount pg, V.wfAt (W64 (branchPgid pg i))) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ cl ↦ cv ∗ cv.stack' ↦* es ∗
      ownSliceCap elemRef cv.stack' (DFrac.own 1) ∗ bktCtx cv.bucket' V q ∗ bktPages V q ∗
      key ↦*{dk} kb }}
    (App (App (Val (cl @!! go.GoType.PointerType Cursor.ty @!! go!"searchPage")) (Val #key))
      (Val #rv.page'))
  {{ (cv' : Cursor) (i : w64) (path : List elemRef) (lpg : List w8) (idx : w64), RET #();
      ⌜cv'.bucket' = cv.bucket' ∧ 0 ≤ sint.Z i ∧ sint.Z i < pageCount pg ∧
        stackOK V (W64 (branchPgid pg (sint.Z i).toNat)) path ∧
        stackLeaf V (W64 (branchPgid pg (sint.Z i).toNat)) path lpg idx ∧ leafOK lpg ∧
        leafSeekAt lpg kb idx⌝ ∗
      cl ↦ cv' ∗ cv'.stack' ↦* (es.set (es.length - 1) { rv with index' := i } ++ path) ∗
      ownSliceCap elemRef cv'.stack' (DFrac.own 1) ∗
      bktCtx cv.bucket' V q ∗ bktPages V q ∗ key ↦*{dk} kb }}

end spec

end bbolt
end EtcdGrove
end Perennial
