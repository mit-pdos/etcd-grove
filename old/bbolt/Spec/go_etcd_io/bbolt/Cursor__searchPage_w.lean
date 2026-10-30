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

/-- `c.searchPage(key, p)` of a writer's cursor, its top element the branch page `p` (page
`pid` of the view): the top element gets the index of the child to search, which is searched. -/
abbrev Cursor.searchPage.wspec : Prop :=
  ∀ (cl : Loc) (cv : Cursor) (es : List elemRef) (rv : elemRef) (W : WView) (hwm : Nat)
    (bl : Loc) (B : BRec) (txl : Loc) (pmap : GoMap) (pm : GMap w64 Loc) (dqp : DFrac)
    (pid : w64) (pg : List w8) (key : GoSlice) (kb : List w8) (dk : DFrac),
  cv.bucket' = bl → wctxOK W hwm bl B txl pm → es.getLast? = some rv → rv.node' = null →
  B.ib.root' ≠ W64 0 → W.pages !! uint.nat pid = some pg →
  rv.page' = W.data +ₗ ((uint.nat pid * W.ps : Nat) : Int) →
  pageFlags pg = branchPageFlag → branchWF pg pg.length hwm → 16 ≤ pg.length →
  (∀ i < pageCount pg, posOK W hwm B (W64 (branchPgid pg i : Int))) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ cl ↦ cv ∗ cv.stack' ↦* es ∗
      ownSliceCap elemRef cv.stack' (DFrac.own 1) ∗ wctx W bl B txl pmap pm dqp ∗ key ↦*{dk} kb }}
    (App (App (Val (cl @!! go.GoType.PointerType Cursor.ty @!! go!"searchPage")) (Val #key))
      (Val #rv.page'))
  {{ (cv' : Cursor) (i : w64) (path : List elemRef), RET #();
      ⌜cv'.bucket' = bl ∧ 0 ≤ sint.Z i ∧ sint.Z i < pageCount pg ∧
        wpath W B (W64 (branchPgid pg (sint.Z i).toNat : Int)) path⌝ ∗
      cl ↦ cv' ∗ cv'.stack' ↦* (es.set (es.length - 1) { rv with index' := i } ++ path) ∗
      ownSliceCap elemRef cv'.stack' (DFrac.own 1) ∗ wctx W bl B txl pmap pm dqp ∗ key ↦*{dk} kb }}

end spec

end bbolt
end EtcdGrove
end Perennial
