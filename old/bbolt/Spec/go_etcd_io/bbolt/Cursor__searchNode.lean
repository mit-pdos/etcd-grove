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

/-- `c.searchNode(key, n)` of a writer's cursor, its top element the branch node `nl`: the top
element gets the index of the child to search (the last entry not above `key`), which is
searched. -/
abbrev Cursor.searchNode.spec : Prop :=
  ∀ (cl : Loc) (cv : Cursor) (es : List elemRef) (rv : elemRef) (W : WView) (hwm : Nat)
    (bl : Loc) (B : BRec) (txl : Loc) (pmap : GoMap) (pm : GMap w64 Loc) (dqp : DFrac)
    (nl : Loc) (r : NRec) (key : GoSlice) (kb : List w8) (dk : DFrac),
  cv.bucket' = bl → wctxOK W hwm bl B txl pm → es.getLast? = some rv → rv.node' = nl →
  B.ns !! nl = some r → r.nv.isLeaf' = false →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ cl ↦ cv ∗ cv.stack' ↦* es ∗
      ownSliceCap elemRef cv.stack' (DFrac.own 1) ∗ wctx W bl B txl pmap pm dqp ∗ key ↦*{dk} kb }}
    (App (App (Val (cl @!! go.GoType.PointerType Cursor.ty @!! go!"searchNode")) (Val #key))
      (Val #nl))
  {{ (cv' : Cursor) (i : w64) (path : List elemRef) (w : WEntry), RET #();
      ⌜cv'.bucket' = bl ∧ 0 ≤ sint.Z i ∧ r.ws[(sint.Z i).toNat]? = some w ∧
        wpath W B w.pgid path⌝ ∗
      cl ↦ cv' ∗ cv'.stack' ↦* (es.set (es.length - 1) { rv with index' := i } ++ path) ∗
      ownSliceCap elemRef cv'.stack' (DFrac.own 1) ∗ wctx W bl B txl pmap pm dqp ∗ key ↦*{dk} kb }}

end spec

end bbolt
end EtcdGrove
end Perennial
