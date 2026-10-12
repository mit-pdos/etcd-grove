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

/-- `c.seek(key)` of a writer's cursor (its bucket `bl`, clean): the stack becomes a path from
the bucket's root down to a leaf (`wpath`), and the key returned is one the cursor can read
(`keySrcOK`). -/
abbrev Cursor.seek.wspec : Prop :=
  ∀ (cl : Loc) (cv : Cursor) (es : List elemRef) (W : WView) (hwm : Nat) (bl : Loc)
    (B : BRec) (txl : Loc) (pmap : GoMap) (pm : GMap w64 Loc) (dqp : DFrac)
    (key : GoSlice) (kb : List w8) (dk : DFrac),
  cv.bucket' = bl → wctxOK W hwm bl B txl pm →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ cl ↦ cv ∗ cv.stack' ↦* es ∗
      ownSliceCap elemRef cv.stack' (DFrac.own 1) ∗ wctx W bl B txl pmap pm dqp ∗ key ↦*{dk} kb }}
    (App (Val (cl @!! go.GoType.PointerType Cursor.ty @!! go!"seek")) (Val #key))
  {{ (cv' : Cursor) (path : List elemRef) (k v : GoSlice) (f : w32), RET (PairV (PairV #k #v) #f);
      ⌜cv'.bucket' = bl ∧ wpath W B B.ib.root' path ∧ keySrcOK W B k⌝ ∗
      cl ↦ cv' ∗ cv'.stack' ↦* path ∗ ownSliceCap elemRef cv'.stack' (DFrac.own 1) ∗
      wctx W bl B txl pmap pm dqp ∗ key ↦*{dk} kb }}

end spec

end bbolt
end EtcdGrove
end Perennial
