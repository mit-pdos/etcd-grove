module
public import Spec.go_etcd_io.bbolt.Cursor__keyValue

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt

section defs
variable [ext : FfiSyntax]

/-- What `keyValue` returns of a leaf node's inodes `ins` at index `i`: nil past the end, else
the inode's key, value and flags. -/
def nodeKV (ins : List internal.common.Inode) (i : Int) : GoSlice × GoSlice × w32 :=
  if ins.length = 0 ∨ (ins.length : Int) ≤ i then (slice.nil, slice.nil, W32 0)
  else match ins[i.toNat]? with
    | some it => (it.key', it.value', it.flags')
    | none => (slice.nil, slice.nil, W32 0)

/-- What it returns of the top element `rv`: of its node (`nodeKV`) or its page (`kvResult`). -/
def kvResW (rv : elemRef) (pg : List w8) (ins : List internal.common.Inode) :
    GoSlice × GoSlice × w32 :=
  if rv.node' = null then kvResult rv.page' pg (sint.Z rv.index') else nodeKV ins (sint.Z rv.index')

end defs

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `c.keyValue()` of a writer's cursor, its top element a leaf node or a leaf page: the key,
value and flags of the element at its index (`kvResW`), nil past the end. -/
abbrev Cursor.keyValue.wspec : Prop :=
  ∀ (cl : Loc) (cv : Cursor) (dqc : DFrac) (es : List elemRef) (dqs : DFrac) (rv : elemRef)
    (q : DFrac) (pg : List w8) (nv : node) (dqn : DFrac) (ins : List internal.common.Inode)
    (dqi : DFrac),
  es.getLast? = some rv →
  (rv.node' = null → rv.page'.locCar ≠ 0 ∧ 16 ≤ pg.length ∧ pageFlags pg = leafPageFlag ∧
    leafWF pg pg.length ∧ (0 ≤ sint.Z rv.index' ∨ pageCount pg = 0)) →
  (rv.node' ≠ null → 0 ≤ sint.Z rv.index') →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ cl ↦{dqc} cv ∗ cv.stack' ↦*{dqs} es ∗
      (if rv.node' = null then bytesPointsto rv.page' q pg
       else iprop(rv.node' ↦{dqn} nv ∗ nv.inodes' ↦*{dqi} ins)) }}
    (App (Val (cl @!! go.GoType.PointerType Cursor.ty @!! go!"keyValue")) (Val #()))
  {{ RET (PairV (PairV #(kvResW rv pg ins).1 #(kvResW rv pg ins).2.1) #(kvResW rv pg ins).2.2);
      cl ↦{dqc} cv ∗ cv.stack' ↦*{dqs} es ∗
      (if rv.node' = null then bytesPointsto rv.page' q pg
       else iprop(rv.node' ↦{dqn} nv ∗ nv.inodes' ↦*{dqi} ins)) }}

end spec

end bbolt
end EtcdGrove
end Perennial
