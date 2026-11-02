module
public import Proof.go_etcd_io.bbolt.WriteTxClean

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

/-- `c.node()` of a writer's cursor whose stack is a path from the root of its (clean) bucket
down to a leaf: the leaf's node, the nodes on the path materialized (`Bucket.node`, `childAt`);
the bucket stays clean. -/
abbrev Cursor.node.spec : Prop :=
  ∀ (cl : Loc) (cv : Cursor) (path : List elemRef) (W : WView) (hwm : Nat) (bl : Loc)
    (B : BRec) (txl : Loc) (st : TxStats) (pmap : GoMap) (pm : GMap w64 Loc) (dqp : DFrac),
  cv.bucket' = bl → wctxOK W hwm bl B txl pm → wpath W B B.ib.root' path →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ cl ↦ cv ∗ cv.stack' ↦* path ∗
      wctx W bl B txl pmap pm dqp ∗ structFieldRef Tx go!"stats" txl ↦ st }}
    (App (Val (cl @!! go.GoType.PointerType Cursor.ty @!! go!"node")) (Val #()))
  {{ (l : Loc) (B' : BRec) (st' : TxStats), RET #l;
      cl ↦ cv ∗ cv.stack' ↦* path ∗ wctx W bl B' txl pmap pm dqp ∗
      structFieldRef Tx go!"stats" txl ↦ st' ∗
      ⌜bktClean W hwm bl B' ∧ bktGrows B B' ∧ ∃ r, B'.ns !! l = some r ∧ r.nv.isLeaf' = true⌝ }}

end spec

end bbolt
end EtcdGrove
end Perennial
