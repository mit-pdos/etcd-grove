module
public import Proof.go_etcd_io.bbolt.Init

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

/-- `b.Cursor()`, over what it touches: the bucket's `tx` field, and the transaction's `stats`
(the `CursorCount` statistic grows). A new cursor with an empty stack. -/
abbrev Bucket.Cursor.wspec : Prop :=
  ∀ (bl : Loc) (bv : Bucket) (dqb : DFrac) (st : TxStats),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ bl ↦{dqb} bv ∗
      structFieldRef Tx go!"stats" bv.tx' ↦ st }}
    (App (Val (bl @!! go.GoType.PointerType Bucket.ty @!! go!"Cursor")) (Val #()))
  {{ (cl : Loc) (s : GoSlice), RET #cl;
      cl ↦ ({ bucket' := bl, stack' := s } : Cursor) ∗ s ↦* ([] : List elemRef) ∗
      ownSliceCap elemRef s (DFrac.own 1) ∗ bl ↦{dqb} bv ∗
      structFieldRef Tx go!"stats" bv.tx' ↦ { st with CursorCount' := st.CursorCount' + W64 1 } }}

end spec

end bbolt
end EtcdGrove
end Perennial
