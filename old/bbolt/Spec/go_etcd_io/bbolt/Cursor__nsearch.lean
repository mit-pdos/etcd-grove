module
public import Proof.go_etcd_io.bbolt.Init
public import Proof.go_etcd_io.bbolt.PageView
public import Proof.go_etcd_io.bbolt.KeyOrder

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

/-- `c.nsearch(key)` with the top of the stack a reference to a leaf page (the read path): the
top's index becomes the first element whose key is not below `key` (`count` if none): the keys
increase, so the binary search finds it. -/
abbrev Cursor.nsearch.spec : Prop :=
  ∀ (cl : Loc) (cv : Cursor) (dqc : DFrac) (es : List elemRef) (rv : elemRef) (q : DFrac)
    (pg : List w8) (key : GoSlice) (kb : List w8) (dk : DFrac),
  es.getLast? = some rv → rv.node' = null → rv.page'.locCar ≠ 0 → 16 ≤ pg.length →
  pageFlags pg = leafPageFlag → leafWF pg pg.length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ cl ↦{dqc} cv ∗ cv.stack' ↦* es ∗ bytesPointsto rv.page' q pg ∗ key ↦*{dk} kb }}
    (App (Val (cl @!! go.GoType.PointerType Cursor.ty @!! go!"nsearch")) (Val #key))
  {{ (idx : w64), RET #();
      ⌜0 ≤ sint.Z idx ∧ sint.Z idx ≤ pageCount pg ∧
        (∀ k, 0 ≤ k → k < sint.Z idx → leafGE pg kb k = false) ∧
        (sint.Z idx < pageCount pg → leafGE pg kb (sint.Z idx) = true)⌝ ∗
      cl ↦{dqc} cv ∗ cv.stack' ↦* es.set (es.length - 1) { rv with index' := idx } ∗
      bytesPointsto rv.page' q pg ∗ key ↦*{dk} kb }}

end spec

end bbolt
end EtcdGrove
end Perennial
