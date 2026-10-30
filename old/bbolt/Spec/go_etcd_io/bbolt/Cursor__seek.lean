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

/-- `c.seek(key)` on the read path: the stack becomes the path down to the leaf where `key`
belongs, at the first element whose key is not below `key` (`leafSeekAt`, past the end if
none); its key, value and flags (nil past the end). -/
abbrev Cursor.seek.spec : Prop :=
  ∀ (cl bl : Loc) (V : BktView) (q : Qp) (es : List elemRef) (key : GoSlice) (kb : List w8)
    (dk : DFrac),
  V.ok → V.wfAt V.root →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ curI cl bl V q es ∗ key ↦*{dk} kb }}
    (App (Val (cl @!! go.GoType.PointerType Cursor.ty @!! go!"seek")) (Val #key))
  {{ (es' : List elemRef) (r : elemRef) (pg : List w8),
      RET (PairV (PairV #(kvResult r.page' pg (sint.Z r.index')).1
        #(kvResult r.page' pg (sint.Z r.index')).2.1) #(kvResult r.page' pg (sint.Z r.index')).2.2);
      ⌜leafTop V es' r pg ∧ leafSeekAt pg kb r.index'⌝ ∗ curI cl bl V q es' ∗ key ↦*{dk} kb }}

end spec

end bbolt
end EtcdGrove
end Perennial
