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

/-- `c.Bucket()`: the cursor's bucket. -/
abbrev Cursor.Bucket.spec : Prop :=
  ∀ (cl : Loc) (cv : Cursor) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ cl ↦{dq} cv }}
    (App (Val (cl @!! go.GoType.PointerType Cursor.ty @!! go!"Bucket")) (Val #()))
  {{ RET #cv.bucket'; cl ↦{dq} cv }}

end spec

end bbolt
end EtcdGrove
end Perennial
