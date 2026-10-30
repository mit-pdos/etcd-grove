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

/-- `c.last()` on the read path: from the top of the stack down to a leaf, pushing each
branch's last element (a leaf's index is its last element, `-1` if it is empty). -/
abbrev Cursor.last.spec : Prop :=
  ∀ (cl bl : Loc) (V : BktView) (q : Qp) (es : List elemRef) (pid : w64) (r : elemRef)
    (pg : List w8),
  V.ok → curPath V V.root es pid r pg →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ curI cl bl V q es }}
    (App (Val (cl @!! go.GoType.PointerType Cursor.ty @!! go!"last")) (Val #()))
  {{ (es' : List elemRef) (r' : elemRef) (pg' : List w8), RET #();
      ⌜leafTop V es' r' pg'⌝ ∗ curI cl bl V q es' }}

end spec

end bbolt
end EtcdGrove
end Perennial
