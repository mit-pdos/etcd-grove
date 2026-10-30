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

/-- `c.First()` on the read path (an open transaction): the first key and value of the
bucket (the value nil for a nested bucket), nil for an empty bucket. -/
abbrev Cursor.First.spec : Prop :=
  ∀ (cl bl : Loc) (V : BktView) (q : Qp) (es : List elemRef),
  V.ok → V.wfAt V.root →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ curI cl bl V q es }}
    (App (Val (cl @!! go.GoType.PointerType Cursor.ty @!! go!"First")) (Val #()))
  {{ (es' : List elemRef) (k v : GoSlice) (f : w32), RET (PairV #k #(kvVal v f));
      ⌜cursorOK V es' ∧ kvOK V es' k v f⌝ ∗ curI cl bl V q es' }}

end spec

end bbolt
end EtcdGrove
end Perennial
