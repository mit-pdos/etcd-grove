module
public import Proof.go_etcd_io.bbolt.BucketRead

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

/-- `tx.Cursor()` on the read path: a cursor on the root bucket (`&tx.root`, see
`Bucket.Cursor.spec`). -/
abbrev Tx.Cursor.spec : Prop :=
  ∀ (txl : Loc) (V : BktView) (q : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗
      bktCtx (structFieldRef Tx go!"root" txl) V q ∗ bktPages V q ∗ txStats V.tx }}
    (App (Val (txl @!! go.GoType.PointerType Tx.ty @!! go!"Cursor")) (Val #()))
  {{ (cl : Loc), RET #cl; curI cl (structFieldRef Tx go!"root" txl) V q [] ∗ txStats V.tx }}

end spec

end bbolt
end EtcdGrove
end Perennial
