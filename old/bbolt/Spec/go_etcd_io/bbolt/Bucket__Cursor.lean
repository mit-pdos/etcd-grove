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

/-- `b.Cursor()` on the read path: a new cursor on the bucket, never positioned (its stack
empty); it counts the cursor in the transaction's statistics. -/
abbrev Bucket.Cursor.spec : Prop :=
  ∀ (bl : Loc) (V : BktView) (q : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ bktCtx bl V q ∗ bktPages V q ∗
      txStats V.tx }}
    (App (Val (bl @!! go.GoType.PointerType Bucket.ty @!! go!"Cursor")) (Val #()))
  {{ (cl : Loc), RET #cl; curI cl bl V q [] ∗ txStats V.tx }}

end spec

end bbolt
end EtcdGrove
end Perennial
