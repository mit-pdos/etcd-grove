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

/-- `b.Sequence()` on the read path: the bucket's sequence (its `InBucket` header's). -/
abbrev Bucket.Sequence.spec : Prop :=
  ∀ (bl : Loc) (V : BktView) (q : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ bktR bl V q }}
    (App (Val (bl @!! go.GoType.PointerType Bucket.ty @!! go!"Sequence")) (Val #()))
  {{ RET #V.seq; bktR bl V q }}

end spec

end bbolt
end EtcdGrove
end Perennial
