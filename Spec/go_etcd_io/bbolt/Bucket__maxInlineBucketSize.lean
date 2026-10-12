module
public import Proof.go_etcd_io.bbolt.Inlineable

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

/-- `b.maxInlineBucketSize()`: a quarter of the page size `b.tx.db.pageSize` (`maxInline`). -/
abbrev Bucket.maxInlineBucketSize.spec : Prop :=
  ∀ (bl : Loc) (bv : Bucket) (dq : DFrac) (dbl : Loc) (dt : DFrac) (ps : Nat),
  ps < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ bl ↦{dq} bv ∗
      structFieldRef Tx go!"db" bv.tx' ↦{dt} dbl ∗
      structFieldRef DB go!"pageSize" dbl ↦□ W64 (ps : Int) }}
    (App (Val (bl @!! go.GoType.PointerType Bucket.ty @!! go!"maxInlineBucketSize")) (Val #()))
  {{ RET #(maxInline ps); bl ↦{dq} bv ∗ structFieldRef Tx go!"db" bv.tx' ↦{dt} dbl }}

end spec

end bbolt
end EtcdGrove
end Perennial
