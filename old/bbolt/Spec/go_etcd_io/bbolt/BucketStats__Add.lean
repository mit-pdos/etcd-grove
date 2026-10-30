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

/-- `s.Add(other)`: adds `other`'s counts to `s`'s, the depth the larger. -/
abbrev BucketStats.Add.spec : Prop :=
  ∀ (l : Loc) (v o : BucketStats),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ l ↦ v }}
    (App (Val (l @!! go.GoType.PointerType BucketStats.ty @!! go!"Add")) (Val #o))
  {{ RET #(); l ↦ (BucketStats.mk (v.BranchPageN' + o.BranchPageN') (v.BranchOverflowN' + o.BranchOverflowN') (v.LeafPageN' + o.LeafPageN') (v.LeafOverflowN' + o.LeafOverflowN') (v.KeyN' + o.KeyN') (if sint.Z v.Depth' < sint.Z o.Depth' then o.Depth' else v.Depth') (v.BranchAlloc' + o.BranchAlloc') (v.BranchInuse' + o.BranchInuse') (v.LeafAlloc' + o.LeafAlloc') (v.LeafInuse' + o.LeafInuse') (v.BucketN' + o.BucketN') (v.InlineBucketN' + o.InlineBucketN') (v.InlineBucketInuse' + o.InlineBucketInuse')) }}

end spec

end bbolt
end EtcdGrove
end Perennial
