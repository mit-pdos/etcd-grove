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

/-- `db.growSize(mmapSize, growSize)`: `mmapSize` up to the allocation size, else `growSize`
plus the allocation size. -/
abbrev DB.growSize.spec : Prop :=
  ∀ (dbl : Loc) (d : DB) (dq : DFrac) (mmapSize growSize : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ dbl ↦{dq} d }}
    (App (App (Val (dbl @!! go.GoType.PointerType DB.ty @!! go!"growSize")) (Val #mmapSize)) (Val #growSize))
  {{ RET #(if sint.Z mmapSize ≤ sint.Z d.AllocSize' then mmapSize else growSize + d.AllocSize');
      dbl ↦{dq} d }}

end spec

end bbolt
end EtcdGrove
end Perennial
