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

/-- `db.invalidate()`: forgets the mapping and the metas. -/
abbrev DB.invalidate.spec : Prop :=
  ∀ (dbl : Loc) (d : DB),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ dbl ↦ d }}
    (App (Val (dbl @!! go.GoType.PointerType DB.ty @!! go!"invalidate")) (Val #()))
  {{ (d' : DB), RET #(); ⌜d' = ({ d with dataref' := slice.nil, data' := null, datasz' := W64 0, meta0' := null, meta1' := null } : DB)⌝ ∗ dbl ↦ d' }}

end spec

end bbolt
end EtcdGrove
end Perennial
