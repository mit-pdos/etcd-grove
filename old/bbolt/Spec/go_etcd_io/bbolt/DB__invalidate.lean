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

/-- `db.invalidate()`: forgets the mapping and the metas. Over the fields it writes. -/
abbrev DB.invalidate.spec : Prop :=
  ∀ (dbl : Loc) (dr : GoSlice) (dp : Loc) (ds : w64) (m0 m1 : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ structFieldRef DB go!"dataref" dbl ↦ dr ∗
      structFieldRef DB go!"data" dbl ↦ dp ∗ structFieldRef DB go!"datasz" dbl ↦ ds ∗ structFieldRef DB go!"meta0" dbl ↦ m0 ∗ structFieldRef DB go!"meta1" dbl ↦ m1 }}
    (App (Val (dbl @!! go.GoType.PointerType DB.ty @!! go!"invalidate")) (Val #()))
  {{ RET #(); structFieldRef DB go!"dataref" dbl ↦ slice.nil ∗ structFieldRef DB go!"data" dbl ↦ null ∗ structFieldRef DB go!"datasz" dbl ↦ W64 0 ∗
      structFieldRef DB go!"meta0" dbl ↦ null ∗ structFieldRef DB go!"meta1" dbl ↦ null }}

end spec

end bbolt
end EtcdGrove
end Perennial
