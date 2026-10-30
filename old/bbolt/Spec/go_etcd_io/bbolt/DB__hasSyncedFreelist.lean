module
public import Spec.go_etcd_io.bbolt.DB__meta

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
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]

/-- `db.hasSyncedFreelist()`: the current meta (`metaPick`) records a freelist page (its
`freelist` is not `PgidNoFreelist`). Over what `db.meta()` reads. -/
abbrev DB.hasSyncedFreelist.spec : Prop :=
  ∀ (dbl m0 m1 : Loc) (dq dq0 dq1 : DFrac) (v0 v1 : internal.common.Meta),
  m0.locCar ≠ 0 → m1.locCar ≠ 0 → metaValid v0 ∨ metaValid v1 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗
      structFieldRef DB go!"meta0" dbl ↦{dq} m0 ∗ structFieldRef DB go!"meta1" dbl ↦{dq} m1 ∗
      m0 ↦{dq0} v0 ∗ m1 ↦{dq1} v1 }}
    (App (Val (dbl @!! go.GoType.PointerType DB.ty @!! go!"hasSyncedFreelist")) (Val #()))
  {{ RET #(!decide ((if metaPick v0 v1 then v1 else v0).freelist' = W64 18446744073709551615));
      structFieldRef DB go!"meta0" dbl ↦{dq} m0 ∗ structFieldRef DB go!"meta1" dbl ↦{dq} m1 ∗
      m0 ↦{dq0} v0 ∗ m1 ↦{dq1} v1 }}

end spec

end bbolt
end EtcdGrove
end Perennial
