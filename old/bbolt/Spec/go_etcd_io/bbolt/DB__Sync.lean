module
public import Spec.go_etcd_io.bbolt.getDiscardLogger
public import Spec.go_etcd_io.bbolt.fdatasync

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

/-- `db.Sync()` (the database's logger nil or the default one, so nothing is logged):
`fdatasync(db)`, its error returned. Over the fields it reads. -/
abbrev DB.Sync.spec : Prop :=
  ∀ (dbl f : Loc) (fd : w64) (dq : DFrac) (lg : GoInterface) (dl : Loc),
  dbl ≠ null → (lg = interface.nil ∨ lg = discardIface dl) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ structFieldRef DB go!"logger" dbl ↦{dq} lg ∗
      (globalAddr discardLogger ↦□ dl : IProp GF) ∗
      structFieldRef DB go!"file" dbl ↦{dq} f ∗ osFile f fd }}
    (App (Val (dbl @!! go.GoType.PointerType DB.ty @!! go!"Sync")) (Val #()))
  {{ (err : GoInterface), RET #err;
      structFieldRef DB go!"logger" dbl ↦{dq} lg ∗ structFieldRef DB go!"file" dbl ↦{dq} f }}

end spec

end bbolt
end EtcdGrove
end Perennial
