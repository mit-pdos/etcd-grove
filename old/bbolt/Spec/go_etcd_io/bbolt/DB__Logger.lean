module
public import Spec.go_etcd_io.bbolt.getDiscardLogger

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

/-- `db.Logger()` of an open database: its logger, the default one if nil. -/
abbrev DB.Logger.spec : Prop :=
  ∀ (dbl : Loc) (dq : DFrac) (lg : GoInterface) (dl : Loc),
  dbl ≠ null →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ structFieldRef DB go!"logger" dbl ↦{dq} lg ∗
      (globalAddr discardLogger ↦□ dl : IProp GF) }}
    (App (Val (dbl @!! go.GoType.PointerType DB.ty @!! go!"Logger")) (Val #()))
  {{ RET #(if lg = interface.nil then discardIface dl else lg);
      structFieldRef DB go!"logger" dbl ↦{dq} lg }}

end spec

end bbolt
end EtcdGrove
end Perennial
