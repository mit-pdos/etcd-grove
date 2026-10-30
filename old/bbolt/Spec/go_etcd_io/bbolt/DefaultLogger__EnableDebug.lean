module
public import Spec.go_etcd_io.bbolt.header
public import Proof.log.LogModel

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

/-- `l.EnableDebug()`: sets the `DefaultLogger`'s `debug` flag (so it needs the logger's
points-to, whole: the default logger's `defaultLoggerOK` is persistent and stays not debugging). -/
abbrev DefaultLogger.EnableDebug.spec : Prop :=
  ∀ (dl ll : Loc) (d : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ dl ↦ DefaultLogger.mk ll d }}
    (App (Val (dl @!! go.GoType.PointerType DefaultLogger.ty @!! go!"EnableDebug")) (Val #()))
  {{ RET #(); dl ↦ DefaultLogger.mk ll true }}

end spec

end bbolt
end EtcdGrove
end Perennial
