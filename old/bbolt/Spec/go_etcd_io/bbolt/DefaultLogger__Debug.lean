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

/-- `l.Debug(...)` of a `DefaultLogger` over a set-up `log.Logger`: logs (at level DEBUG) if
its `debug` flag is set (`EnableDebug`), and returns. (The default logger, `defaultLoggerOK`, is
the case `d = false`, `dq` discarded: it logs nothing.) -/
abbrev DefaultLogger.Debug.spec : Prop :=
  ∀ (dl ll : Loc) (d : Bool) (dq : DFrac) (v : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ dl ↦{dq} DefaultLogger.mk ll d ∗ isLog ll }}
    (App (Val (dl @!! go.GoType.PointerType DefaultLogger.ty @!! go!"Debug")) (Val #v))
  {{ RET #(); dl ↦{dq} DefaultLogger.mk ll d }}

end spec

end bbolt
end EtcdGrove
end Perennial
