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

/-- `l.EnableTimestamps()` of a `DefaultLogger` over a set-up `log.Logger`: sets the
`log.Logger`'s date and time flags (not modeled: `isLog` is persistent, Go's flags atomic), and
returns. It reads the `DefaultLogger`, writes none of its fields. -/
abbrev DefaultLogger.EnableTimestamps.spec : Prop :=
  ∀ (dl ll : Loc) (d : Bool) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ dl ↦{dq} DefaultLogger.mk ll d ∗ isLog ll }}
    (App (Val (dl @!! go.GoType.PointerType DefaultLogger.ty @!! go!"EnableTimestamps")) (Val #()))
  {{ RET #(); dl ↦{dq} DefaultLogger.mk ll d }}

end spec

end bbolt
end EtcdGrove
end Perennial
