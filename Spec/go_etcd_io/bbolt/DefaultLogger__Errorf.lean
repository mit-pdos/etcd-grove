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

/-- The default logger at `dl`: a `DefaultLogger` (not debugging) over a set-up `log.Logger`,
persistently. -/
def defaultLoggerOK (dl : Loc) : IProp GF :=
  iprop(∃ (ll : Loc), (dl ↦□ DefaultLogger.mk ll false : IProp GF) ∗ isLog ll)

instance defaultLoggerOK_persistent (dl : Loc) : Persistent (defaultLoggerOK (GF := GF) dl) := by
  unfold defaultLoggerOK; infer_instance

/-- `l.Errorf(format, v...)` of the default logger: logs, returns. -/
abbrev DefaultLogger.Errorf.spec : Prop :=
  ∀ (dl : Loc) (f : GoString) (v : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ defaultLoggerOK dl }}
    (App (App (Val (dl @!! go.GoType.PointerType DefaultLogger.ty @!! go!"Errorf")) (Val #f)) (Val #v))
  {{ RET #(); True }}

end spec

end bbolt
end EtcdGrove
end Perennial
