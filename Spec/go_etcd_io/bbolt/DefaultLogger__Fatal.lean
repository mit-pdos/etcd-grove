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

/-- `l.Fatal(...)` of the default logger: logs (at level FATAL), then `os.Exit(1)`: it never
returns (postcondition `False`; the program ends). -/
abbrev DefaultLogger.Fatal.spec : Prop :=
  ∀ (dl : Loc) (v : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ defaultLoggerOK dl }}
    (App (Val (dl @!! go.GoType.PointerType DefaultLogger.ty @!! go!"Fatal")) (Val #v))
  {{ RET #(); False }}

end spec

end bbolt
end EtcdGrove
end Perennial
