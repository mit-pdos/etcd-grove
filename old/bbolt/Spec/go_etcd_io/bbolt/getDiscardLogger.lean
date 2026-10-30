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

/-- The default logger as a `Logger`: the `*DefaultLogger` at `dl` (`discardLogger`'s value). -/
def discardIface (dl : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType DefaultLogger.ty) #dl

/-- `getDiscardLogger()`: the global `discardLogger`, as a `Logger`. -/
abbrev getDiscardLogger.spec : Prop :=
  ∀ (dl : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ (globalAddr discardLogger ↦□ dl : IProp GF) }}
    (App (Val #(functions getDiscardLogger [])) (Val #()))
  {{ RET #(discardIface dl); True }}

end spec

end bbolt
end EtcdGrove
end Perennial
