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

/-- `l.Panicf(...)`: `log.Logger.Panicf` writes the message and then panics, always. A panic is a
safety violation, so the only sound triple has precondition `False`: a caller must show it never
reaches this call. (bbolt itself never calls it.) -/
abbrev DefaultLogger.Panicf.spec : Prop :=
  ∀ (dl : Loc) (f : GoString) (v : GoSlice),
  {{ (⌜False⌝ : IProp GF) }}
    (App (App (Val (dl @!! go.GoType.PointerType DefaultLogger.ty @!! go!"Panicf")) (Val #f)) (Val #v))
  {{ RET #(); True }}

end spec

end bbolt
end EtcdGrove
end Perennial
