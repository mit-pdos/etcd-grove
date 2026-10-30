module
public import Proof.log.LogModel

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `l.Output(calldepth, s)` of a set-up `*log.Logger`: writes the line, returns an error. -/
abbrev log.Logger.Output.spec : Prop :=
  ∀ (l : Loc) (cd : w64) (s : GoString),
  {{ isLog (GF := GF) l }}
    (App (App (Val (l @!! go.GoType.PointerType _root_.Perennial.log.Logger.ty @!! go!"Output"))
      (Val #cd)) (Val #s))
  {{ (e : GoInterface), RET #e; True }}

end spec

end bbolt
end EtcdGrove
end Perennial
