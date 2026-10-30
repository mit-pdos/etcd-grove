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

/-- `l.SetFlags(fl)` of a set-up `*log.Logger`: returns (the flags are not modeled; Go stores
them atomically, so the call is safe under any sharing and `isLog` stays persistent). -/
abbrev log.Logger.SetFlags.spec : Prop :=
  ∀ (l : Loc) (fl : w64),
  {{ isLog (GF := GF) l }}
    (App (Val (l @!! go.GoType.PointerType _root_.Perennial.log.Logger.ty @!! go!"SetFlags")) (Val #fl))
  {{ RET #(); True }}

end spec

end bbolt
end EtcdGrove
end Perennial
