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

/-- `l.Flags()` of a set-up `*log.Logger`: some flags (they are not modeled: the output goes to
`io.Discard`; Go keeps them in an `atomic.Int32`, so the call is safe under any sharing). -/
abbrev log.Logger.Flags.spec : Prop :=
  ∀ (l : Loc),
  {{ isLog (GF := GF) l }}
    (App (Val (l @!! go.GoType.PointerType _root_.Perennial.log.Logger.ty @!! go!"Flags")) (Val #()))
  {{ (fl : w64), RET #fl; True }}

end spec

end bbolt
end EtcdGrove
end Perennial
