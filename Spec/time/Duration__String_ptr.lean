/-
`(*time.Duration).String`: the trust boundary, as `Duration.String` (`Duration__String.lean`).
Goose calls a value method on an addressable variable through the pointer's method set
(`downloadTook.String()` in rafthttp's snapshot handler); Perennial translates `time` without
`Duration.String`, so its pointer wrapper is not translated either (as `Duration__Seconds_ptr`).
Lean-first (no Rocq counterpart; rafthttp stage 7e).
-/
module

public import Perennial.Proof.time

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `(&d).String()` of a duration variable `l ↦ d`: some string (as `Duration.String`); it
returns, the variable unchanged. -/
abbrev time.Duration.String_ptr.spec : Prop :=
  ∀ (l : Loc) (d : _root_.Perennial.time.Duration),
  {{ (l ↦ d : IProp GF) }}
    (App (Val (l @!! go.GoType.PointerType _root_.Perennial.time.Duration.ty @!! go!"String"))
      (Val #()))
  {{ (s : GoString), RET #s; l ↦ d }}

end spec

end EtcdGrove
end Perennial
