/-
`fmt.Sprintf`: the trust boundary, for arguments that are not all of predeclared basic types
(as `fmt.Errorf` and `fmt.Printf`, `Spec/fmt/Errorf.lean`, whose `fmt.argsOk` it shares; the
snapshot handler's error messages, `%v` of an error; rafthttp stage 7e, the user's choice).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.fmt.Errorf

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.fmt.Assumptions]

/-- **`fmt.Sprintf(format, args...)`** returns some string, for arguments that are
`fmt.argsOk`; the arguments' slice comes back. The output is not modelled. -/
abbrev fmt.SprintfArgs.spec : Prop :=
  ∀ (format : GoString) (args_sl : GoSlice) (xs : List GoInterface) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args_sl ↦*{dq} xs ∗ fmt.argsOk xs }}
    (App (App (Val #(functions _root_.Perennial.fmt.Sprintf [])) (Val #format)) (Val #args_sl))
  {{ (s : GoString), RET #s; args_sl ↦*{dq} xs }}

end spec

end EtcdGrove
end Perennial
