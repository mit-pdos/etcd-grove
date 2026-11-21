/-
`fmt.Sprintf(format, args...)` with read-only slices among the arguments, under `%v`/`%s`
(`fmt.argsOkSl`): `fmt.SprintfArgs.spec`'s statement for the arguments Perennial's model of `fmt` does
not cover (it is stuck on reflection into a slice; fmtmodel, 2026-11-20: until then `fmt.argsOk`
admitted these slices, under the axiom `fmt.SprintfArgs`). `UnconditionalPartsOrFailClosed`'s `%v` of a
`[]Decision`. Proof: `Proof/fmt/SprintfSlice.lean` (an axiom). Lean-first.
-/
module

public import Spec.fmt.Errorf

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.fmt.Assumptions]

/-- See the file header: `fmt.SprintfArgs.spec` with `fmt.argsOkSl` for `fmt.argsOk`. -/
abbrev fmt.SprintfSlice.spec : Prop :=
  ∀ (format : GoString) (args_sl : GoSlice) (xs : List GoInterface) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args_sl ↦*{dq} xs ∗ fmt.argsOkSl fmt.methodVerbs format xs }}
    (App (App (Val #(functions _root_.Perennial.fmt.Sprintf [])) (Val #format)) (Val #args_sl))
  {{ (s : GoString), RET #s; args_sl ↦*{dq} xs }}

end spec

end EtcdGrove
end Perennial
