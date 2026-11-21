/-
`fmt.Errorf(format, args...)` with read-only slices among the arguments, under `%v`/`%s`
(`fmt.argsOkSl`): `fmt.ErrorfLeaf.spec`'s statement for the arguments Perennial's model of `fmt` does
not cover (it is stuck on reflection into a slice; fmtmodel, 2026-11-20: until then `fmt.argsOk` admitted
these slices and `fmt.ErrorfLeaf` was proved over the previous model, which ignored the arguments). The
union authorizer's `%v` of a `[]string` (`ConditionsAwareDecisionUnion.Add`) and of a `[]Decision`
(`unionAuthzHandler.EvaluateConditions`). Proof: `Proof/fmt/ErrorfSlice.lean` (an axiom). Lean-first.
-/
module

public import Spec.fmt.ErrorfErrs
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

/-- See the file header: `fmt.ErrorfLeaf.spec` with `fmt.argsOkSl` for `fmt.argsOk`. -/
abbrev fmt.ErrorfSlice.spec : Prop :=
  ∀ (format : GoString) (args_sl : GoSlice) (xs : List GoInterface) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args_sl ↦*{dq} xs ∗ fmt.argsOkSl fmt.errorfVerbs format xs }}
    (App (App (Val (@! _root_.Perennial.fmt.Errorf)) (Val #format)) (Val #args_sl))
  {{ (err : GoInterfaceOk), RET #(interface.ok err);
      args_sl ↦*{dq} xs ∗ errOk err ∗ ⌜methodSet err.ty !! go!"Errors" = none⌝ }}

end spec

end EtcdGrove
end Perennial
