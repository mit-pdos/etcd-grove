/-
`w.Interface()` of the `Value` of the pointer `p : *T`: the interface holding `p` at type `*T`.

Proved over Perennial's model of `reflect` (reflect S0, `Proof/reflect/Value__Interface.lean`; until then a trust-boundary axiom), in the vocabulary of `Proof/reflect/Values.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Proof.reflect.Values
public import Perennial.Proof.reflect.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI reflectM

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [reflect.Assumptions]

/-- See the file header. -/
abbrev reflect.Value.Interface.spec : Prop :=
  ∀ (w : _root_.Perennial.reflect.Value) (T : go.GoType) (p : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.reflect ∗ ⌜reflPtr w T p⌝ }}
    (App (App (Val (GoInstruction (MethodResolve _root_.Perennial.reflect.Value.ty go!"Interface")))
      (Val #w)) (Val #()))
  {{ RET #(interface.mkOk (go.GoType.PointerType T) #p : GoInterface); True }}

end spec

end EtcdGrove
end Perennial
