/-
`rt.Elem()` of the `reflect.Type` of a slice type `[]T`: the `reflect.Type` of `T`.

Faithful: `Elem` of a slice type is its element type (`reflect/type.go`).

Proved over Perennial's model of `reflect` (reflect S0, `Proof/reflect/Type__Elem.lean`; until then a trust-boundary axiom, stage 7e-2, `notes/k8s-7e-2-draft.md` §5.2, attacked in `notes/k8s-7e-2-attack.md`), in the vocabulary of `Proof/reflect/Values.lean`. Lean-first (no Rocq counterpart).
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
abbrev reflect.Type.Elem.spec : Prop :=
  ∀ (rt : _root_.Perennial.reflect.Type') (T : go.GoType),
  {{ isPkgInit (PROP := IProp GF) pkg_id.reflect ∗ ⌜reflType rt (go.GoType.SliceType T)⌝ }}
    (App (App (Val (GoInstruction (MethodResolve _root_.Perennial.reflect.Type'.ty go!"Elem"))) (Val #rt))
      (Val #()))
  {{ (et : _root_.Perennial.reflect.Type'), RET #et; ⌜reflType et T⌝ }}

end spec

end EtcdGrove
end Perennial
