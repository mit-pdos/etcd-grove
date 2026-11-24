/-
`reflect.TypeOf` of a non-nil interface whose dynamic type is not the model's `rtype`
(`reflectM.notRType`): some `reflect.Type`, whose `String()` returns some string (`String()` of the
nil `Type` panics). As `reflect.ValueOf`'s `IsNil`, `String` is specified in the postcondition, as a
persistent triple of the call as Goose translates it (`MethodResolve reflect.Type'.ty "String"` on the
value). Lean-first (no Rocq counterpart); for the Kubernetes etcd3 store's `getTypeName`
(`reflect.TypeOf(obj).String()`, a tracing attribute).

Proved over Perennial's model of `reflect` (reflect S0, `Proof/reflect/TypeOf.lean`), from the
trust-boundary spec of the names-only `rtype.String` (`Spec/reflect/rtype__String.lean`). Until
reflect S0 an axiom for every non-nil interface; the model's `TypeOf` is stuck on a value of reflect's
own `rtype`, hence the premise.
-/
module

public import Perennial.Proof.reflect.Base
public import Proof.reflect.Values

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- See the file header. -/
abbrev reflect.TypeOf.spec : Prop :=
  ∀ (x : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.reflect ∗ ⌜reflectM.notRType x⌝ }}
    (App (Val (@! _root_.Perennial.reflect.TypeOf)) (Val #x))
  {{ (t : val), RET t;
      □ ({{ True }}
          (App (App (Val (GoInstruction (MethodResolve _root_.Perennial.reflect.Type'.ty go!"String")))
            (Val t)) (Val #()))
        {{ (s : GoString), RET #s; True }}) }}

end spec

end EtcdGrove
end Perennial
