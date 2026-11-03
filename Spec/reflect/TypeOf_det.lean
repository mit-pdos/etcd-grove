/-
`reflect.TypeOf`, deterministic: **a trust-boundary axiom PROPOSAL** (the DaemonSet run's track A,
for the trust-frontier review; not used by any proof yet, not an axiom: a `Prop` a proof may take
as a hypothesis once approved). Lean-first.

`Spec/reflect/TypeOf.lean` (the current boundary spec) says only that `TypeOf` of a non-nil
interface returns some `reflect.Type` with a `String()`. client-go's informer factory keys its map
of informers by `reflect.TypeOf(obj)` (`sharedInformerFactory.InformerFor`, `factory.go`), and the
reflector checks watch events against `reflect.TypeOf(expectedType)`, so their proofs need:

* **deterministic in the dynamic type**: `TypeOf(x)` for `x = interface.mkOk t v` is a function of
  `t` alone (`rt t`), the value `v` playing no part;
* **injective on types**: two different dynamic types have different `reflect.Type`s;
* **comparable**: each `rt t` is a pointer (Go's `*rtype`), so a map lookup or `==` on it does
  not panic.

All three are Go's documented behavior (`reflect.TypeOf` "returns the reflection Type that
represents the dynamic type of i"; types are compared by identity, `reflect.Type` values are
`*rtype` pointers, one per type). What it admits beyond the code's uses: the statement is about
`TypeOf` alone, says nothing of the `Type`'s methods, and claims nothing for the `nil` interface.
-/
module

public import Spec.reflect.TypeOf

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

/-- **`reflect.TypeOf` is a function of the dynamic type, injective, with comparable results**
(the proposal: see the file header). -/
abbrev reflect.TypeOf_det.spec : Prop :=
  ∃ rt : go.GoType → GoInterface,
    (∀ t1 t2, rt t1 = rt t2 → t1 = t2) ∧
    (∀ t, ∃ (ty : go.GoType) (p : Loc), rt t = interface.mkOk (go.GoType.PointerType ty) #p) ∧
    ∀ (t : go.GoType) (v : val),
      {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
        (App (Val (@! _root_.Perennial.reflect.TypeOf)) (Val #(interface.mkOk t v)))
      {{ RET #(rt t); True }}

end spec

end EtcdGrove
end Perennial
