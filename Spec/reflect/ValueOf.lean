/-
`reflect.ValueOf` of an interface holding a pointer `p` (of any type `*T`): a `reflect.Value` whose
`IsNil()` reports whether `p` is nil and whose `Elem()`, for a non-nil `p`, is the addressable `Value`
of the `T` at `p` (`reflElem`). Lean-first (no Rocq counterpart); unit P4 (2026-10-14), for the txn
package's `isNil` (`util.go`: `reflect.ValueOf(msg).IsNil()`); `Elem` since stage 7e-2
(`notes/k8s-7e-2-draft.md` §5.2).

`IsNil` and `Elem` are methods of the result, specified here as persistent triples of the calls as
Goose translates them (`MethodResolve reflect.Value.ty "IsNil"` on the value). Proved over Perennial's
model of `reflect` (reflect S0, `Proof/reflect/ValueOf.lean`); until then an axiom. `Elem` needs `T`
to have a kind (`go.kindOf (underlying T)`; every Go type has one, the model's opaque types need
not), as the `Elem()` of the model reads it.
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

/-- `reflect.ValueOf(i)` of an interface holding the pointer `p` of type `*T`: a value `v` whose
`IsNil()` returns whether `p` is nil, and whose `Elem()`, for a non-nil `p` and a `T` with a kind, is
the addressable `Value` of the `T` at `p` (persistent). -/
abbrev reflect.ValueOf.spec : Prop :=
  ∀ (T : go.GoType) (p : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
    (App (Val (@! _root_.Perennial.reflect.ValueOf))
      (Val #(interface.mkOk (go.GoType.PointerType T) #p)))
  {{ (v : val), RET v;
      □ ({{ True }}
          (App (App (Val (GoInstruction (MethodResolve _root_.Perennial.reflect.Value.ty go!"IsNil")))
            (Val v)) (Val #()))
        {{ RET #(decide (p = null)); True }}) ∗
      □ ({{ ⌜p ≠ null ∧ ∃ k : Nat, go.kindOf (underlying T) = some k⌝ }}
          (App (App (Val (GoInstruction (MethodResolve _root_.Perennial.reflect.Value.ty go!"Elem")))
            (Val v)) (Val #()))
        {{ (e : _root_.Perennial.reflect.Value), RET #e; ⌜reflectM.reflElem e T p⌝ }}) }}

end spec

end EtcdGrove
end Perennial
