/-
`v.Kind()` of the addressable `Value` of a slice variable `[]T` (on the variable `vp` holding `v`):
`reflect.Slice` (23).

Faithful: `Kind` reads the type descriptor's kind (`reflect/value.go`).

Proved over Perennial's model of `reflect` (reflect S0, `Proof/reflect/Value__Kind.lean`; until then a trust-boundary axiom, stage 7e-2, `notes/k8s-7e-2-draft.md` §5.2, attacked in `notes/k8s-7e-2-attack.md`), in the vocabulary of `Proof/reflect/Values.lean`. Lean-first (no Rocq counterpart).
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
abbrev reflect.Value.Kind.spec : Prop :=
  ∀ (vp : Loc) (dq : DFrac) (v : _root_.Perennial.reflect.Value) (T : go.GoType) (p : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.reflect ∗ vp ↦{dq} v ∗ ⌜reflElem v (go.GoType.SliceType T) p⌝ }}
    (App (Val #(methods (go.GoType.PointerType _root_.Perennial.reflect.Value.ty) go!"Kind" #vp)) (Val #()))
  {{ RET #(W64 23); vp ↦{dq} v }}

end spec

end EtcdGrove
end Perennial
