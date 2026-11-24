/-
`v.IsNil()` of the addressable `Value` of the slice variable at `p`: true only of an empty slice
(revised after the attack, change 4), false only of a non-nil slice.

Faithful: `IsNil` of a slice is `Data == nil`, which only a nil slice has, whose length is 0
(`reflect/value.go`; this repository's attack test `TestKindLenCapIsNil`,
`examples/k8s7e2attack/attack_test.go`).
False only of a non-nil slice (`b = false → s ≠ slice.nil`, added 2026-11-19, stage 7g,
`notes/k8s-7g-trust.md`): `false` means `Data != nil`, and the model's `slice.nil` (`⟨null, 0, 0⟩`) is Go's
nil slice, the only REACHABLE slice with a nil `Data`; a non-nil `Data` (`&zerobase` too) is a non-null
location in the model. The model has other null-pointer slices (`⟨null, 0, c⟩`, from slicing a nil array
pointer, where Go panics: Perennial's `docs/KNOWN_LIMITATIONS.md`, "Field and element addresses through nil
do not panic"), so "ptr null → `slice.nil`" is NOT a law of the model; never rely on it (attack
`/shared/tmp/isnil-attack/report.md`, minor 1). Needed by `finalizeList`, whose `if v.IsNil() { v.Set(MakeSlice(…, 0, 0)) }` leaves the items
non-nil on both branches. Go: `examples/k8s/etcd3/trustspecs_test.go` `TestIsNilFalseNonNil`.

Proved over Perennial's model of `reflect` (reflect S0, `Proof/reflect/Value__IsNil.lean`; until then a trust-boundary axiom, stage 7e-2, `notes/k8s-7e-2-draft.md` §5.2, attacked in `notes/k8s-7e-2-attack.md`), in the vocabulary of `Proof/reflect/Values.lean`. Lean-first (no Rocq counterpart).
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
abbrev reflect.Value.IsNil.spec : Prop :=
  ∀ (vp : Loc) (dq dq' : DFrac) (v : _root_.Perennial.reflect.Value) (T : go.GoType) (p : Loc) (s : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.reflect ∗ vp ↦{dq} v ∗
      ⌜reflElem v (go.GoType.SliceType T) p⌝ ∗ p ↦{dq'} s }}
    (App (Val #(methods (go.GoType.PointerType _root_.Perennial.reflect.Value.ty) go!"IsNil" #vp)) (Val #()))
  {{ (b : Bool), RET #b; ⌜(b = true → uint.Z s.len = 0) ∧ (b = false → s ≠ slice.nil)⌝ ∗ vp ↦{dq} v ∗ p ↦{dq'} s }}

end spec

end EtcdGrove
end Perennial
