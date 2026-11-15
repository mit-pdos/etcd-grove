/-
`v.IsNil()` of the addressable `Value` of the slice variable at `p`: true only of an empty slice
(revised after the attack, change 4).

Faithful: `IsNil` of a slice is `Data == nil`, which only a nil slice has, whose length is 0
(`reflect/value.go`; this repository's attack test `TestKindLenCapIsNil`,
`examples/k8s7e2attack/attack_test.go`).

The trust boundary: an axiom, `Proof/reflect/Value__IsNil.lean` (`reflect` is names-only; the reasoning principles of `Proof/reflect/Values.lean`; stage 7e-2, `notes/k8s-7e-2-draft.md` §5.2, attacked in `notes/k8s-7e-2-attack.md`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.reflect.Values
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base

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
  {{ (b : Bool), RET #b; ⌜b = true → uint.Z s.len = 0⌝ ∗ vp ↦{dq} v ∗ p ↦{dq'} s }}

end spec

end EtcdGrove
end Perennial
