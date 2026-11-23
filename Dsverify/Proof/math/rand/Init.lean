/-
**A hypothesis**: `math.rand`'s initializer meets Perennial's initialization spec (notes/dsv-gryff.md,
"Hypotheses"; the pattern of dsv-vr's `Dsverify/Proof/encoding/json/Init.lean`): Perennial translates `math/rand` but proves no initialization of it (the lab's
`Harness/Proof/math/rand.lean` stated its own).
The rule is no new axiom, so the spec is the class `InitHyp` (a `Prop`), which every theorem whose
proof initializes `math.rand` takes as an instance argument, up to the kit's closed statement. Replace
by the proved `wp_initialize'` when it lands.
-/
module

public import Dsverify.Proof.math.rand.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic

namespace math.rand

/-- **Hypothesis** (the file header): `math.rand`'s initializer establishes its package fact. -/
class InitHyp [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext] {hlc : HasLC}
    (GF : BundledGFunctors) [HeapGS hlc GF] [go.Semantics] : Prop where
  wp_init : ∀ (get_is_pkg_init : GoString → IProp GF),
    GetIsPkgInitProp pkg_id.math.rand get_is_pkg_init →
    {{ ownInitializing get_is_pkg_init }} (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗ isPkgInit (PROP := IProp GF) pkg_id.math.rand }}

section init
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [sem : go.Semantics]

/-- Perennial's form of `math.rand`'s initialization, from the hypothesis. -/
theorem wp_initialize' [h : InitHyp GF] (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.math.rand get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }} (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗ isPkgInit (PROP := IProp GF) pkg_id.math.rand }} :=
  h.wp_init get_is_pkg_init Hinit

end init

end math.rand

end Perennial
