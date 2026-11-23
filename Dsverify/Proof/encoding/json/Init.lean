/-
**A hypothesis**: `encoding.json`'s initializer meets Perennial's initialization spec (notes/dsv-vr.md,
"Hypotheses"). `encoding.json` is translated names only in the part (its model's Lean half does not exist
yet), so its `initialize'` cannot be proved here, and the rule is no new axiom: the spec is the
class `InitHyp` (a `Prop`), which every theorem whose proof initializes `encoding.json` takes as an
instance argument (`etc/gen-init.py`'s `dsv_inits` adds the section variable), up to the kit's
closed statement. Replace by the model's proved `wp_initialize'` when it lands.
-/
module

public import Dsverify.Proof.encoding.json.Base
public import Net.Proof.runtime.PkgInitExt

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic

namespace encoding.json

/-- **Hypothesis** (the file header): `encoding.json`'s initializer establishes its package fact. -/
class InitHyp [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext] {hlc : HasLC}
    (GF : BundledGFunctors) [HeapGS hlc GF] [go.Semantics] : Prop where
  wp_init : ∀ (get_is_pkg_init : GoString → IProp GF),
    GetIsPkgInitProp pkg_id.encoding.json get_is_pkg_init →
    {{ ownInitializing get_is_pkg_init }} (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗ isPkgInit (PROP := IProp GF) pkg_id.encoding.json }}

section init
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [sem : go.Semantics]

/-- Perennial's form of `encoding.json`'s initialization, from the hypothesis. -/
theorem wp_initialize' [h : InitHyp GF] (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.encoding.json get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }} (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗ isPkgInit (PROP := IProp GF) pkg_id.encoding.json }} :=
  h.wp_init get_is_pkg_init Hinit

end init

end encoding.json
end Perennial
