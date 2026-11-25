/-
The initializer of `github.com/google/uuid` as a **hypothesis** of the part's swiftpaxos proofs (notes/dsv-swiftpaxos.md,
"Hypotheses"; `etc/gen-init.py`'s `HYP_INITS`): `github.com/google/uuid` is translated names and types only in the part (no model: the proof's specs of it are hypotheses, notes/dsv-swiftpaxos.md), so its initializer (`nodeMu`, `rander`, the pool variables) cannot be proved here. The class `github_com.google.uuid.InitHyp GF` says that it
establishes the package's fact (`True` here: no proof of the part reads a variable of the package);
initializers that run it take it as an instance (dsv-vr's mechanism, `dsv_hyp_fix`), up to the kit's
closed statement, where it is a visible premise. To discharge: a model of the package with a proved
`wp_initialize'`.
-/
module

public import Dsverify.GeneratedProof.github_com.google.uuid
public import Proof.runtime.PkgInitExt

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace github_com.google.uuid

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The package's fact, `True`, written by hand (not `define_is_pkg_init`, which needs the facts of
all its imports, some of which have none in the part): no importer reads the imports' facts
through it. -/
instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.google.uuid :=
  { isPkgInitDeps := iprop(True), isPkgInitDef := iprop(True) }
/-- Its well-formedness: `get_is_pkg_init` gives its fact (its imports' are not constrained). -/
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.google.uuid :=
  { get_is_pkg_init_prop_def := fun g => g pkg_id.github_com.google.uuid = isPkgInit pkg_id.github_com.google.uuid ∧ True }

end def_

section init
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [sem : go.Semantics]

/-- **Hypothesis** (the file header): `github.com/google/uuid`'s initializer establishes its package fact. -/
class InitHyp [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext] {hlc : HasLC}
    (GF : BundledGFunctors) [HeapGS hlc GF] [go.Semantics] : Prop where
  wp_init : ∀ (get_is_pkg_init : GoString → IProp GF),
    GetIsPkgInitProp pkg_id.github_com.google.uuid get_is_pkg_init →
    {{ ownInitializing get_is_pkg_init }} (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗ isPkgInit (PROP := IProp GF) pkg_id.github_com.google.uuid }}

/-- Perennial's form of `github.com/google/uuid`'s initialization, from the hypothesis. -/
theorem wp_initialize' [h : InitHyp GF] (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.google.uuid get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }} (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗ isPkgInit (PROP := IProp GF) pkg_id.github_com.google.uuid }} :=
  h.wp_init get_is_pkg_init Hinit

end init

end github_com.google.uuid
end Perennial
