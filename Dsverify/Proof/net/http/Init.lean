/-
The initializer of `net/http` as a **hypothesis** of the part's EPaxos proofs (notes/dsv-epaxos.md,
"Hypotheses"; `etc/gen-init.py`'s `DSV_HYP_INITS`): `Net/`'s model of net/http has no initializer proof (plan 5.2 item 7; its imports' initializers are not all translated). The class `net.http.InitHyp GF` says that
it establishes the package's fact (`True` here: no proof of the part reads a variable of `net/http`);
generated initializers take it as an instance (dsv-vr's mechanism, `dsv_hyp_fix`). To discharge:
prove `net.http.wp_initialize'` (a generated `Init.lean` without axioms) and replace this module by it.
-/
module

public import Net.GeneratedProof.net.http
public import Net.Proof.runtime.PkgInitExt

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace net.http

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The package's fact, `True`, written by hand (not `define_is_pkg_init`, which needs the facts of
all its imports, some of which have none in the part): no importer reads the imports' facts
through it. -/
instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.net.http :=
  { isPkgInitDeps := iprop(True), isPkgInitDef := iprop(True) }
/-- Its well-formedness: `get_is_pkg_init` gives its fact (its imports' are not constrained). -/
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.net.http :=
  { get_is_pkg_init_prop_def := fun g => g pkg_id.net.http = isPkgInit pkg_id.net.http ∧ True }

end def_

section init
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [sem : go.Semantics]

/-- **Hypothesis** (the file header): `net/http`'s initializer establishes its package fact. -/
class InitHyp [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext] {hlc : HasLC}
    (GF : BundledGFunctors) [HeapGS hlc GF] [go.Semantics] : Prop where
  wp_init : ∀ (get_is_pkg_init : GoString → IProp GF),
    GetIsPkgInitProp pkg_id.net.http get_is_pkg_init →
    {{ ownInitializing get_is_pkg_init }} (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗ isPkgInit (PROP := IProp GF) pkg_id.net.http }}

/-- Perennial's form of `net/http`'s initialization, from the hypothesis. -/
theorem wp_initialize' [h : InitHyp GF] (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.net.http get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }} (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗ isPkgInit (PROP := IProp GF) pkg_id.net.http }} :=
  h.wp_init get_is_pkg_init Hinit

end init

end net.http
end Perennial
