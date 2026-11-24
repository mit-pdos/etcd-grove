/-
The initializer of `net/http` as a **hypothesis** of the part's EPaxos proofs (notes/dsv-epaxos.md,
"Hypotheses"; `etc/gen-init.py`'s `DSV_HYP_INITS`): `Net/`'s model of net/http has no initializer proof (plan 5.2 item 7; its imports' initializers are not all translated). The class `net.http.InitHyp GF` says that
it establishes the package's fact (`True` here: no proof of the part reads a variable of `net/http`) and those of
every package its initializer reaches (its imports' initializers run first: the well-formedness
condition `GetIsPkgInitProp pkg_id.net.http` constrains the table at each of them; a package of
that closure with no fact elsewhere has a `True` one in `Net/`, `Net/Proof/<pkg>/Base.lean`);
generated initializers take it as an instance (dsv-vr's mechanism, `dsv_hyp_fix`). To discharge:
prove `net.http.wp_initialize'` (a generated `Init.lean` without axioms) and replace this module by it.
Its fact is `Net/`'s (`Net/Proof/net/http/PkgInit.lean`), shared with the part `Net/`, whose
`wp_initialize'` is an interim axiom instead (`Net/Proof/net/http/Init.lean`; rpc-driver, 2026-11-24:
until then the fact was declared here, and its closure's `True` facts were the part's).
-/
module

public import Net.Proof.net.http.PkgInit
public import Proof.runtime.PkgInitExt

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace net.http

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
