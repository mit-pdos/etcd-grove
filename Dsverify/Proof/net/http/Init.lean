/-
The initializer of `net/http` as a **hypothesis** of the part's EPaxos proofs (notes/dsv-epaxos.md,
"Hypotheses"; `etc/gen-init.py`'s `DSV_HYP_INITS`): `Net/`'s model of net/http has no initializer proof (plan 5.2 item 7; its imports' initializers are not all translated). The class `net.http.InitHyp GF` says that
it runs from any initialization state and gives the package's fact (`True` here: no proof of the
part reads a variable of `net/http`); `wp_initialize'_lb` is the form the generated initializers call.
To discharge: prove `net.http.wp_initialize'_lb` (a generated `Init.lean` without axioms) and replace
this module by it.
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.net.http.Assumptions]

/-- **Hypothesis**: `net/http`'s initializer runs, keeping what is initialized, and gives its fact. -/
class InitHyp (GF : BundledGFunctors) [HeapGS HasLC.hasLC GF] : Prop where
  initLb : ∀ (get_is_pkg_init : GoString → IProp GF),
    GetIsPkgInitProp pkg_id.net.http get_is_pkg_init → ∀ (σ0 : GMap GoString Bool),
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.net.http }}

theorem wp_initialize'_lb [h : InitHyp GF] (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.net.http get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.net.http }} :=
  h.initLb get_is_pkg_init Hinit σ0

end init

end net.http
end Perennial
