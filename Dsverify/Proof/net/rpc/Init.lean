/-
The initializer of `net/rpc` as a **hypothesis** of the part's EPaxos proofs (notes/dsv-epaxos.md,
"Hypotheses"; `etc/gen-init.py`'s `DSV_HYP_INITS`): `Net/`'s model of net/rpc has no initializer proof (its closure reaches net/http's untranslated initializers; notes/dsverify-net-port-plan.md, 5.2 item 5). The class `net.rpc.InitHyp GF` says that
it establishes the package's fact (`True` here: no proof of the part reads a variable of `net/rpc`) and those of
every package its initializer reaches (its imports' initializers run first: the well-formedness
condition `GetIsPkgInitProp pkg_id.net.rpc` constrains the table at each of them, net/http's
closure included; a package with no fact elsewhere has a `True` one in the part);
generated initializers take it as an instance (dsv-vr's mechanism, `dsv_hyp_fix`). To discharge:
prove `net.rpc.wp_initialize'` (a generated `Init.lean` without axioms) and replace this module by it.
-/
module

public import Net.GeneratedProof.net.rpc
public import Proof.runtime.PkgInitExt
public import Dsverify.Proof.net.http.Init
public import Dsverify.Proof.go.token.Base
public import Perennial.Proof.log.Base

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace net.rpc

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The package's fact: `True`, with its imports' facts (`define_is_pkg_init`). -/
instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.net.rpc :=
  define_is_pkg_init iprop(True)
/-- Its well-formedness: `get_is_pkg_init` gives its fact and, recursively, the facts of every
package its initializer reaches (its `PkgInfo` imports, which are the packages whose initializers
`initialize'` runs: `build_get_is_pkg_init_wf`). -/
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.net.rpc :=
  build_get_is_pkg_init_wf

end def_

section init
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [sem : go.Semantics]

/-- **Hypothesis** (the file header): `net/rpc`'s initializer establishes its package fact. -/
class InitHyp [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext] {hlc : HasLC}
    (GF : BundledGFunctors) [HeapGS hlc GF] [go.Semantics] : Prop where
  wp_init : ∀ (get_is_pkg_init : GoString → IProp GF),
    GetIsPkgInitProp pkg_id.net.rpc get_is_pkg_init →
    {{ ownInitializing get_is_pkg_init }} (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗ isPkgInit (PROP := IProp GF) pkg_id.net.rpc }}

/-- Perennial's form of `net/rpc`'s initialization, from the hypothesis. -/
theorem wp_initialize' [h : InitHyp GF] (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.net.rpc get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }} (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗ isPkgInit (PROP := IProp GF) pkg_id.net.rpc }} :=
  h.wp_init get_is_pkg_init Hinit

end init

end net.rpc
end Perennial
