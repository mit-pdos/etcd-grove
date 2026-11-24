/-
The initializer of `net/http` (the part `Net/`'s model, `models/net/http`; its imports' initializers are not all translated): its
`wp_initialize'`, an **interim trust-boundary axiom** (below), and its package fact `True`
(`PkgInit.lean`). Taken by the generated initializers of the part's packages that import it (as an
external initializer: `etc/gen-init.py`'s `NET_AXIOM_INITS`, registered in
`Proof/runtime/PkgInitNet.lean`), so that a top-level statement over a program importing it
(`examples/net/rpcdriver`) has no premise for it. `Dsverify/` keeps its hypothesis
(`Dsverify/Proof/net/http/Init.lean`'s `InitHyp`, a premise of the kits' statements) over the same
fact.
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

/-- **Trust-boundary axiom, interim**: `net/http`'s initializer establishes its package fact
(`True`) and, before it, those of every package it reaches (`GetIsPkgInitProp`: its imports'
initializers run first). Interim, retired by L2 step 6 (net/rpc's and net/http's initializers
proved; notes/library-drivers.md). -/
axiom wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.net.http get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }} (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗ isPkgInit (PROP := IProp GF) pkg_id.net.http }}

end init

end net.http
end Perennial
