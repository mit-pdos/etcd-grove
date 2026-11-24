/-
The initializer of `net/rpc` (the part `Net/`'s model, `models/net/rpc`; its closure reaches net/http): its
`wp_initialize'`, an **interim trust-boundary axiom** (below), and its package fact `rpcInit`
(`PkgInit.lean`). Taken by the generated initializers of the part's packages that import it (as an
external initializer: `etc/gen-init.py`'s `NET_AXIOM_INITS`, registered in
`Proof/runtime/PkgInitNet.lean`), so that a top-level statement over a program importing it
(`examples/net/rpcdriver`) has no premise for it. Its first
initialization, which also returns the exclusive state the initializer makes, is `InitFirst.lean`.
`Dsverify/` keeps its hypothesis (`Dsverify/Proof/net/rpc/Init.lean`'s `InitHyp`, a premise of the
kits' statements) over its own `True` fact.
-/
module

public import Net.Proof.net.rpc.PkgInit
public import Proof.runtime.PkgInitExt

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace net.rpc

section init
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions]

/-- **Trust-boundary axiom, interim**: `net/rpc`'s initializer establishes its package fact
(`rpcInit`) and, before it, those of every package it reaches (`GetIsPkgInitProp`: its imports'
initializers run first). Interim, retired by L2 step 6 (net/rpc's and net/http's initializers
proved; notes/library-drivers.md). -/
axiom wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.net.rpc get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }} (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗ isPkgInit (PROP := IProp GF) pkg_id.net.rpc }}

end init

end net.rpc
end Perennial
