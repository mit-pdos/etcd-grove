/-
net/http's **first** initialization on a machine: its initializer, run when net/http is not yet
initialized, also returns the exclusive state it makes: the right to register on `DefaultServeMux`,
no pattern registered (`muxOwn dmux []`, `MuxDefs.lean`). Its shape is the swiftpaxos kit's
`RpcFirstInit` (`ownInitializing g` with `g pkg_id.net.http ⊢ False`: net/http not initialized, so
this runs once per machine), for net/http alone.

**Interim trust-boundary axiom**, retired by L2 step 6 (net/rpc's and net/http's initializers
proved; notes/library-drivers.md), with `MuxDefs`' definitions refined by phase 7's S5.
-/
module

public import Net.Proof.net.http.Init
public import Net.Proof.net.http.MuxDefs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace net.http

section init
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem' : net.http.Assumptions]

/-- **Trust-boundary axiom, interim** (see the file header): net/http's first initialization.
Interim, retired by L2 step 6 (net/rpc's and net/http's initializers proved;
notes/library-drivers.md). -/
axiom wp_init_first (g g' : GoString → IProp GF)
    (hnot : g pkg_id.net.http ⊢ iprop(False))
    (Hinit : GetIsPkgInitProp pkg_id.net.http g')
    (hsame : ∀ p, p ≠ pkg_id.net.http → g' p = g p) :
    {{ ownInitializing g }} (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing g' ∗ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗
        muxOwn (GF := GF) dmux [] }}

end init

end net.http
end Perennial
