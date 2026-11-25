/-
net/rpc's **first** initialization on a machine: its initializer, run when net/rpc is not yet
initialized, also returns the exclusive state it makes (`rpcFirstRes`): the codec registry at
`nil` (`codecUnset`, the half of `codec` that `SetCodec` takes) and `DefaultServer`'s registry,
empty, owned (`defaultServerO γ γf ∗ svcOwn γf ∅`: the right to register a fresh name, which
`Register.spec_fresh` takes). Its shape is the swiftpaxos kit's `RpcFirstInit` (`ownInitializing g`
with `g pkg_id.net.rpc ⊢ False`: net/rpc not initialized, so this runs once per machine), for
net/rpc alone (net/http's is `Net/Proof/net/http/InitFirst.lean`).

**Interim trust-boundary axiom**, retired by L2 step 6 (net/rpc's and net/http's initializers
proved; notes/library-drivers.md): there `DefaultServer`'s owned registry comes from
`NewServer.spec_owned`, and `codecUnset` from the allocation of `codec`.
-/
module

public import Net.Proof.net.rpc.Init

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

/-- What net/rpc's first initialization returns besides its fact (see the file header). -/
def rpcFirstRes : IProp GF :=
  iprop(codecUnset ∗ ∃ γ γf : GName, defaultServerO γ γf ∗ svcOwn γf ∅)

/-- **Trust-boundary axiom, interim** (see the file header): net/rpc's first initialization.
Interim, retired by L2 step 6 (net/rpc's and net/http's initializers proved;
notes/library-drivers.md). -/
axiom wp_init_first (g g' : GoString → IProp GF)
    (hnot : g pkg_id.net.rpc ⊢ iprop(False))
    (Hinit : GetIsPkgInitProp pkg_id.net.rpc g')
    (hsame : ∀ p, p ≠ pkg_id.net.rpc → g' p = g p) :
    {{ ownInitializing g }} (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing g' ∗ isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗ rpcFirstRes }}

end init

end net.rpc
end Perennial
