/-
Package initialization of `k8s_io.apiserver.pkg.storage.feature`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact (`checkerInit`, `storage/etcd3/Base.lean`): `CheckClient` on
`DefaultFeatureSupportChecker`'s checker returns, stated as the call's own WP, the variable's load
included (the interface type is axiomatized, Goose's gap G1). Its initializer initializes its
imports and runs its variables' untranslated initializers (`feature_support_checker.go`); the
trust-boundary axiom `DefaultFeatureSupportChecker_init` states the one the fact reads
(`newDefaultFeatureSupportChecker()`, whose `CheckClient` starts, once per endpoint, a goroutine
polling the endpoint's `Status`, and returns), `opaqueInitsOk` the others.
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base
public import Perennial.Proof.context.Link
public import Proof.go_etcd_io.etcd.client.v3.Init
public import Proof.k8s_io.apiserver.pkg.storage.Init

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

/-- `x ∈ [a, ..., x, ...]`, linear in the list (`simp` overflows on the long ones). -/
local macro "mem_tac" : tactic =>
  `(tactic| repeat (first | exact List.Mem.head _ | apply List.Mem.tail))

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section opaqueInits
namespace k8s_io.apiserver.pkg.storage.feature
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `DefaultFeatureSupportChecker = newDefaultFeatureSupportChecker()` (`feature_support_checker.go`): a checker whose `CheckClient` returns for a constructed client and its context (`checkClientOk`; sweep repairs 1, B5: until then for any arguments) (the variable never changes after). -/
axiom DefaultFeatureSupportChecker_init :
    {{ (True : IProp GF) }} (App (Val DefaultFeatureSupportChecker.init) (Val #()))
    {{ RET #(); _root_.Perennial.k8s_io.apiserver.pkg.storage.etcd3.checkerInit (GF := GF) }}

end k8s_io.apiserver.pkg.storage.feature
end opaqueInits

end Perennial
