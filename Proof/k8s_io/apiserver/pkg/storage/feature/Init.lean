/-
Package initialization of `k8s_io.apiserver.pkg.storage.feature`
(item 8, 2026-10-17): its `wp_initialize'`.

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
public import Proof.runtime.PkgInitExt

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

/-- **The trust boundary: `k8s_io.apiserver.pkg.storage.feature`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([v3_4_31.init,
        v3_5_0.init,
        v3_5_13.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

/-- `DefaultFeatureSupportChecker = newDefaultFeatureSupportChecker()` (`feature_support_checker.go`): a checker whose `CheckClient` returns (the variable never changes after). -/
axiom DefaultFeatureSupportChecker_init :
    {{ (True : IProp GF) }} (App (Val DefaultFeatureSupportChecker.init) (Val #()))
    {{ RET #(); _root_.Perennial.k8s_io.apiserver.pkg.storage.etcd3.checkerInit (GF := GF) }}

end k8s_io.apiserver.pkg.storage.feature
end opaqueInits

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.k8s_io.apiserver.pkg.storage.feature.Assumptions]

namespace k8s_io.apiserver.pkg.storage.feature

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.k8s_io.apiserver.pkg.storage.feature get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.feature }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply (_root_.Perennial.k8s_io.apiserver.pkg.storage.wp_initialize'_lb _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.client.v3.wp_initialize'_lb _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.context _root_.Perennial.context.initialize'
      EtcdGrove.ExternalInit.context _root_.Perennial.context.wp_initialize' _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  wp_apply (opaqueInitsOk v3_4_31.init (by mem_tac))
  wp_apply (opaqueInitsOk v3_5_0.init (by mem_tac))
  wp_apply (opaqueInitsOk v3_5_13.init (by mem_tac))
  wp_apply DefaultFeatureSupportChecker_init as #HDefaultFeatureSupportChecker
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.k8s_io.apiserver.pkg.storage.feature get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.feature }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end k8s_io.apiserver.pkg.storage.feature

end init

end Perennial
