/-
Package initialization of `k8s_io.apiserver.pkg.util.feature`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`featureInit`, `storage/etcd3/Base.lean`): `DefaultFeatureGate` holds a feature
gate whose `Enabled` answers some `bool` for any feature. Its initializer initializes its import
(`component-base/featuregate`, names-only) and runs its variables' untranslated initializers
(`feature_gate.go`); the trust-boundary axiom `DefaultFeatureGate_init` states the one the fact
reads (`DefaultMutableFeatureGate`, a `featuregate.NewFeatureGate()`, whose `Enabled` looks the
feature up in its map and returns; which features are on is the deployment's), `opaqueInitsOk`
the other.
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base
public import Proof.k8s_io.component_base.featuregate.Init
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
namespace k8s_io.apiserver.pkg.util.feature
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `k8s_io.apiserver.pkg.util.feature`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([DefaultMutableFeatureGate.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

/-- `DefaultFeatureGate = DefaultMutableFeatureGate` (`feature_gate.go`, a `featuregate.NewFeatureGate()`): a gate whose `Enabled` returns some `bool` for any feature. -/
axiom DefaultFeatureGate_init :
    {{ (True : IProp GF) }} (App (Val DefaultFeatureGate.init) (Val #()))
    {{ RET #(); ∃ g : GoInterfaceOk, globalAddr DefaultFeatureGate ↦ GoInterface.ok g ∗
      □ ∀ (f : val) (Φ : val → IProp GF), ▷ (∀ b : Bool, Φ #b) -∗
        WP (App (Val #(methods g.ty go!"Enabled" g.v)) (Val f)) {{ Φ }} }}

end k8s_io.apiserver.pkg.util.feature
end opaqueInits

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.k8s_io.apiserver.pkg.util.feature.Assumptions]

namespace k8s_io.apiserver.pkg.util.feature

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.k8s_io.apiserver.pkg.util.feature get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.util.feature }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply (_root_.Perennial.k8s_io.component_base.featuregate.wp_initialize'_lb _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  wp_apply (opaqueInitsOk DefaultMutableFeatureGate.init (by mem_tac))
  wp_apply DefaultFeatureGate_init as ⟨%gDefaultFeatureGate, HDefaultFeatureGate, #SDefaultFeatureGate⟩
  ipersist HDefaultFeatureGate
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish
  imodintro
  iexists _
  iframe #

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.k8s_io.apiserver.pkg.util.feature get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.util.feature }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end k8s_io.apiserver.pkg.util.feature

end init

end Perennial
