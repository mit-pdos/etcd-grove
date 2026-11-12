/-
Package initialization of `k8s_io.apiserver.pkg.features`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`featuresInit`, `storage/etcd3/Base.lean`): `DefaultFeatureGate` holds a gate with
the specs of `k8sfeature.featureGateOk` (`util/feature/Gate.lean`: `Enabled` of the queried
features, `Set` of one to `false`). Its initializer initializes its import (`util/feature`, whose
fact gives the gate) and runs its variable's untranslated initializer (`opaqueInitsOk`) and its
untranslated `init` (`kube_features.go:347-350`, `DefaultMutableFeatureGate.AddVersioned(...)` and
`zpagesfeatures.AddFeatureGates(...)` under `runtime.Must`), whose trust-boundary axiom
`init_0_ok` says it registers the package's features with that gate.
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base
public import Proof.k8s_io.apiserver.pkg.util.feature.Init
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
namespace k8s_io.apiserver.pkg.features
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `k8s_io.apiserver.pkg.features`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([defaultVersionedKubernetesFeatureGates.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

/-- `init.«0»` (`kube_features.go:347-350`): registers the package's features (and component-base's zpages features) with the default gate `DefaultMutableFeatureGate` holds, under `runtime.Must`; after it the gate has the specs of `featureGateOk` (`util/feature/Gate.lean`). -/
axiom init_0_ok : ∀ g : GoInterfaceOk,
    {{ (globalAddr k8s_io.apiserver.pkg.util.feature.DefaultMutableFeatureGate ↦□ GoInterface.ok g : IProp GF) }} (App (Val (@! init.«0»)) (Val #()))
    {{ RET #(); EtcdGrove.k8sfeature.featureGateOk g }}

end k8s_io.apiserver.pkg.features
end opaqueInits

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.k8s_io.apiserver.pkg.features.Assumptions]

namespace k8s_io.apiserver.pkg.features

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.k8s_io.apiserver.pkg.features get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.features }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply (_root_.Perennial.k8s_io.apiserver.pkg.util.feature.wp_initialize'_lb _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  wp_apply (opaqueInitsOk defaultVersionedKubernetesFeatureGates.init (by mem_tac))
  ihave #Hfi : (_root_.Perennial.k8s_io.apiserver.pkg.storage.etcd3.featureInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hd1
  icases Hfi with ⟨%g0, #Hmg, #Hdg⟩
  wp_apply (init_0_ok g0) $$ [] as #Hgate
  · iframe #
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
    (Hinit : GetIsPkgInitProp pkg_id.k8s_io.apiserver.pkg.features get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.features }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end k8s_io.apiserver.pkg.features

end init

end Perennial
