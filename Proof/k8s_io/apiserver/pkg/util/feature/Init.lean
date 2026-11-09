/-
Package initialization of `k8s_io.apiserver.pkg.util.feature`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`featureInit`, `storage/etcd3/Base.lean`): `DefaultMutableFeatureGate` and
`DefaultFeatureGate` hold the same feature gate. Its initializer initializes its import
(`component-base/featuregate`, names-only) and runs its variables' untranslated initializers
(`feature_gate.go`); the trust-boundary axioms `DefaultMutableFeatureGate_init`
(`featuregate.NewFeatureGate()`: a gate) and `DefaultFeatureGate_init` (`DefaultFeatureGate =
DefaultMutableFeatureGate`: the same gate) state them. (Sweep repairs 1, B5, 2026-11-08: until then
`DefaultFeatureGate_init` gave a gate whose `Enabled` answered any `bool` for any feature, false of an
unregistered one, and `DefaultMutableFeatureGate` was `opaqueInitsOk`'s, unlinked; the gate's specs
are now `features`' registration's, `features.init_0_ok`.)
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `DefaultMutableFeatureGate = featuregate.NewFeatureGate()` (`feature_gate.go`): a feature gate, no Kubernetes feature registered yet (`features`' `init` registers them, `features.init_0_ok`). -/
axiom DefaultMutableFeatureGate_init :
    {{ (True : IProp GF) }} (App (Val DefaultMutableFeatureGate.init) (Val #()))
    {{ RET #(); ∃ g : GoInterfaceOk, globalAddr DefaultMutableFeatureGate ↦ GoInterface.ok g }}

/-- `DefaultFeatureGate = DefaultMutableFeatureGate` (`feature_gate.go`): the same gate. -/
axiom DefaultFeatureGate_init : ∀ g : GoInterfaceOk,
    {{ (globalAddr DefaultMutableFeatureGate ↦□ GoInterface.ok g : IProp GF) }} (App (Val DefaultFeatureGate.init) (Val #()))
    {{ RET #(); globalAddr DefaultFeatureGate ↦ GoInterface.ok g }}

end k8s_io.apiserver.pkg.util.feature
end opaqueInits

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
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
  wp_apply DefaultMutableFeatureGate_init as ⟨%gDefaultMutableFeatureGate, HDefaultMutableFeatureGate⟩
  ipersist HDefaultMutableFeatureGate
  wp_apply (DefaultFeatureGate_init gDefaultMutableFeatureGate) $$ [] as HDefaultFeatureGate
  · iframe #
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
