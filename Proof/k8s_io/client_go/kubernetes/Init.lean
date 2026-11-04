/-
Package initialization of `k8s_io.client_go.kubernetes`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer initializes its imports (it has no initialized
variable).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Base
public import Proof.k8s_io.client_go.discovery.Init
public import Proof.k8s_io.client_go.kubernetes.typed.admissionregistration.v1.Init
public import Proof.k8s_io.client_go.kubernetes.typed.admissionregistration.v1alpha1.Init
public import Proof.k8s_io.client_go.kubernetes.typed.admissionregistration.v1beta1.Init
public import Proof.k8s_io.client_go.kubernetes.typed.apiserverinternal.v1alpha1.Init
public import Proof.k8s_io.client_go.kubernetes.typed.apps.v1.Init
public import Proof.k8s_io.client_go.kubernetes.typed.apps.v1beta1.Init
public import Proof.k8s_io.client_go.kubernetes.typed.apps.v1beta2.Init
public import Proof.k8s_io.client_go.kubernetes.typed.authentication.v1.Init
public import Proof.k8s_io.client_go.kubernetes.typed.authentication.v1alpha1.Init
public import Proof.k8s_io.client_go.kubernetes.typed.authentication.v1beta1.Init
public import Proof.k8s_io.client_go.kubernetes.typed.authorization.v1.Init
public import Proof.k8s_io.client_go.kubernetes.typed.authorization.v1alpha1.Init
public import Proof.k8s_io.client_go.kubernetes.typed.authorization.v1beta1.Init
public import Proof.k8s_io.client_go.kubernetes.typed.autoscaling.v1.Init
public import Proof.k8s_io.client_go.kubernetes.typed.autoscaling.v2.Init
public import Proof.k8s_io.client_go.kubernetes.typed.batch.v1.Init
public import Proof.k8s_io.client_go.kubernetes.typed.batch.v1beta1.Init
public import Proof.k8s_io.client_go.kubernetes.typed.certificates.v1.Init
public import Proof.k8s_io.client_go.kubernetes.typed.certificates.v1alpha1.Init
public import Proof.k8s_io.client_go.kubernetes.typed.certificates.v1beta1.Init
public import Proof.k8s_io.client_go.kubernetes.typed.coordination.v1.Init
public import Proof.k8s_io.client_go.kubernetes.typed.coordination.v1alpha2.Init
public import Proof.k8s_io.client_go.kubernetes.typed.coordination.v1beta1.Init
public import Proof.k8s_io.client_go.kubernetes.typed.core.v1.Init
public import Proof.k8s_io.client_go.kubernetes.typed.discovery.v1.Init
public import Proof.k8s_io.client_go.kubernetes.typed.discovery.v1beta1.Init
public import Proof.k8s_io.client_go.kubernetes.typed.events.v1.Init
public import Proof.k8s_io.client_go.kubernetes.typed.events.v1beta1.Init
public import Proof.k8s_io.client_go.kubernetes.typed.extensions.v1beta1.Init
public import Proof.k8s_io.client_go.kubernetes.typed.flowcontrol.v1.Init
public import Proof.k8s_io.client_go.kubernetes.typed.flowcontrol.v1beta1.Init
public import Proof.k8s_io.client_go.kubernetes.typed.flowcontrol.v1beta2.Init
public import Proof.k8s_io.client_go.kubernetes.typed.flowcontrol.v1beta3.Init
public import Proof.k8s_io.client_go.kubernetes.typed.lifecycle.v1alpha1.Init
public import Proof.k8s_io.client_go.kubernetes.typed.networking.v1.Init
public import Proof.k8s_io.client_go.kubernetes.typed.networking.v1beta1.Init
public import Proof.k8s_io.client_go.kubernetes.typed.node.v1.Init
public import Proof.k8s_io.client_go.kubernetes.typed.node.v1alpha1.Init
public import Proof.k8s_io.client_go.kubernetes.typed.node.v1beta1.Init
public import Proof.k8s_io.client_go.kubernetes.typed.policy.v1.Init
public import Proof.k8s_io.client_go.kubernetes.typed.policy.v1beta1.Init
public import Proof.k8s_io.client_go.kubernetes.typed.rbac.v1.Init
public import Proof.k8s_io.client_go.kubernetes.typed.rbac.v1alpha1.Init
public import Proof.k8s_io.client_go.kubernetes.typed.rbac.v1beta1.Init
public import Proof.k8s_io.client_go.kubernetes.typed.resource.v1.Init
public import Proof.k8s_io.client_go.kubernetes.typed.resource.v1alpha3.Init
public import Proof.k8s_io.client_go.kubernetes.typed.resource.v1beta1.Init
public import Proof.k8s_io.client_go.kubernetes.typed.resource.v1beta2.Init
public import Proof.k8s_io.client_go.kubernetes.typed.scheduling.v1.Init
public import Proof.k8s_io.client_go.kubernetes.typed.scheduling.v1alpha3.Init
public import Proof.k8s_io.client_go.kubernetes.typed.scheduling.v1beta1.Init
public import Proof.k8s_io.client_go.kubernetes.typed.storage.v1.Init
public import Proof.k8s_io.client_go.kubernetes.typed.storage.v1alpha1.Init
public import Proof.k8s_io.client_go.kubernetes.typed.storage.v1beta1.Init
public import Proof.k8s_io.client_go.kubernetes.typed.storagemigration.v1.Init
public import Proof.k8s_io.client_go.kubernetes.typed.storagemigration.v1beta1.Init
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

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.k8s_io.client_go.kubernetes.Assumptions]

namespace k8s_io.client_go.kubernetes

set_option maxHeartbeats 8000000 in
theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.k8s_io.client_go.kubernetes get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.kubernetes }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply (_root_.Perennial.k8s_io.client_go.kubernetes.typed.storagemigration.v1beta1.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd57⟩
  wp_apply (_root_.Perennial.k8s_io.client_go.kubernetes.typed.storagemigration.v1.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd56⟩
  wp_apply (_root_.Perennial.k8s_io.client_go.kubernetes.typed.storage.v1beta1.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd55⟩
  wp_apply (_root_.Perennial.k8s_io.client_go.kubernetes.typed.storage.v1alpha1.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd54⟩
  wp_apply (_root_.Perennial.k8s_io.client_go.kubernetes.typed.storage.v1.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd53⟩
  wp_apply (_root_.Perennial.k8s_io.client_go.kubernetes.typed.scheduling.v1beta1.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd52⟩
  wp_apply (_root_.Perennial.k8s_io.client_go.kubernetes.typed.scheduling.v1alpha3.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd51⟩
  wp_apply (_root_.Perennial.k8s_io.client_go.kubernetes.typed.scheduling.v1.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd50⟩
  wp_apply (_root_.Perennial.k8s_io.client_go.kubernetes.typed.resource.v1beta2.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd49⟩
  wp_apply (_root_.Perennial.k8s_io.client_go.kubernetes.typed.resource.v1beta1.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd48⟩
  wp_apply (_root_.Perennial.k8s_io.client_go.kubernetes.typed.resource.v1alpha3.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd47⟩
  wp_apply (_root_.Perennial.k8s_io.client_go.kubernetes.typed.resource.v1.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd46⟩
  wp_apply (_root_.Perennial.k8s_io.client_go.kubernetes.typed.rbac.v1beta1.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd45⟩
  wp_apply (_root_.Perennial.k8s_io.client_go.kubernetes.typed.rbac.v1alpha1.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd44⟩
  wp_apply (_root_.Perennial.k8s_io.client_go.kubernetes.typed.rbac.v1.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd43⟩
  wp_apply (_root_.Perennial.k8s_io.client_go.kubernetes.typed.policy.v1beta1.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd42⟩
  wp_apply (_root_.Perennial.k8s_io.client_go.kubernetes.typed.policy.v1.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd41⟩
  wp_apply (_root_.Perennial.k8s_io.client_go.kubernetes.typed.node.v1beta1.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd40⟩
  wp_apply (_root_.Perennial.k8s_io.client_go.kubernetes.typed.node.v1alpha1.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd39⟩
  wp_apply (_root_.Perennial.k8s_io.client_go.kubernetes.typed.node.v1.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd38⟩
  wp_apply (_root_.Perennial.k8s_io.client_go.kubernetes.typed.networking.v1beta1.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd37⟩
  wp_apply (_root_.Perennial.k8s_io.client_go.kubernetes.typed.networking.v1.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd36⟩
  wp_apply (_root_.Perennial.k8s_io.client_go.kubernetes.typed.lifecycle.v1alpha1.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd35⟩
  wp_apply (_root_.Perennial.k8s_io.client_go.kubernetes.typed.flowcontrol.v1beta3.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd34⟩
  wp_apply (_root_.Perennial.k8s_io.client_go.kubernetes.typed.flowcontrol.v1beta2.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd33⟩
  wp_apply (_root_.Perennial.k8s_io.client_go.kubernetes.typed.flowcontrol.v1beta1.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd32⟩
  wp_apply (_root_.Perennial.k8s_io.client_go.kubernetes.typed.flowcontrol.v1.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd31⟩
  wp_apply (_root_.Perennial.k8s_io.client_go.kubernetes.typed.extensions.v1beta1.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd30⟩
  wp_apply (_root_.Perennial.k8s_io.client_go.kubernetes.typed.events.v1beta1.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd29⟩
  wp_apply (_root_.Perennial.k8s_io.client_go.kubernetes.typed.events.v1.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd28⟩
  wp_apply (_root_.Perennial.k8s_io.client_go.kubernetes.typed.discovery.v1beta1.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd27⟩
  wp_apply (_root_.Perennial.k8s_io.client_go.kubernetes.typed.discovery.v1.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd26⟩
  wp_apply (_root_.Perennial.k8s_io.client_go.kubernetes.typed.core.v1.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd25⟩
  wp_apply (_root_.Perennial.k8s_io.client_go.kubernetes.typed.coordination.v1beta1.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd24⟩
  wp_apply (_root_.Perennial.k8s_io.client_go.kubernetes.typed.coordination.v1alpha2.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd23⟩
  wp_apply (_root_.Perennial.k8s_io.client_go.kubernetes.typed.coordination.v1.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd22⟩
  wp_apply (_root_.Perennial.k8s_io.client_go.kubernetes.typed.certificates.v1beta1.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd21⟩
  wp_apply (_root_.Perennial.k8s_io.client_go.kubernetes.typed.certificates.v1alpha1.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd20⟩
  wp_apply (_root_.Perennial.k8s_io.client_go.kubernetes.typed.certificates.v1.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd19⟩
  wp_apply (_root_.Perennial.k8s_io.client_go.kubernetes.typed.batch.v1beta1.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd18⟩
  wp_apply (_root_.Perennial.k8s_io.client_go.kubernetes.typed.batch.v1.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd17⟩
  wp_apply (_root_.Perennial.k8s_io.client_go.kubernetes.typed.autoscaling.v2.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd16⟩
  wp_apply (_root_.Perennial.k8s_io.client_go.kubernetes.typed.autoscaling.v1.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd15⟩
  wp_apply (_root_.Perennial.k8s_io.client_go.kubernetes.typed.authorization.v1beta1.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd14⟩
  wp_apply (_root_.Perennial.k8s_io.client_go.kubernetes.typed.authorization.v1alpha1.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd13⟩
  wp_apply (_root_.Perennial.k8s_io.client_go.kubernetes.typed.authorization.v1.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd12⟩
  wp_apply (_root_.Perennial.k8s_io.client_go.kubernetes.typed.authentication.v1beta1.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd11⟩
  wp_apply (_root_.Perennial.k8s_io.client_go.kubernetes.typed.authentication.v1alpha1.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd10⟩
  wp_apply (_root_.Perennial.k8s_io.client_go.kubernetes.typed.authentication.v1.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd9⟩
  wp_apply (_root_.Perennial.k8s_io.client_go.kubernetes.typed.apps.v1beta2.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd8⟩
  wp_apply (_root_.Perennial.k8s_io.client_go.kubernetes.typed.apps.v1beta1.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd7⟩
  wp_apply (_root_.Perennial.k8s_io.client_go.kubernetes.typed.apps.v1.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd6⟩
  wp_apply (_root_.Perennial.k8s_io.client_go.kubernetes.typed.apiserverinternal.v1alpha1.wp_initialize'_lb _ Hinit.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd5⟩
  wp_apply (_root_.Perennial.k8s_io.client_go.kubernetes.typed.admissionregistration.v1beta1.wp_initialize'_lb _ Hinit.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply (_root_.Perennial.k8s_io.client_go.kubernetes.typed.admissionregistration.v1alpha1.wp_initialize'_lb _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (_root_.Perennial.k8s_io.client_go.kubernetes.typed.admissionregistration.v1.wp_initialize'_lb _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (_root_.Perennial.k8s_io.client_go.discovery.wp_initialize'_lb _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  iframe Hown
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.k8s_io.client_go.kubernetes get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.kubernetes }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end k8s_io.client_go.kubernetes

end init

end Perennial
