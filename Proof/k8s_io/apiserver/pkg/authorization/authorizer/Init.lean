/-
Package initialization of `k8s_io.apiserver.pkg.authorization.authorizer`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`authorizerInit`, `authorizer/Base.lean`): `ErrorConditionEvaluationNotSupported`
holds some error, read-only for good. Its initializer allocates it, initializes its imports and runs
its translated initializers: the interface assertions `var _ Condition = GenericCondition{}` and
`var _ Authorizer = AuthorizerFunc(nil)` (conversions to interfaces) and `errors.New(...)`
(Perennial's `errors.wp_New`, `interfaces.go`).
-/
module

public import Proof.k8s_io.apiserver.pkg.authorization.authorizer.Base
public import Perennial.Proof.context.Link
public import Perennial.Proof.errors.Link
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.iter.Link
public import Perennial.Proof.slices.Link
public import Perennial.Proof.strings.Link
public import Proof.k8s_io.apimachinery.pkg.fields.Init
public import Proof.k8s_io.apimachinery.pkg.labels.Init
public import Proof.k8s_io.apimachinery.pkg.runtime.Init
public import Proof.k8s_io.apimachinery.pkg.runtime.schema.Init
public import Proof.k8s_io.apimachinery.pkg.util.errors.Init
public import Proof.k8s_io.apimachinery.pkg.util.sets.Init
public import Proof.k8s_io.apimachinery.pkg.util.validation.Init
public import Proof.k8s_io.apimachinery.pkg.util.validation.field.Init
public import Proof.k8s_io.apiserver.pkg.authentication.user.Init
public import Proof.net.http.Init
public import Perennial.Proof.errors.Link
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
variable [package_sem : _root_.Perennial.k8s_io.apiserver.pkg.authorization.authorizer.Assumptions]

namespace k8s_io.apiserver.pkg.authorization.authorizer

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.k8s_io.apiserver.pkg.authorization.authorizer get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.authorization.authorizer }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrorConditionEvaluationNotSupported _ as HErrorConditionEvaluationNotSupported
  wp_apply (_root_.Perennial.k8s_io.apiserver.pkg.authentication.user.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd16⟩
  wp_apply (_root_.Perennial.k8s_io.apimachinery.pkg.runtime.schema.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd15⟩
  wp_apply (_root_.Perennial.k8s_io.apimachinery.pkg.runtime.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd14⟩
  wp_apply (_root_.Perennial.k8s_io.apimachinery.pkg.labels.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd13⟩
  wp_apply (_root_.Perennial.k8s_io.apimachinery.pkg.fields.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd12⟩
  wp_apply (_root_.Perennial.net.http.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd11⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.errors _root_.Perennial.errors.initialize'
      EtcdGrove.ExternalInit.errors _root_.Perennial.errors.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd10⟩
  wp_apply (_root_.Perennial.k8s_io.apimachinery.pkg.util.validation.field.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd9⟩
  wp_apply (_root_.Perennial.k8s_io.apimachinery.pkg.util.validation.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd8⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.slices _root_.Perennial.slices.initialize'
      EtcdGrove.ExternalInit.slices _root_.Perennial.slices.wp_initialize' _ Hinit.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd7⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.context _root_.Perennial.context.initialize'
      EtcdGrove.ExternalInit.context _root_.Perennial.context.wp_initialize' _ Hinit.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd6⟩
  wp_apply (_root_.Perennial.k8s_io.apimachinery.pkg.util.sets.wp_initialize'_lb _ Hinit.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd5⟩
  wp_apply (_root_.Perennial.k8s_io.apimachinery.pkg.util.errors.wp_initialize'_lb _ Hinit.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.strings _root_.Perennial.strings.initialize'
      EtcdGrove.ExternalInit.strings _root_.Perennial.strings.wp_initialize' _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.iter _root_.Perennial.iter.initialize'
      EtcdGrove.ExternalInit.iter _root_.Perennial.iter.wp_initialize' _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.fmt _root_.Perennial.fmt.initialize'
      EtcdGrove.ExternalInit.fmt _root_.Perennial.fmt.wp_initialize' _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of ErrorConditionEvaluationNotSupported))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New as %xE -
  try wp_auto
  ipersist HErrorConditionEvaluationNotSupported
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish
  imodintro
  unfold authorizerInit
  iexists _; iexact HErrorConditionEvaluationNotSupported

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.k8s_io.apiserver.pkg.authorization.authorizer get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.authorization.authorizer }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end k8s_io.apiserver.pkg.authorization.authorizer

end init

end Perennial
