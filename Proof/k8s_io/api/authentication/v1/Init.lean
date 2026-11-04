/-
Package initialization of `k8s_io.api.authentication.v1`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer initializes its imports and runs the untranslated
initializers of its variables (`X.init`, axioms of the translation), which the
trust-boundary axiom `opaqueInitsOk` says run without panicking.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Base
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
namespace k8s_io.api.authentication.v1
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `k8s_io.api.authentication.v1`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([ErrInvalidLengthGenerated.init,
        ErrIntOverflowGenerated.init,
        ErrUnexpectedEndOfGroupGenerated.init,
        SchemeGroupVersion.init,
        SchemeBuilder.init,
        localSchemeBuilder.init,
        AddToScheme.init,
        map_BoundObjectReference.init,
        map_SelfSubjectReview.init,
        map_SelfSubjectReviewStatus.init,
        map_TokenRequest.init,
        map_TokenRequestSpec.init,
        map_TokenRequestStatus.init,
        map_TokenReview.init,
        map_TokenReviewSpec.init,
        map_TokenReviewStatus.init,
        map_UserInfo.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

end k8s_io.api.authentication.v1
end opaqueInits

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.k8s_io.api.authentication.v1.Assumptions]

namespace k8s_io.api.authentication.v1

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.k8s_io.api.authentication.v1 get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.k8s_io.api.authentication.v1 }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply (opaqueInitsOk ErrInvalidLengthGenerated.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrIntOverflowGenerated.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrUnexpectedEndOfGroupGenerated.init (by mem_tac))
  wp_apply (opaqueInitsOk SchemeGroupVersion.init (by mem_tac))
  wp_apply (opaqueInitsOk SchemeBuilder.init (by mem_tac))
  wp_apply (opaqueInitsOk localSchemeBuilder.init (by mem_tac))
  wp_apply (opaqueInitsOk AddToScheme.init (by mem_tac))
  wp_apply (opaqueInitsOk map_BoundObjectReference.init (by mem_tac))
  wp_apply (opaqueInitsOk map_SelfSubjectReview.init (by mem_tac))
  wp_apply (opaqueInitsOk map_SelfSubjectReviewStatus.init (by mem_tac))
  wp_apply (opaqueInitsOk map_TokenRequest.init (by mem_tac))
  wp_apply (opaqueInitsOk map_TokenRequestSpec.init (by mem_tac))
  wp_apply (opaqueInitsOk map_TokenRequestStatus.init (by mem_tac))
  wp_apply (opaqueInitsOk map_TokenReview.init (by mem_tac))
  wp_apply (opaqueInitsOk map_TokenReviewSpec.init (by mem_tac))
  wp_apply (opaqueInitsOk map_TokenReviewStatus.init (by mem_tac))
  wp_apply (opaqueInitsOk map_UserInfo.init (by mem_tac))
  iframe Hown
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.k8s_io.api.authentication.v1 get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.k8s_io.api.authentication.v1 }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end k8s_io.api.authentication.v1

end init

end Perennial
