/-
Package initialization of `google_golang_org.grpc`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer initializes its imports and runs the untranslated
initializers of its variables (`X.init`, axioms of the translation), which the
trust-boundary axiom `opaqueInitsOk` says run without panicking.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Perennial.Proof.context.Link
public import Proof.google_golang_org.grpc.metadata.Init
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
namespace google_golang_org.grpc
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `google_golang_org.grpc`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([DefaultBackoffConfig.init,
        noOpRegisterHealthListenerFn.init,
        unaryStreamDesc.init,
        ErrClientConnClosing.init,
        errConnDrain.init,
        errConnClosing.init,
        errConnIdling.init,
        invalidDefaultServiceConfigErrPrefix.init,
        PickFirstBalancerName.init,
        errNoTransportSecurity.init,
        errTransportCredsAndBundle.init,
        errNoTransportCredsInBundle.init,
        errTransportCredentialsMissing.init,
        disconnectionsMetric.init,
        connectionAttemptsSucceededMetric.init,
        connectionAttemptsFailedMetric.init,
        openConnectionsMetric.init,
        «_».init,
        ErrClientConnTimeout.init,
        «_».init,
        «_».init,
        errContextCanceled.init,
        errContextDeadline.init,
        statusOK.init,
        logger.init,
        defaultServerOptions.init,
        ErrServerStopped.init,
        «_».init,
        errDuplicatedName.init,
        errEmptyServiceNonEmptyMethod.init,
        metadataFromOutgoingContextRaw.init,
        emptyMethodConfig.init,
        «_».init,
        «_».init,
        «_».init,
        «_».init,
        «_».init,
        «_».init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

end google_golang_org.grpc
end opaqueInits

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.google_golang_org.grpc.Assumptions]
variable [_root_.Perennial.context.ErrorStringIsError]
  [_root_.Perennial.context.DeadlineExceededIsError]

namespace google_golang_org.grpc

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.google_golang_org.grpc get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply (_root_.Perennial.google_golang_org.grpc.metadata.wp_initialize'_lb _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.context _root_.Perennial.context.initialize'
      EtcdGrove.ExternalInit.context _root_.Perennial.context.wp_initialize' _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  wp_apply (opaqueInitsOk DefaultBackoffConfig.init (by mem_tac))
  wp_apply (opaqueInitsOk noOpRegisterHealthListenerFn.init (by mem_tac))
  wp_apply (opaqueInitsOk unaryStreamDesc.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrClientConnClosing.init (by mem_tac))
  wp_apply (opaqueInitsOk errConnDrain.init (by mem_tac))
  wp_apply (opaqueInitsOk errConnClosing.init (by mem_tac))
  wp_apply (opaqueInitsOk errConnIdling.init (by mem_tac))
  wp_apply (opaqueInitsOk invalidDefaultServiceConfigErrPrefix.init (by mem_tac))
  wp_apply (opaqueInitsOk PickFirstBalancerName.init (by mem_tac))
  wp_apply (opaqueInitsOk errNoTransportSecurity.init (by mem_tac))
  wp_apply (opaqueInitsOk errTransportCredsAndBundle.init (by mem_tac))
  wp_apply (opaqueInitsOk errNoTransportCredsInBundle.init (by mem_tac))
  wp_apply (opaqueInitsOk errTransportCredentialsMissing.init (by mem_tac))
  wp_apply (opaqueInitsOk disconnectionsMetric.init (by mem_tac))
  wp_apply (opaqueInitsOk connectionAttemptsSucceededMetric.init (by mem_tac))
  wp_apply (opaqueInitsOk connectionAttemptsFailedMetric.init (by mem_tac))
  wp_apply (opaqueInitsOk openConnectionsMetric.init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk ErrClientConnTimeout.init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk errContextCanceled.init (by mem_tac))
  wp_apply (opaqueInitsOk errContextDeadline.init (by mem_tac))
  wp_apply (opaqueInitsOk statusOK.init (by mem_tac))
  wp_apply (opaqueInitsOk logger.init (by mem_tac))
  wp_apply (opaqueInitsOk defaultServerOptions.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrServerStopped.init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk errDuplicatedName.init (by mem_tac))
  wp_apply (opaqueInitsOk errEmptyServiceNonEmptyMethod.init (by mem_tac))
  wp_apply (opaqueInitsOk metadataFromOutgoingContextRaw.init (by mem_tac))
  wp_apply (opaqueInitsOk emptyMethodConfig.init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  iframe Hown
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.google_golang_org.grpc get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end google_golang_org.grpc

end init

end Perennial
