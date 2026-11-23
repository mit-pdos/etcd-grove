/-
Package initialization of `google_golang_org.grpc`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer initializes its imports and runs the trusted
initializers of its variables (`X.init`, models in `TrustedCode/` that do nothing).
-/
module

public import Dsverify.Proof.google_golang_org.grpc.Base
public import Perennial.Proof.context.Link
public import Net.Proof.runtime.PkgInitExt

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
variable [package_sem : _root_.Perennial.google_golang_org.grpc.Assumptions]

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
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.context _root_.Perennial.context.initialize'
      EtcdGrove.ExternalInit.context _root_.Perennial.context.wp_initialize' _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  wp_call  -- DefaultBackoffConfig: its trusted initializer does nothing
  wp_call  -- unaryStreamDesc: its trusted initializer does nothing
  wp_call  -- ErrClientConnClosing: its trusted initializer does nothing
  wp_call  -- errConnDrain: its trusted initializer does nothing
  wp_call  -- errConnClosing: its trusted initializer does nothing
  wp_call  -- errConnIdling: its trusted initializer does nothing
  wp_call  -- invalidDefaultServiceConfigErrPrefix: its trusted initializer does nothing
  wp_call  -- PickFirstBalancerName: its trusted initializer does nothing
  wp_call  -- errNoTransportSecurity: its trusted initializer does nothing
  wp_call  -- errTransportCredsAndBundle: its trusted initializer does nothing
  wp_call  -- errNoTransportCredsInBundle: its trusted initializer does nothing
  wp_call  -- errTransportCredentialsMissing: its trusted initializer does nothing
  wp_call  -- «_»: its trusted initializer does nothing
  wp_call  -- ErrClientConnTimeout: its trusted initializer does nothing
  wp_call  -- «_»: its trusted initializer does nothing
  wp_call  -- «_»: its trusted initializer does nothing
  wp_call  -- modelChooseRandom: its trusted initializer does nothing
  wp_call  -- grpcStatusDetailsBinHeader: its trusted initializer does nothing
  wp_call  -- errStreamDone: its trusted initializer does nothing
  wp_call  -- errIllegalHeaderWrite: its trusted initializer does nothing
  wp_call  -- errTransportClosing: its trusted initializer does nothing
  wp_call  -- transportFailureCodes: its trusted initializer does nothing
  wp_call  -- errMalformedFrame: its trusted initializer does nothing
  wp_call  -- http2ErrCodeNames: its trusted initializer does nothing
  wp_call  -- http2ErrConvTab: its trusted initializer does nothing
  wp_call  -- errContextCanceled: its trusted initializer does nothing
  wp_call  -- errContextDeadline: its trusted initializer does nothing
  wp_call  -- statusOK: its trusted initializer does nothing
  wp_call  -- logger: its trusted initializer does nothing
  wp_call  -- defaultServerOptions: its trusted initializer does nothing
  wp_call  -- ErrServerStopped: its trusted initializer does nothing
  wp_call  -- «_»: its trusted initializer does nothing
  wp_call  -- metadataFromOutgoingContextRaw: its trusted initializer does nothing
  wp_call  -- emptyMethodConfig: its trusted initializer does nothing
  wp_call  -- «_»: its trusted initializer does nothing
  wp_call  -- «_»: its trusted initializer does nothing
  wp_call  -- «_»: its trusted initializer does nothing
  wp_call  -- «_»: its trusted initializer does nothing
  wp_call  -- «_»: its trusted initializer does nothing
  wp_call  -- «_»: its trusted initializer does nothing
  -- the translated init.«0»
  wp_func_call
  wp_call
  try wp_auto
  -- the translated init.«1»
  wp_func_call
  wp_call
  try wp_auto
  -- the translated init.«2»
  wp_func_call
  wp_call
  try wp_auto
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
