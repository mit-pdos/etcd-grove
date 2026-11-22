/-
Package initialization of `google_golang_org.grpc`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`grpcInit`, `cache/v3/Base.lean`): `EnableTracing` holds `false` for good. Its
initializer initializes its imports, allocates `EnableTracing` (`var EnableTracing bool`,
`trace.go:33` at v1.84.0: translated, no initializer, so its cell holds `false`), runs the
untranslated initializers of its other variables (`X.init`, axioms of the translation), which the
trust-boundary axiom `opaqueInitsOk` says run without panicking, and its untranslated `init`
functions, which the trust-boundary axiom `initFuncsOk` says return. (Until 2026-11-19 the cell
came from the trust-boundary axiom `DefaultBackoffConfig_init`.) No translated code writes
`EnableTracing`; a program that writes it (etcd's `embed` at log level debug, grpc-proxy `--debug`)
gets no proof: it would need the cell, which `finish` makes persistent.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Perennial.Proof.context.Link
public import Perennial.Proof.io.Link
public import Perennial.Proof.time.Link
public import Proof.google_golang_org.grpc.credentials.Init
public import Proof.google_golang_org.grpc.keepalive.Init
public import Proof.google_golang_org.grpc.metadata.Init
public import Proof.google_golang_org.grpc.peer.Init
public import Proof.google_golang_org.grpc.resolver.Init
public import Proof.google_golang_org.grpc.stats.Init
public import Proof.net.Init
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `google_golang_org.grpc`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([DefaultBackoffConfig.init,
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
        «_».init,
        ErrClientConnTimeout.init,
        «_».init,
        «_».init,
        modelChooseRandom.init,
        grpcStatusDetailsBinHeader.init,
        errStreamDone.init,
        errIllegalHeaderWrite.init,
        errTransportClosing.init,
        transportFailureCodes.init,
        errMalformedFrame.init,
        http2ErrCodeNames.init,
        http2ErrConvTab.init,
        errContextCanceled.init,
        errContextDeadline.init,
        statusOK.init,
        logger.init,
        defaultServerOptions.init,
        ErrServerStopped.init,
        «_».init,
        metadataFromOutgoingContextRaw.init,
        emptyMethodConfig.init,
        «_».init,
        «_».init,
        «_».init,
        «_».init,
        «_».init,
        «_».init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

/-- **The trust boundary: `google_golang_org.grpc`'s untranslated `init` functions return.** Goose
names a package's `func init()`s `init.<k>`, as gc does, and translates them names-only
here, so the model does not unfold them (`@! init.<k>`: the semantics' `functions`, which
the package's `Assumptions` do not constrain for them). Go runs them at program start, and
etcd starts, so each returns without panicking. A fact about the Go code, as the axioms of
other names-only functions (`EtcdGrove.prometheus.MustRegister.wp_proof`). -/
axiom initFuncsOk :
    ∀ f ∈ ([init.«0», init.«1», init.«2»] : List GoString),
    {{ (True : IProp GF) }} (App (Val (@! f)) (Val #())) {{ RET #(); True }}

end google_golang_org.grpc
end opaqueInits

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.google_golang_org.grpc.Assumptions]

namespace google_golang_org.grpc

set_option maxHeartbeats 8000000 in
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
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := Bool) EnableTracing _ as HEnableTracing
  wp_apply (_root_.Perennial.google_golang_org.grpc.peer.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd10⟩
  wp_apply (_root_.Perennial.google_golang_org.grpc.metadata.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd9⟩
  wp_apply (_root_.Perennial.google_golang_org.grpc.stats.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd8⟩
  wp_apply (_root_.Perennial.google_golang_org.grpc.credentials.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd7⟩
  wp_apply (_root_.Perennial.net.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd6⟩
  wp_apply (_root_.Perennial.google_golang_org.grpc.resolver.wp_initialize'_lb _ Hinit.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd5⟩
  wp_apply (_root_.Perennial.google_golang_org.grpc.keepalive.wp_initialize'_lb _ Hinit.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.io _root_.Perennial.io.initialize'
      EtcdGrove.ExternalInit.io _root_.Perennial.io.wp_initialize' _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.context _root_.Perennial.context.initialize'
      EtcdGrove.ExternalInit.context _root_.Perennial.context.wp_initialize' _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.time _root_.Perennial.time.initialize'
      EtcdGrove.ExternalInit.time _root_.Perennial.time.wp_initialize' _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  wp_apply (opaqueInitsOk DefaultBackoffConfig.init (by mem_tac))
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
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk ErrClientConnTimeout.init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk modelChooseRandom.init (by mem_tac))
  wp_apply (opaqueInitsOk grpcStatusDetailsBinHeader.init (by mem_tac))
  wp_apply (opaqueInitsOk errStreamDone.init (by mem_tac))
  wp_apply (opaqueInitsOk errIllegalHeaderWrite.init (by mem_tac))
  wp_apply (opaqueInitsOk errTransportClosing.init (by mem_tac))
  wp_apply (opaqueInitsOk transportFailureCodes.init (by mem_tac))
  wp_apply (opaqueInitsOk errMalformedFrame.init (by mem_tac))
  wp_apply (opaqueInitsOk http2ErrCodeNames.init (by mem_tac))
  wp_apply (opaqueInitsOk http2ErrConvTab.init (by mem_tac))
  wp_apply (opaqueInitsOk errContextCanceled.init (by mem_tac))
  wp_apply (opaqueInitsOk errContextDeadline.init (by mem_tac))
  wp_apply (opaqueInitsOk statusOK.init (by mem_tac))
  wp_apply (opaqueInitsOk logger.init (by mem_tac))
  wp_apply (opaqueInitsOk defaultServerOptions.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrServerStopped.init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk metadataFromOutgoingContextRaw.init (by mem_tac))
  wp_apply (opaqueInitsOk emptyMethodConfig.init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (initFuncsOk init.«0» (by mem_tac))
  wp_apply (initFuncsOk init.«1» (by mem_tac))
  wp_apply (initFuncsOk init.«2» (by mem_tac))
  ipersist HEnableTracing
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
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
