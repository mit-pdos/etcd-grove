/-
Package initialization of `net.http`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer initializes its imports, runs the untranslated
initializers of its variables (`X.init`, axioms of the translation), which the
trust-boundary axiom `opaqueInitsOk` says run without panicking, and its untranslated
`init` functions, which the trust-boundary axiom `initFuncsOk` says return.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply
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
namespace net.http
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `net.http`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([DefaultClient.init,
        ErrSchemeMismatch.init,
        ErrUseLastResponse.init,
        httpcookiemaxnum.init,
        errBlankCookie.init,
        errEqualNotFoundInCookie.init,
        errInvalidCookieName.init,
        errInvalidCookieValue.init,
        errCookieNumLimitExceeded.init,
        cookieNameSanitizer.init,
        sentinelHandler.init,
        errCrossOriginRequest.init,
        errCrossOriginRequestFromOldBrowser.init,
        errInvalidUnsafePath.init,
        httpservecontentkeepheaders.init,
        errSeeker.init,
        errNoOverlap.init,
        unixEpochTime.init,
        errMissingSeek.init,
        errMissingReadDir.init,
        httpservecontentmaxranges.init,
        timeFormats.init,
        headerNewlineToSpace.init,
        headerSorterPool.init,
        aLongTimeAgo.init,
        NoBody.init,
        «_».init,
        «_».init,
        «_».init,
        «_».init,
        «_».init,
        maxSlice.init,
        ErrMissingFile.init,
        ErrNotSupported.init,
        ErrUnexpectedTrailer.init,
        ErrMissingBoundary.init,
        ErrNotMultipart.init,
        ErrHeaderTooLong.init,
        ErrShortBody.init,
        ErrMissingContentLength.init,
        reqWriteExcludeHeader.init,
        ErrNoCookie.init,
        multipartByReader.init,
        errMissingHost.init,
        respExcludeHeader.init,
        ErrNoLocation.init,
        httpmuxgo121.init,
        ErrBodyNotAllowed.init,
        ErrHijacked.init,
        ErrContentLength.init,
        ErrWriteAfterFlush.init,
        ServerContextKey.init,
        LocalAddrContextKey.init,
        crlf.init,
        colonSpace.init,
        copyBufPool.init,
        errTooLarge.init,
        extraHeaderKeys.init,
        headerContentLength.init,
        headerDate.init,
        rstAvoidanceDelay.init,
        «_».init,
        ErrAbortHandler.init,
        htmlReplacer.init,
        DefaultServeMux.init,
        stateName.init,
        ErrServerClosed.init,
        http2server.init,
        ErrHandlerTimeout.init,
        «_».init,
        uniqNameNext.init,
        socksnoDeadline.init,
        socksaLongTimeAgo.init,
        ErrLineTooLong.init,
        suppressedHeaders304.init,
        suppressedHeadersNoBody.init,
        excludedHeadersNoBody.init,
        ErrBodyReadAfterClose.init,
        singleCRLF.init,
        doubleCRLF.init,
        errTrailerEOF.init,
        httplaxcontentlength.init,
        nopCloserType.init,
        nopCloserWriterToType.init,
        http2client.init,
        errCannotRewind.init,
        ErrSkipAltProtocol.init,
        DefaultTransport.init,
        errKeepAlivesDisabled.init,
        errConnBroken.init,
        errCloseIdle.init,
        errTooManyIdle.init,
        errTooManyIdleHost.init,
        errCloseIdleConns.init,
        errReadLoopExiting.init,
        errIdleConnTimeout.init,
        errServerClosedIdle.init,
        testHookProxyConnectTimeout.init,
        «_».init,
        errCallerOwnsConn.init,
        errClosedEarly.init,
        maxWriteWaitBeforeConnReuse.init,
        errTimeout.init,
        errRequestCanceled.init,
        errRequestCanceledConn.init,
        errRequestDone.init,
        testHookEnterRoundTrip.init,
        testHookWaitResLoop.init,
        testHookRoundTripRetried.init,
        testHookPrePendingDial.init,
        testHookPostPendingDial.init,
        testHookMu.init,
        testHookReadLoopBeforeNextRead.init,
        errReadOnClosedResBody.init,
        errConcurrentReadOnResBody.init,
        gzipPool.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

/-- **The trust boundary: `net.http`'s untranslated `init` functions return.** Goose
names a package's `func init()`s `init.<k>`, as gc does, and translates them names-only
here, so the model does not unfold them (`@! init.<k>`: the semantics' `functions`, which
the package's `Assumptions` do not constrain for them). Go runs them at program start, and
etcd starts, so each returns without panicking. A fact about the Go code, as the axioms of
other names-only functions (`EtcdGrove.prometheus.MustRegister.wp_proof`). -/
axiom initFuncsOk :
    ∀ f ∈ ([init.«0», init.«1»] : List GoString),
    {{ (True : IProp GF) }} (App (Val (@! f)) (Val #())) {{ RET #(); True }}

end net.http
end opaqueInits

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.net.http.Assumptions]

namespace net.http

set_option maxHeartbeats 8000000 in
theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.net.http get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.net.http }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply (opaqueInitsOk DefaultClient.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrSchemeMismatch.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrUseLastResponse.init (by mem_tac))
  wp_apply (opaqueInitsOk httpcookiemaxnum.init (by mem_tac))
  wp_apply (opaqueInitsOk errBlankCookie.init (by mem_tac))
  wp_apply (opaqueInitsOk errEqualNotFoundInCookie.init (by mem_tac))
  wp_apply (opaqueInitsOk errInvalidCookieName.init (by mem_tac))
  wp_apply (opaqueInitsOk errInvalidCookieValue.init (by mem_tac))
  wp_apply (opaqueInitsOk errCookieNumLimitExceeded.init (by mem_tac))
  wp_apply (opaqueInitsOk cookieNameSanitizer.init (by mem_tac))
  wp_apply (opaqueInitsOk sentinelHandler.init (by mem_tac))
  wp_apply (opaqueInitsOk errCrossOriginRequest.init (by mem_tac))
  wp_apply (opaqueInitsOk errCrossOriginRequestFromOldBrowser.init (by mem_tac))
  wp_apply (opaqueInitsOk errInvalidUnsafePath.init (by mem_tac))
  wp_apply (opaqueInitsOk httpservecontentkeepheaders.init (by mem_tac))
  wp_apply (opaqueInitsOk errSeeker.init (by mem_tac))
  wp_apply (opaqueInitsOk errNoOverlap.init (by mem_tac))
  wp_apply (opaqueInitsOk unixEpochTime.init (by mem_tac))
  wp_apply (opaqueInitsOk errMissingSeek.init (by mem_tac))
  wp_apply (opaqueInitsOk errMissingReadDir.init (by mem_tac))
  wp_apply (opaqueInitsOk httpservecontentmaxranges.init (by mem_tac))
  wp_apply (opaqueInitsOk timeFormats.init (by mem_tac))
  wp_apply (opaqueInitsOk headerNewlineToSpace.init (by mem_tac))
  wp_apply (opaqueInitsOk headerSorterPool.init (by mem_tac))
  wp_apply (opaqueInitsOk aLongTimeAgo.init (by mem_tac))
  wp_apply (opaqueInitsOk NoBody.init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk maxSlice.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrMissingFile.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrNotSupported.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrUnexpectedTrailer.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrMissingBoundary.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrNotMultipart.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrHeaderTooLong.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrShortBody.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrMissingContentLength.init (by mem_tac))
  wp_apply (opaqueInitsOk reqWriteExcludeHeader.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrNoCookie.init (by mem_tac))
  wp_apply (opaqueInitsOk multipartByReader.init (by mem_tac))
  wp_apply (opaqueInitsOk errMissingHost.init (by mem_tac))
  wp_apply (opaqueInitsOk respExcludeHeader.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrNoLocation.init (by mem_tac))
  wp_apply (opaqueInitsOk httpmuxgo121.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrBodyNotAllowed.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrHijacked.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrContentLength.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrWriteAfterFlush.init (by mem_tac))
  wp_apply (opaqueInitsOk ServerContextKey.init (by mem_tac))
  wp_apply (opaqueInitsOk LocalAddrContextKey.init (by mem_tac))
  wp_apply (opaqueInitsOk crlf.init (by mem_tac))
  wp_apply (opaqueInitsOk colonSpace.init (by mem_tac))
  wp_apply (opaqueInitsOk copyBufPool.init (by mem_tac))
  wp_apply (opaqueInitsOk errTooLarge.init (by mem_tac))
  wp_apply (opaqueInitsOk extraHeaderKeys.init (by mem_tac))
  wp_apply (opaqueInitsOk headerContentLength.init (by mem_tac))
  wp_apply (opaqueInitsOk headerDate.init (by mem_tac))
  wp_apply (opaqueInitsOk rstAvoidanceDelay.init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk ErrAbortHandler.init (by mem_tac))
  wp_apply (opaqueInitsOk htmlReplacer.init (by mem_tac))
  wp_apply (opaqueInitsOk DefaultServeMux.init (by mem_tac))
  wp_apply (opaqueInitsOk stateName.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrServerClosed.init (by mem_tac))
  wp_apply (opaqueInitsOk http2server.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrHandlerTimeout.init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk uniqNameNext.init (by mem_tac))
  wp_apply (opaqueInitsOk socksnoDeadline.init (by mem_tac))
  wp_apply (opaqueInitsOk socksaLongTimeAgo.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrLineTooLong.init (by mem_tac))
  wp_apply (opaqueInitsOk suppressedHeaders304.init (by mem_tac))
  wp_apply (opaqueInitsOk suppressedHeadersNoBody.init (by mem_tac))
  wp_apply (opaqueInitsOk excludedHeadersNoBody.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrBodyReadAfterClose.init (by mem_tac))
  wp_apply (opaqueInitsOk singleCRLF.init (by mem_tac))
  wp_apply (opaqueInitsOk doubleCRLF.init (by mem_tac))
  wp_apply (opaqueInitsOk errTrailerEOF.init (by mem_tac))
  wp_apply (opaqueInitsOk httplaxcontentlength.init (by mem_tac))
  wp_apply (opaqueInitsOk nopCloserType.init (by mem_tac))
  wp_apply (opaqueInitsOk nopCloserWriterToType.init (by mem_tac))
  wp_apply (opaqueInitsOk http2client.init (by mem_tac))
  wp_apply (opaqueInitsOk errCannotRewind.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrSkipAltProtocol.init (by mem_tac))
  wp_apply (opaqueInitsOk DefaultTransport.init (by mem_tac))
  wp_apply (opaqueInitsOk errKeepAlivesDisabled.init (by mem_tac))
  wp_apply (opaqueInitsOk errConnBroken.init (by mem_tac))
  wp_apply (opaqueInitsOk errCloseIdle.init (by mem_tac))
  wp_apply (opaqueInitsOk errTooManyIdle.init (by mem_tac))
  wp_apply (opaqueInitsOk errTooManyIdleHost.init (by mem_tac))
  wp_apply (opaqueInitsOk errCloseIdleConns.init (by mem_tac))
  wp_apply (opaqueInitsOk errReadLoopExiting.init (by mem_tac))
  wp_apply (opaqueInitsOk errIdleConnTimeout.init (by mem_tac))
  wp_apply (opaqueInitsOk errServerClosedIdle.init (by mem_tac))
  wp_apply (opaqueInitsOk testHookProxyConnectTimeout.init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk errCallerOwnsConn.init (by mem_tac))
  wp_apply (opaqueInitsOk errClosedEarly.init (by mem_tac))
  wp_apply (opaqueInitsOk maxWriteWaitBeforeConnReuse.init (by mem_tac))
  wp_apply (opaqueInitsOk errTimeout.init (by mem_tac))
  wp_apply (opaqueInitsOk errRequestCanceled.init (by mem_tac))
  wp_apply (opaqueInitsOk errRequestCanceledConn.init (by mem_tac))
  wp_apply (opaqueInitsOk errRequestDone.init (by mem_tac))
  wp_apply (opaqueInitsOk testHookEnterRoundTrip.init (by mem_tac))
  wp_apply (opaqueInitsOk testHookWaitResLoop.init (by mem_tac))
  wp_apply (opaqueInitsOk testHookRoundTripRetried.init (by mem_tac))
  wp_apply (opaqueInitsOk testHookPrePendingDial.init (by mem_tac))
  wp_apply (opaqueInitsOk testHookPostPendingDial.init (by mem_tac))
  wp_apply (opaqueInitsOk testHookMu.init (by mem_tac))
  wp_apply (opaqueInitsOk testHookReadLoopBeforeNextRead.init (by mem_tac))
  wp_apply (opaqueInitsOk errReadOnClosedResBody.init (by mem_tac))
  wp_apply (opaqueInitsOk errConcurrentReadOnResBody.init (by mem_tac))
  wp_apply (opaqueInitsOk gzipPool.init (by mem_tac))
  wp_apply (initFuncsOk init.«0» (by mem_tac))
  wp_apply (initFuncsOk init.«1» (by mem_tac))
  iframe Hown
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.net.http get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.net.http }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end net.http

end init

end Perennial
