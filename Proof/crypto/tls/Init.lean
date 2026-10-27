/-
Package initialization of `crypto.tls`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer initializes its imports and runs the untranslated
initializers of its variables (`X.init`, axioms of the translation), which the
trust-boundary axiom `opaqueInitsOk` says run without panicking.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base
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
namespace crypto.tls
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `crypto.tls`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([«_».init,
        alertText.init,
        signaturePadding.init,
        rsaSignatureSchemes.init,
        globalCertCache.init,
        supportedUpToTLS12.init,
        supportedOnlyTLS12.init,
        supportedOnlyTLS13.init,
        cipherSuites.init,
        cipherSuitesTLS13.init,
        cipherSuitesPreferenceOrder.init,
        cipherSuitesPreferenceOrderNoAES.init,
        disabledCipherSuites.init,
        hasGCMAsmAMD64.init,
        hasGCMAsmARM64.init,
        hasGCMAsmS390X.init,
        hasGCMAsmPPC64.init,
        hasAESGCMHardwareSupport.init,
        aesgcmCiphers.init,
        directSigning.init,
        helloRetryRequestRandom.init,
        deprecatedSessionTicketKey.init,
        supportedVersions.init,
        errNoCertificates.init,
        tlssha1.init,
        _SignatureScheme_index_8.init,
        _SignatureScheme_index_9.init,
        _CurveID_index_0.init,
        _CurveID_index_3.init,
        _ClientAuthType_index.init,
        outBufPool.init,
        errShutdown.init,
        errEarlyCloseWrite.init,
        tlsmlkem.init,
        tlssecpmlkem.init,
        defaultCipherSuitesTLS13.init,
        defaultCipherSuitesTLS13NoAES.init,
        allowedSupportedVersionsFIPS.init,
        allowedCurvePreferencesFIPS.init,
        allowedSignatureAlgorithmsFIPS.init,
        allowedCipherSuitesFIPS.init,
        allowedCipherSuitesTLS13FIPS.init,
        errMalformedECHConfigList.init,
        errMalformedECHExt.init,
        errInvalidECHExt.init,
        fips140ems.init,
        tlsmaxrsasize.init,
        errClientKeyExchange.init,
        errServerKeyExchange.init,
        «_».init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

end crypto.tls
end opaqueInits

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.crypto.tls.Assumptions]

namespace crypto.tls

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.crypto.tls get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.crypto.tls }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk alertText.init (by mem_tac))
  wp_apply (opaqueInitsOk signaturePadding.init (by mem_tac))
  wp_apply (opaqueInitsOk rsaSignatureSchemes.init (by mem_tac))
  wp_apply (opaqueInitsOk globalCertCache.init (by mem_tac))
  wp_apply (opaqueInitsOk supportedUpToTLS12.init (by mem_tac))
  wp_apply (opaqueInitsOk supportedOnlyTLS12.init (by mem_tac))
  wp_apply (opaqueInitsOk supportedOnlyTLS13.init (by mem_tac))
  wp_apply (opaqueInitsOk cipherSuites.init (by mem_tac))
  wp_apply (opaqueInitsOk cipherSuitesTLS13.init (by mem_tac))
  wp_apply (opaqueInitsOk cipherSuitesPreferenceOrder.init (by mem_tac))
  wp_apply (opaqueInitsOk cipherSuitesPreferenceOrderNoAES.init (by mem_tac))
  wp_apply (opaqueInitsOk disabledCipherSuites.init (by mem_tac))
  wp_apply (opaqueInitsOk hasGCMAsmAMD64.init (by mem_tac))
  wp_apply (opaqueInitsOk hasGCMAsmARM64.init (by mem_tac))
  wp_apply (opaqueInitsOk hasGCMAsmS390X.init (by mem_tac))
  wp_apply (opaqueInitsOk hasGCMAsmPPC64.init (by mem_tac))
  wp_apply (opaqueInitsOk hasAESGCMHardwareSupport.init (by mem_tac))
  wp_apply (opaqueInitsOk aesgcmCiphers.init (by mem_tac))
  wp_apply (opaqueInitsOk directSigning.init (by mem_tac))
  wp_apply (opaqueInitsOk helloRetryRequestRandom.init (by mem_tac))
  wp_apply (opaqueInitsOk deprecatedSessionTicketKey.init (by mem_tac))
  wp_apply (opaqueInitsOk supportedVersions.init (by mem_tac))
  wp_apply (opaqueInitsOk errNoCertificates.init (by mem_tac))
  wp_apply (opaqueInitsOk tlssha1.init (by mem_tac))
  wp_apply (opaqueInitsOk _SignatureScheme_index_8.init (by mem_tac))
  wp_apply (opaqueInitsOk _SignatureScheme_index_9.init (by mem_tac))
  wp_apply (opaqueInitsOk _CurveID_index_0.init (by mem_tac))
  wp_apply (opaqueInitsOk _CurveID_index_3.init (by mem_tac))
  wp_apply (opaqueInitsOk _ClientAuthType_index.init (by mem_tac))
  wp_apply (opaqueInitsOk outBufPool.init (by mem_tac))
  wp_apply (opaqueInitsOk errShutdown.init (by mem_tac))
  wp_apply (opaqueInitsOk errEarlyCloseWrite.init (by mem_tac))
  wp_apply (opaqueInitsOk tlsmlkem.init (by mem_tac))
  wp_apply (opaqueInitsOk tlssecpmlkem.init (by mem_tac))
  wp_apply (opaqueInitsOk defaultCipherSuitesTLS13.init (by mem_tac))
  wp_apply (opaqueInitsOk defaultCipherSuitesTLS13NoAES.init (by mem_tac))
  wp_apply (opaqueInitsOk allowedSupportedVersionsFIPS.init (by mem_tac))
  wp_apply (opaqueInitsOk allowedCurvePreferencesFIPS.init (by mem_tac))
  wp_apply (opaqueInitsOk allowedSignatureAlgorithmsFIPS.init (by mem_tac))
  wp_apply (opaqueInitsOk allowedCipherSuitesFIPS.init (by mem_tac))
  wp_apply (opaqueInitsOk allowedCipherSuitesTLS13FIPS.init (by mem_tac))
  wp_apply (opaqueInitsOk errMalformedECHConfigList.init (by mem_tac))
  wp_apply (opaqueInitsOk errMalformedECHExt.init (by mem_tac))
  wp_apply (opaqueInitsOk errInvalidECHExt.init (by mem_tac))
  wp_apply (opaqueInitsOk fips140ems.init (by mem_tac))
  wp_apply (opaqueInitsOk tlsmaxrsasize.init (by mem_tac))
  wp_apply (opaqueInitsOk errClientKeyExchange.init (by mem_tac))
  wp_apply (opaqueInitsOk errServerKeyExchange.init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  iframe Hown
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.crypto.tls get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.crypto.tls }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end crypto.tls

end init

end Perennial
