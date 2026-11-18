/-
Package initialization of `crypto.tls`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer initializes its imports and runs the untranslated
initializers of its variables (`X.init`, axioms of the translation), which the
trust-boundary axiom `opaqueInitsOk` says run without panicking.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Perennial.Proof.ProofPrelude
public import Perennial.Golang.Theory.Pkg
public import Code.go_etcd_io.raft.v3
public import Code.go_etcd_io.raft.v3.confchange
public import Code.go_etcd_io.raft.v3.raftpb
public import Code.go_etcd_io.raft.v3.tracker
public import Code.google_golang_org.protobuf.proto
public import Code.k8s_io.utils.third_party.forked.golang.btree
public import Perennial.Code.bytes
public import Perennial.Code.cmp
public import Perennial.Code.context
public import Perennial.Code.encoding.binary
public import Perennial.Code.errors
public import Perennial.Code.fmt
public import Perennial.Code.github_com.goose_lang.primitive
public import Perennial.Code.internal.oserror
public import Perennial.Code.internal.stringslite
public import Perennial.Code.io
public import Perennial.Code.iter
public import Perennial.Code.log
public import Perennial.Code.math
public import Perennial.Code.slices
public import Perennial.Code.sort
public import Perennial.Code.strconv
public import Perennial.Code.strings
public import Perennial.Code.sync
public import Perennial.Code.sync.atomic
public import Perennial.Code.time
public import Perennial.Code.«unsafe»

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

end crypto.tls

end init

end Perennial
