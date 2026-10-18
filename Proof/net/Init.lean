/-
Package initialization of `net`
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
namespace net
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `net`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([rfc6724policyTable.init,
        confVal.init,
        netdns.init,
        multipathtcp.init,
        errLameReferral.init,
        errCannotUnmarshalDNSMessage.init,
        errCannotMarshalDNSMessage.init,
        errServerMisbehaving.init,
        errInvalidDNSResponse.init,
        errNoAnswerFromDNSServer.init,
        errServerTemporarilyMisbehaving.init,
        netedns0.init,
        distantFuture.init,
        lookupOrderName.init,
        defaultNS.init,
        getHostname.init,
        testHookLookupIP.init,
        testPreHookSetKeepAlive.init,
        testHookSetKeepAlive.init,
        testHookStepTime.init,
        testHookCanceledDial.init,
        hostsFilePath.init,
        socketFunc.init,
        connectFunc.init,
        listenFunc.init,
        getsockoptIntFunc.init,
        errInvalidInterface.init,
        errInvalidInterfaceIndex.init,
        errInvalidInterfaceName.init,
        errNoSuchInterface.init,
        errNoSuchMulticastInterface.init,
        flagNames.init,
        zoneCache.init,
        v4InV6Prefix.init,
        IPv4bcast.init,
        IPv4allsys.init,
        IPv4allrouter.init,
        IPv4zero.init,
        IPv6zero.init,
        IPv6unspecified.init,
        IPv6loopback.init,
        IPv6interfacelocalallnodes.init,
        IPv6linklocalallnodes.init,
        IPv6linklocalallrouters.init,
        classAMask.init,
        classBMask.init,
        classCMask.init,
        protocols.init,
        services.init,
        DefaultResolver.init,
        «_».init,
        errMalformedDNSRecordsDetail.init,
        readProtocolsOnce.init,
        errNoSuitableAddress.init,
        errMissingAddress.init,
        errCanceled.init,
        ErrWriteToConnected.init,
        aLongTimeAgo.init,
        noDeadline.init,
        noCancel.init,
        «_».init,
        errTimeout.init,
        errNoSuchHost.init,
        errUnknownPort.init,
        errClosed.init,
        ErrClosed.init,
        «_».init,
        «_».init,
        pollSplice.init,
        _cgo_77133bf98b3a_C2func_getaddrinfo.init,
        _cgo_77133bf98b3a_C2func_getnameinfo.init,
        _cgo_77133bf98b3a_Cfunc_free.init,
        _cgo_77133bf98b3a_Cfunc_freeaddrinfo.init,
        _cgo_77133bf98b3a_Cfunc_gai_strerror.init,
        _cgo_77133bf98b3a_Cfunc_getaddrinfo.init,
        _cgo_77133bf98b3a_Cfunc_getnameinfo.init,
        _cgo_77133bf98b3a_Cfunc_res_search.init,
        _cgo_77133bf98b3a_Cfunc__Cmalloc.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

end net
end opaqueInits

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.net.Assumptions]

namespace net

set_option maxHeartbeats 8000000 in
theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.net get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.net }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply (opaqueInitsOk rfc6724policyTable.init (by mem_tac))
  wp_apply (opaqueInitsOk confVal.init (by mem_tac))
  wp_apply (opaqueInitsOk netdns.init (by mem_tac))
  wp_apply (opaqueInitsOk multipathtcp.init (by mem_tac))
  wp_apply (opaqueInitsOk errLameReferral.init (by mem_tac))
  wp_apply (opaqueInitsOk errCannotUnmarshalDNSMessage.init (by mem_tac))
  wp_apply (opaqueInitsOk errCannotMarshalDNSMessage.init (by mem_tac))
  wp_apply (opaqueInitsOk errServerMisbehaving.init (by mem_tac))
  wp_apply (opaqueInitsOk errInvalidDNSResponse.init (by mem_tac))
  wp_apply (opaqueInitsOk errNoAnswerFromDNSServer.init (by mem_tac))
  wp_apply (opaqueInitsOk errServerTemporarilyMisbehaving.init (by mem_tac))
  wp_apply (opaqueInitsOk netedns0.init (by mem_tac))
  wp_apply (opaqueInitsOk distantFuture.init (by mem_tac))
  wp_apply (opaqueInitsOk lookupOrderName.init (by mem_tac))
  wp_apply (opaqueInitsOk defaultNS.init (by mem_tac))
  wp_apply (opaqueInitsOk getHostname.init (by mem_tac))
  wp_apply (opaqueInitsOk testHookLookupIP.init (by mem_tac))
  wp_apply (opaqueInitsOk testPreHookSetKeepAlive.init (by mem_tac))
  wp_apply (opaqueInitsOk testHookSetKeepAlive.init (by mem_tac))
  wp_apply (opaqueInitsOk testHookStepTime.init (by mem_tac))
  wp_apply (opaqueInitsOk testHookCanceledDial.init (by mem_tac))
  wp_apply (opaqueInitsOk hostsFilePath.init (by mem_tac))
  wp_apply (opaqueInitsOk socketFunc.init (by mem_tac))
  wp_apply (opaqueInitsOk connectFunc.init (by mem_tac))
  wp_apply (opaqueInitsOk listenFunc.init (by mem_tac))
  wp_apply (opaqueInitsOk getsockoptIntFunc.init (by mem_tac))
  wp_apply (opaqueInitsOk errInvalidInterface.init (by mem_tac))
  wp_apply (opaqueInitsOk errInvalidInterfaceIndex.init (by mem_tac))
  wp_apply (opaqueInitsOk errInvalidInterfaceName.init (by mem_tac))
  wp_apply (opaqueInitsOk errNoSuchInterface.init (by mem_tac))
  wp_apply (opaqueInitsOk errNoSuchMulticastInterface.init (by mem_tac))
  wp_apply (opaqueInitsOk flagNames.init (by mem_tac))
  wp_apply (opaqueInitsOk zoneCache.init (by mem_tac))
  wp_apply (opaqueInitsOk v4InV6Prefix.init (by mem_tac))
  wp_apply (opaqueInitsOk IPv4bcast.init (by mem_tac))
  wp_apply (opaqueInitsOk IPv4allsys.init (by mem_tac))
  wp_apply (opaqueInitsOk IPv4allrouter.init (by mem_tac))
  wp_apply (opaqueInitsOk IPv4zero.init (by mem_tac))
  wp_apply (opaqueInitsOk IPv6zero.init (by mem_tac))
  wp_apply (opaqueInitsOk IPv6unspecified.init (by mem_tac))
  wp_apply (opaqueInitsOk IPv6loopback.init (by mem_tac))
  wp_apply (opaqueInitsOk IPv6interfacelocalallnodes.init (by mem_tac))
  wp_apply (opaqueInitsOk IPv6linklocalallnodes.init (by mem_tac))
  wp_apply (opaqueInitsOk IPv6linklocalallrouters.init (by mem_tac))
  wp_apply (opaqueInitsOk classAMask.init (by mem_tac))
  wp_apply (opaqueInitsOk classBMask.init (by mem_tac))
  wp_apply (opaqueInitsOk classCMask.init (by mem_tac))
  wp_apply (opaqueInitsOk protocols.init (by mem_tac))
  wp_apply (opaqueInitsOk services.init (by mem_tac))
  wp_apply (opaqueInitsOk DefaultResolver.init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk errMalformedDNSRecordsDetail.init (by mem_tac))
  wp_apply (opaqueInitsOk readProtocolsOnce.init (by mem_tac))
  wp_apply (opaqueInitsOk errNoSuitableAddress.init (by mem_tac))
  wp_apply (opaqueInitsOk errMissingAddress.init (by mem_tac))
  wp_apply (opaqueInitsOk errCanceled.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrWriteToConnected.init (by mem_tac))
  wp_apply (opaqueInitsOk aLongTimeAgo.init (by mem_tac))
  wp_apply (opaqueInitsOk noDeadline.init (by mem_tac))
  wp_apply (opaqueInitsOk noCancel.init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk errTimeout.init (by mem_tac))
  wp_apply (opaqueInitsOk errNoSuchHost.init (by mem_tac))
  wp_apply (opaqueInitsOk errUnknownPort.init (by mem_tac))
  wp_apply (opaqueInitsOk errClosed.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrClosed.init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk pollSplice.init (by mem_tac))
  wp_apply (opaqueInitsOk _cgo_77133bf98b3a_C2func_getaddrinfo.init (by mem_tac))
  wp_apply (opaqueInitsOk _cgo_77133bf98b3a_C2func_getnameinfo.init (by mem_tac))
  wp_apply (opaqueInitsOk _cgo_77133bf98b3a_Cfunc_free.init (by mem_tac))
  wp_apply (opaqueInitsOk _cgo_77133bf98b3a_Cfunc_freeaddrinfo.init (by mem_tac))
  wp_apply (opaqueInitsOk _cgo_77133bf98b3a_Cfunc_gai_strerror.init (by mem_tac))
  wp_apply (opaqueInitsOk _cgo_77133bf98b3a_Cfunc_getaddrinfo.init (by mem_tac))
  wp_apply (opaqueInitsOk _cgo_77133bf98b3a_Cfunc_getnameinfo.init (by mem_tac))
  wp_apply (opaqueInitsOk _cgo_77133bf98b3a_Cfunc_res_search.init (by mem_tac))
  wp_apply (opaqueInitsOk _cgo_77133bf98b3a_Cfunc__Cmalloc.init (by mem_tac))
  iframe Hown
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.net get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.net }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end net

end init

end Perennial
