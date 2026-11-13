/-
Package initialization of `net`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer initializes its imports and runs the trusted
initializers of its variables (`X.init`, models in `TrustedCode/` that do nothing).
-/
module

public import NetTcp.Proof.net.Base
public import Perennial.Proof.io.Link
public import Perennial.Proof.time.Link
public import NetTcp.Proof.runtime.PkgInitExt

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
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.io _root_.Perennial.io.initialize'
      EtcdGrove.ExternalInit.io _root_.Perennial.io.wp_initialize' _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.time _root_.Perennial.time.initialize'
      EtcdGrove.ExternalInit.time _root_.Perennial.time.wp_initialize' _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  wp_call  -- rfc6724policyTable: its trusted initializer does nothing
  wp_call  -- confVal: its trusted initializer does nothing
  wp_call  -- netdns: its trusted initializer does nothing
  wp_call  -- multipathtcp: its trusted initializer does nothing
  wp_call  -- errLameReferral: its trusted initializer does nothing
  wp_call  -- errCannotUnmarshalDNSMessage: its trusted initializer does nothing
  wp_call  -- errCannotMarshalDNSMessage: its trusted initializer does nothing
  wp_call  -- errServerMisbehaving: its trusted initializer does nothing
  wp_call  -- errInvalidDNSResponse: its trusted initializer does nothing
  wp_call  -- errNoAnswerFromDNSServer: its trusted initializer does nothing
  wp_call  -- errServerTemporarilyMisbehaving: its trusted initializer does nothing
  wp_call  -- netedns0: its trusted initializer does nothing
  wp_call  -- distantFuture: its trusted initializer does nothing
  wp_call  -- lookupOrderName: its trusted initializer does nothing
  wp_call  -- defaultNS: its trusted initializer does nothing
  wp_call  -- getHostname: its trusted initializer does nothing
  wp_call  -- testHookLookupIP: its trusted initializer does nothing
  wp_call  -- testPreHookSetKeepAlive: its trusted initializer does nothing
  wp_call  -- testHookSetKeepAlive: its trusted initializer does nothing
  wp_call  -- testHookStepTime: its trusted initializer does nothing
  wp_call  -- testHookCanceledDial: its trusted initializer does nothing
  wp_call  -- hostsFilePath: its trusted initializer does nothing
  wp_call  -- socketFunc: its trusted initializer does nothing
  wp_call  -- connectFunc: its trusted initializer does nothing
  wp_call  -- listenFunc: its trusted initializer does nothing
  wp_call  -- getsockoptIntFunc: its trusted initializer does nothing
  wp_call  -- errInvalidInterface: its trusted initializer does nothing
  wp_call  -- errInvalidInterfaceIndex: its trusted initializer does nothing
  wp_call  -- errInvalidInterfaceName: its trusted initializer does nothing
  wp_call  -- errNoSuchInterface: its trusted initializer does nothing
  wp_call  -- errNoSuchMulticastInterface: its trusted initializer does nothing
  wp_call  -- flagNames: its trusted initializer does nothing
  wp_call  -- zoneCache: its trusted initializer does nothing
  wp_call  -- v4InV6Prefix: its trusted initializer does nothing
  wp_call  -- IPv4bcast: its trusted initializer does nothing
  wp_call  -- IPv4allsys: its trusted initializer does nothing
  wp_call  -- IPv4allrouter: its trusted initializer does nothing
  wp_call  -- IPv4zero: its trusted initializer does nothing
  wp_call  -- IPv6zero: its trusted initializer does nothing
  wp_call  -- IPv6unspecified: its trusted initializer does nothing
  wp_call  -- IPv6loopback: its trusted initializer does nothing
  wp_call  -- IPv6interfacelocalallnodes: its trusted initializer does nothing
  wp_call  -- IPv6linklocalallnodes: its trusted initializer does nothing
  wp_call  -- IPv6linklocalallrouters: its trusted initializer does nothing
  wp_call  -- classAMask: its trusted initializer does nothing
  wp_call  -- classBMask: its trusted initializer does nothing
  wp_call  -- classCMask: its trusted initializer does nothing
  wp_call  -- protocols: its trusted initializer does nothing
  wp_call  -- services: its trusted initializer does nothing
  wp_call  -- DefaultResolver: its trusted initializer does nothing
  wp_call  -- «_»: its trusted initializer does nothing
  wp_call  -- errMalformedDNSRecordsDetail: its trusted initializer does nothing
  wp_call  -- readProtocolsOnce: its trusted initializer does nothing
  wp_call  -- errNoSuitableAddress: its trusted initializer does nothing
  wp_call  -- errMissingAddress: its trusted initializer does nothing
  wp_call  -- errCanceled: its trusted initializer does nothing
  wp_call  -- ErrWriteToConnected: its trusted initializer does nothing
  wp_call  -- aLongTimeAgo: its trusted initializer does nothing
  wp_call  -- noDeadline: its trusted initializer does nothing
  wp_call  -- noCancel: its trusted initializer does nothing
  wp_call  -- «_»: its trusted initializer does nothing
  wp_call  -- errTimeout: its trusted initializer does nothing
  wp_call  -- errNoSuchHost: its trusted initializer does nothing
  wp_call  -- errUnknownPort: its trusted initializer does nothing
  wp_call  -- errClosed: its trusted initializer does nothing
  wp_call  -- ErrClosed: its trusted initializer does nothing
  wp_call  -- «_»: its trusted initializer does nothing
  wp_call  -- «_»: its trusted initializer does nothing
  wp_call  -- pollSplice: its trusted initializer does nothing
  wp_call  -- _cgo_77133bf98b3a_C2func_getaddrinfo: its trusted initializer does nothing
  wp_call  -- _cgo_77133bf98b3a_C2func_getnameinfo: its trusted initializer does nothing
  wp_call  -- _cgo_77133bf98b3a_Cfunc_free: its trusted initializer does nothing
  wp_call  -- _cgo_77133bf98b3a_Cfunc_freeaddrinfo: its trusted initializer does nothing
  wp_call  -- _cgo_77133bf98b3a_Cfunc_gai_strerror: its trusted initializer does nothing
  wp_call  -- _cgo_77133bf98b3a_Cfunc_getaddrinfo: its trusted initializer does nothing
  wp_call  -- _cgo_77133bf98b3a_Cfunc_getnameinfo: its trusted initializer does nothing
  wp_call  -- _cgo_77133bf98b3a_Cfunc_res_search: its trusted initializer does nothing
  wp_call  -- _cgo_77133bf98b3a_Cfunc__Cmalloc: its trusted initializer does nothing
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
