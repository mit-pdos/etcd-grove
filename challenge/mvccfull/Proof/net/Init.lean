/-
Package initialization of `net`
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
namespace net
variable [GooseExts] [GooseSemantics] [GooseInterp]
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.net.Assumptions]

namespace net

end net

end init

end Perennial
