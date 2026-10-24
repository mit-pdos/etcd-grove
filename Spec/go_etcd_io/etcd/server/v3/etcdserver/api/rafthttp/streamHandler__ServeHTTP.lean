/-
`(*streamHandler).ServeHTTP(w, r)` (`http.go`; rafthttp stage 5e-2): the writing end of a stream,
which answers a stream request with `200` and hands the connection to the peer's stream writer.
Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Peer
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.CloseNotifier

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **A stream handler `h` of the address `a`** (persistent), lending each invocation `Rs`: its
fields read-only, its logger not `nil`, the member it serves owning `a`; its transport's id; its
raft (`IsIDRemoved`, with `Rs`); its peer getter (`Get` of an id, borrowing `Rs`, which holds a
reader's token of the transport's lock, returns `nil` or the peer of that id, with its stream
writers: stage 6 proves it of `Transport`); its transport's `AddRemote`
(returns); and `RaftStreamPrefix`'s value (`streamType.endpoint`'s). -/
def streamHandlerOk (Rh : RaftHttp GF) (a : GoString) (γd : GName) (Rs : IProp GF) (h : Loc) :
    IProp GF :=
  iprop(∃ (hv : rafthttp.streamHandler) (gi : GoInterfaceOk), h ↦□ hv ∗
    ⌜hv.lg' ≠ null ∧ Rh.owner a = hv.id' ∧ hv.peerGetter' = GoInterface.ok gi⌝ ∗
    hv.tr'.[rafthttp.Transport, go!"ID"] ↦□ hv.id' ∗
    □ netRaftOk Rh.γn hv.id' γd Rs hv.r' ∗
    □ (∀ pid : w64, {{ Rs }}
        (App (Val #(methods gi.ty go!"Get" gi.v)) (Val #pid))
      {{ (pi : GoInterface), RET #pi; Rs ∗ (⌜pi = GoInterface.nil⌝ ∨
          ∃ pl : Loc, ⌜pi = interface.mkOk (go.GoType.PointerType rafthttp.peer.ty) #pl⌝ ∗
            peerStreams Rh hv.id' pid pl) }}) ∗
    □ (∀ (pid : w64) (sl : GoSlice) (us : List GoString),
      {{ sl ↦* us ∗ ⌜Rh.member pid ∧ pid ≠ hv.id'⌝ }}
        (App (App (Val (hv.tr' @!! go.GoType.PointerType rafthttp.Transport.ty @!! go!"AddRemote"))
          (Val #pid)) (Val #sl))
      {{ RET #(); True }}) ∗
    globalAddr rafthttp.RaftStreamPrefix ↦□ go!"/raft/stream")

set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 16384 in
instance streamHandlerOk_persistent (Rh : RaftHttp GF) (a : GoString) (γd : GName) (Rs : IProp GF)
    (h : Loc) : Persistent (streamHandlerOk Rh a γd Rs h) := by
  unfold streamHandlerOk; infer_instance

end defs

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`h.ServeHTTP(w, r)`** of a request to `a` routed to the stream prefix (so not of the
prober's path), as `http.handlerFor`
hands it: it returns (or panics, on a peer's malformed version header) with the borrowed `Rs` and
its response writer back (`http.handlerDone`). A stream request it answers with `200` and hands to
the peer's stream writer of its type (`attachOutgoingConn`), waiting until the connection is
closed, which gives the writer back. -/
abbrev rafthttp.streamHandler.ServeHTTP.spec : Prop :=
  ∀ (Rh : RaftHttp GF) (a : GoString) (γd : GName) (Rs : IProp GF) (h : Loc) (wi : GoInterfaceOk)
    (r : Loc) (R : http.HReq) (γk : GName) (rd : GoInterface),
  R.host = a → R.path ≠ probingPath →
  ⊢ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp -∗
    streamHandlerOk Rh a γd Rs h -∗
    http.reqAt r R rd -∗ □ (raftProto Rh).req R γk -∗ http.reqTicket γk -∗
    http.bodyReader rd R [] -∗ http.respWriter (raftHttpNet Rh) (GoInterface.ok wi) a R γk none [] -∗
    http.respHdrs (GoInterface.ok wi) [] -∗
    ⌜go.typeSetContains wi.ty net.http.Flusher.ty = true⌝ -∗ Rs -∗
    WP (App (App (Val (h @!! go.GoType.PointerType rafthttp.streamHandler.ty @!! go!"ServeHTTP"))
      (Val #(GoInterface.ok wi))) (Val #r))
      {{ v, Rs ∗ http.handlerDone (raftHttpNet Rh) (GoInterface.ok wi) a R γk v }}

end spec

end EtcdGrove
end Perennial
