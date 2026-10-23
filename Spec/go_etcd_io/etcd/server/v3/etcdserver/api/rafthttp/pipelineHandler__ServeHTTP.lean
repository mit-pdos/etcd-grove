/-
`(*pipelineHandler).ServeHTTP(w, r)` (`http.go`; rafthttp stage 4, D33b): the receiving end of the
pipeline. Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Stream

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

/-- **A pipeline handler of the address `a`** at `h` (persistent): read-only for good, its logger
set, its `Raft` the receiver's (`netRaftOk`, borrowing `Rs` per call), the member owning `a` its
local id, and `addRemoteFromRequest` of its transport returning (stage 6's transport invariant
gives it; a premise until then). -/
def pipeHandlerOk (Rh : RaftHttp GF) (a : GoString) (γd : GName) (Rs : IProp GF) (h : Loc) :
    IProp GF :=
  iprop(∃ hv : rafthttp.pipelineHandler, h ↦□ hv ∗ ⌜hv.lg' ≠ null ∧ Rh.owner a = hv.localID'⌝ ∗
    □ netRaftOk Rh.γn hv.localID' γd Rs hv.r' ∗
    □ (∀ (r : Loc) (R : http.HReq) (rd : GoInterface),
      {{ http.reqAt r R rd }}
        (App (App (Val (@! rafthttp.addRemoteFromRequest)) (Val #hv.tr')) (Val #r))
      {{ RET #(); True }}))

instance pipeHandlerOk_persistent (Rh : RaftHttp GF) (a : GoString) (γd : GName) (Rs : IProp GF)
    (h : Loc) : Persistent (pipeHandlerOk Rh a γd Rs h) := by
  unfold pipeHandlerOk; infer_instance

end defs

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`h.ServeHTTP(w, r)`** of a request to `a` routed to `RaftPrefix` (`"/raft"`), as
`http.handlerFor` hands it: it returns, or panics (on an error `Process` returns, after answering
`500`), with the borrowed `Rs` back. On the way it calls `Process` with a fresh copy of the
message the request's body encodes, with its bundle: the persistent part from the request's
protocol, the one-shot part withdrawn from its deposit with the request's ticket. -/
abbrev rafthttp.pipelineHandler.ServeHTTP.spec : Prop :=
  ∀ (Rh : RaftHttp GF) (a : GoString) (γd : GName) (Rs : IProp GF) (h : Loc) (wi : GoInterfaceOk)
    (r : Loc) (R : http.HReq) (γk : GName) (rd : GoInterface),
  R.host = a → R.path = go!"/raft" →
  ⊢ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp -∗
    pipeHandlerOk Rh a γd Rs h -∗
    http.reqAt r R rd -∗ □ (raftProto Rh).req R γk -∗ http.reqTicket γk -∗
    http.bodyReader rd R [] -∗ http.respWriter (raftHttpNet Rh) (GoInterface.ok wi) a R γk none [] -∗
    ⌜go.typeSetContains wi.ty net.http.Flusher.ty = true⌝ -∗ Rs -∗
    WP (App (App (Val (h @!! go.GoType.PointerType rafthttp.pipelineHandler.ty @!! go!"ServeHTTP"))
      (Val #(GoInterface.ok wi))) (Val #r)) {{ _v, Rs }}

end spec

end EtcdGrove
end Perennial
