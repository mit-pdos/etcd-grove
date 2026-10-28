/-
`(*snapshotHandler).ServeHTTP(w, r)` (`http.go`; rafthttp stage 7e, D42): the receiving end of the
snapshot stream. Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Stream

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **A snapshot handler of the address `a`** at `h` (persistent): read-only for good, its logger
set, its `Raft` the receiver's (`netRaftOk`, borrowing `Rs` per call), the member owning `a` its
local id, its snapshotter's directory `γd` (`snapDirInv`), and `addRemoteFromRequest` of its
transport returning on a request from another member (as `pipeHandlerOk`). -/
def snapHandlerOk (Rh : RaftHttp GF) (a : GoString) (γd : GName) (Rs : IProp GF) (h : Loc) :
    IProp GF :=
  iprop(∃ (hv : rafthttp.snapshotHandler) (Rm : w64 → IProp GF), h ↦□ hv ∗
    ⌜hv.lg' ≠ null ∧ Rh.owner a = hv.localID'⌝ ∗
    □ netRaftOk Rh.γn hv.localID' γd Rs hv.r' ∗
    snap.isSnapshotter hv.snapshotter' ∗ inv snapDirN (snapDirInv hv.snapshotter' γd Rh.γn.N.img Rm) ∗
    □ (∀ (r : Loc) (R : http.HReq) (rd : GoInterface),
      {{ http.reqAt r R rd ∗ ⌜fromOkAt Rh hv.localID' R.hdr⌝ }}
        (App (App (Val (@! rafthttp.addRemoteFromRequest)) (Val #hv.tr')) (Val #r))
      {{ RET #(); True }}))

instance snapHandlerOk_persistent (Rh : RaftHttp GF) (a : GoString) (γd : GName) (Rs : IProp GF)
    (h : Loc) : Persistent (snapHandlerOk Rh a γd Rs h) := by
  unfold snapHandlerOk; infer_instance

end defs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`h.ServeHTTP(w, r)`** of a request to `a` routed to the snapshot path, as `http.handlerFor`
hands it (its body `reqBody`: a `POST`'s a stream of the protocol's contract, `snapSReq`): it
returns with the borrowed `Rs` back and the writer committed (`204`, or an error's status). On the
way, having decoded the envelope from the body's prefix and saved the rest with `SaveDBFrom` (the
snapshot's index saved, `snapSaved`), it calls `Process` with the decoded message, with its
bundle: the persistent part from the request's protocol, the one-shot part withdrawn from its
deposit with the request's ticket (`netRecv`, with `netSnapRecv`). -/
abbrev rafthttp.snapshotHandler.ServeHTTP.spec : Prop :=
  ∀ (Rh : RaftHttp GF) (a : GoString) (γd : GName) (Rs : IProp GF) (h : Loc) (wi : GoInterfaceOk)
    (r : Loc) (R : http.HReq) (γk : GName) (rd : GoInterface),
  R.host = a → R.path = snapPath →
  ⊢ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp -∗
    snapHandlerOk Rh a γd Rs h -∗
    http.reqAt r R rd -∗ □ (raftProto Rh).req R γk -∗ http.reqTicket γk -∗
    http.reqBody (raftHttpNet Rh) a R γk rd -∗
    http.respWriter (raftHttpNet Rh) (GoInterface.ok wi) a R γk none [] -∗
    http.respHdrs (GoInterface.ok wi) [] -∗ Rs -∗
    WP (App (App (Val (h @!! go.GoType.PointerType rafthttp.snapshotHandler.ty @!! go!"ServeHTTP"))
      (Val #(GoInterface.ok wi))) (Val #r))
      {{ v, Rs ∗ http.handlerDone (raftHttpNet Rh) (GoInterface.ok wi) a R γk v }}

end spec

end EtcdGrove
end Perennial
