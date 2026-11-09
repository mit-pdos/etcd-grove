/-
`(*EtcdServer).Process(ctx, m)` (`server.go:700-722`): the transport's inbound message: refused
(an HTTP 403 error) from a removed member or to another member, else stepped into raft.

**Users**: rafthttp's stream and pipeline handlers (`api/rafthttp/peer.go`, `stream.go`,
`pipeline.go`, `snapshot_sender`'s receiver `http.go`: batch 2f), through the `rafthttp.Raft`
interface. Snippet `raftnode.go` (`ReqProcess`).

**Proof sketch**: `s.cluster.IsIDRemoved(from)` (2e's `Membership`: any answer); `MemberID() != to`:
an error (`httptypes.NewHTTPError`, 2e's); a `MsgApp`'s size (`proto.Size`, 2a's) into the stats
(2e's `v2stats`); `s.r.Step(ctx, m)` (`raftNode.Step.spec`, with `m.to = id` now known). The message
comes with 2f's `recvd ν m` for the server's network (`srvNet γ ν`): `msgSent`, `msgCredit`, and for a
`MsgSnap` of index `i` its database kept (`ν.dbIn i`), which `Process` deposits in the member's
invariant over its snapshot directory, where the batch of the snapshot's install takes it
(`snapImage`, round 1, completeness F6). **Changes** from `specs-ref`'s spec (the transport's `stepIn` bundle): over R1's
`msgSent`/`msgCredit`; the error is 2f's `procErr` (its `raftOk` contract: `procErr_forbidden`
for the 403s, `Rafthttp.procErr_nodeErr` for raft's), and the thread token 2f's contract lends
(`lgMu` and the membership are read under read locks). Callable from `NewServer` on (`srvNode`):
the transport starts before `start`. **Margin**: which error is not described (rafthttp only
logs it or answers it).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiApply

set_option autoImplicit false
set_option linter.iris.dupNamespace false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [ctx_sem : context.Assumptions]

/-- **Step an inbound message** a node of the cluster sent. -/
def EtcdServer.Process.spec : Prop :=
  ∀ (s : Loc) (γ : Names) (id : Nat) (ν : Rafthttp.Net GF) (ctx : GoInterface) (mp : Loc)
    (m : Raft.Msg),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvNode s γ id ∗ srvNet γ ν ∗ Context.ctxOk ctx ∗ Raft.msgPts mp (DFrac.own 1) m ∗
      Rafthttp.recvd ν m ∗ threadTok }}
    (App (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!!
      go!"Process")) (Val #ctx)) (Val #mp))
  {{ (err : GoInterface), RET #err; Rafthttp.procErr err ∗ threadTok }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
