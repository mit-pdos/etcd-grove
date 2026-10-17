/-
**The send queues of a gRPC watch stream** (`watchGRPCStream.sendCreatec`, `sendBestEffortc`,
`client/v3/watch.go` with etcd-io/etcd#21065; `notes/pr-verify/etcd-21065.md`). Lean-first, no
Rocq counterpart.

With the PR, `run` no longer calls the stream's `Send`: it puts each request on one of two
buffered channels (`enqueueCreateReq`, the creates; `enqueueBestEffortReq`, the cancels and
progress requests, dropped when the channel is full), and a goroutine, `sendLoop`, the only
sender on the gRPC stream, takes them off and sends them. Both channels are SPSC (`run` the
producer, the stream's `sendLoop` the consumer; `run` closes them when the stream fails). What an
element carries (`sendElem`): an owned request message (`watchReqSend`) and what the server's
specification asks of a request at any position (`v3rpc.watchUp`: restricted, a watch token for a
create; it does not depend on the position, so the producer does not need to know where the
request will land on the stream).

`sendQIs` (persistent): the two fields (read-only once `newWatchClient` set them: under
`noRetryableStreamErr` it is called once) and the two channels.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvWatch

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace client

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.client.v3

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **What a send queue carries** (the SPSC element, any index): a request message holding `m`
and the server's content for it at any position. -/
def sendElem (V : WEnv GF) (_k : Int) (req : Loc) : IProp GF :=
  iprop(∃ m : v3rpc.WatchReqM, v3rpc.watchReqSend req m ∗ v3rpc.watchUp V.R.γ 0 m)

/-- **A stream's send queues' names**: the create queue (`cc`, `γc`) and the best-effort queue
(`bc`, `γb`). -/
structure SendQ where
  cc : Loc
  γc : SpscNames
  bc : Loc
  γb : SpscNames

/-- **The send queues of the stream `wgs`** (persistent): its two fields, read-only, and the two
SPSC channels of `sendElem` (nothing given at close). -/
def sendQIs (V : WEnv GF) (wgs : Loc) (Q : SendQ) : IProp GF :=
  iprop(wgsF wgs go!"sendCreatec" ↦□ Q.cc ∗ wgsF wgs go!"sendBestEffortc" ↦□ Q.bc ∗
    isSpsc Q.γc Q.cc (sendElem V) (fun _ => iprop(True)) ∗
    isSpsc Q.γb Q.bc (sendElem V) (fun _ => iprop(True)))

instance sendQIs_persistent (V : WEnv GF) (wgs : Loc) (Q : SendQ) :
    Persistent (sendQIs V wgs Q) := by
  unfold sendQIs; infer_instance

/-- The server's content of a request does not depend on its position. -/
theorem watchUp_any (γ : mvcc.WsNames) (i : Nat) (m : v3rpc.WatchReqM) :
    v3rpc.watchUp (GF := GF) γ 0 m ⊢ v3rpc.watchUp γ i m := by
  unfold v3rpc.watchUp
  iintro H
  iexact H

end defs

end client
end EtcdGrove
end Perennial
