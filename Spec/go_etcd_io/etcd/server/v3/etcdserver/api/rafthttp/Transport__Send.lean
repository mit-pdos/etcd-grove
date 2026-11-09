/-
## `(*Transport).Send(msgs)`

**Users.** etcd's `raftNode.start` (`server/etcdserver/raft.go:250`: a leader sends its `Ready`'s messages before the write; `raft.go:329`: a follower after it), on `processMessages`'s output (`MsgSnap`s diverted to `msgSnapC`, at most one `MsgAppResp`, none to removed members). Snippet: `transport.go` (`ReqSendReady`).

**Proof sketch.** For each message: `To` read (`msgPts`); `0`: skipped. `RLock` with the token (a reader slot of the transport's pool), the maps read, `RUnlock`. A peer: `ServerStats.SendAppendReq` for a `MsgApp`, `peer.send` (its spec takes `outMsg`); a remote: `remote.send`; none: dropped (the facts are lost, which only loses a message), logged.

**Changes.** Restated over the new vocabulary (was over `specs-ref`'s `TransportState`/`TransportInv` records, `NetNames`, `netBundle`); same behaviour. The bundle is raft's `msgSent`/`msgCredit` (was `netBundle`'s payload `P`/`O`); `sendable` is the old `MsgMarshals`/`AppShape` premise restated over R1's `Msg`.

**Margin.** No delivery is promised (liveness); the at-most-once delivery is what `raftOk`'s `Process` premise and the credit's exclusivity make of it.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Rafthttp

open Iris Iris.BI Raft
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **Sends messages** (each with its `outMsg`: raft's facts, `sendable`), on a thread with its token: each is handed to the peer or remote of its `To` and delivered at most once (to `Process` of the member serving that peer's URLs, with `recvd`), or dropped. -/
def Transport.Send.spec : Prop :=
  ∀ (t : Loc) (ν : Net GF) (lid : w64) (sl : GoSlice) (ps : List Loc) (ms : List Msg) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ isTransport t ν lid ∗ threadTok ∗ sl ↦*{dq} ps ∗ ⌜ps.length = ms.length⌝ ∗ ([∗list] pm ∈ ps.zip ms, outMsg ν lid pm.1 pm.2) }}
    (App (Val (t @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport.ty @!! go!"Send")) (Val #sl))
  {{ RET #(); threadTok ∗ sl ↦*{dq} ps }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
