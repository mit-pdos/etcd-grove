/-
## `(*streamReader).decodeLoop(rc, t)`

**Users.** `streamReader.run`.

**Proof sketch.** The decoder for the type (`newMsgAppV2Decoder` with the stream's `v2Compat` from `streamBody`'s protocol knowledge, or a `messageDecoder`); the closer registered under `mu` (or the context done: close, `io.EOF`); loop: `decode` (a fresh message, `msgRecv`, and its frame: the writer's frame of that index, since `msgFrame` and `v2Frame` are self-delimiting and decoding is a function (raftpb's `wire_fun`; for msgappv2, a link heartbeat decodes as one, else the frame's message is the sent one); its message a heartbeat or one to `lid` with `msgSent` and a deposit, withdrawn with the reader's token of that index), `paused`, `isLinkHeartbeatMessage`, a non-blocking send on `recvc`/`propc` (`recvChanAt`: no `MsgSnap` comes by a stream, so `recvd`'s snapshot clause is vacuous); on a full queue a log line, where `m.GetType().String()` for a log line is raftpb's `MessageType.String` (a trust-boundary spec, requested of raft-conf-pb: verify-round A5 F1). `types.ID`'s `String()` on an addressable `ID` (log fields, headers) is 1c's `Types.ID.String_ptr.spec` (Goose's pointer receiver).

**Changes.** Restated over the new vocabulary (was over `specs-ref`'s `TransportState`/`TransportInv` records, `NetNames`, `netBundle`); same behaviour. verify-round (A5 F4, A8 F8): the messages queued are `msgRecv`; the frames transparent. verify-round (second pass): the sketch cites `Types.ID.String_ptr.spec`.

**Margin.** None.
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

/-- (internal) **Decodes a dialed stream**: each message (not a heartbeat, not while paused) handed to the peer's `recvc` (or `propc` for a `MsgProp`) with `recvd` (its credit withdrawn with the reader's token for its frame), non-blocking (full: dropped); returns the stream's error. -/
def streamReader.decodeLoop.spec : Prop :=
  ∀ (cr : Loc) (ν : Net GF) (lid pid : w64) (rc : GoInterface) (t : StreamTy),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ srAt cr ν lid pid ∗ srRun cr ∗ streamBody rc ν lid pid t }}
    (App (App (Val (cr @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.streamReader.ty @!! go!"decodeLoop")) (Val #rc)) (Val #(t.str)))
  {{ (err : GoInterface), RET #err; srRun cr ∗ ⌜err ≠ interface.nil⌝ ∗ Http.errOk err }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
