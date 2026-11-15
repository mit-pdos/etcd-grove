/-
## `(*pipelineHandler).ServeHTTP(w, r)`

**Users.** `Transport.Handler`'s mux at `/raft` (served by `Serve`).

**Proof sketch.** The method (`POST`, else `Allow`, `http.Error` 405), the cluster-id header, `checkClusterCompatibilityFromHeader` (its version headers parse: `raftProto`'s request knowledge), `addRemoteFromRequest` (the `X-PeerURLs` hosts are peer addresses: the same), `ioutil.NewLimitedBufferReader` and `io.ReadAll` (the reader's `EOF` gives the body knowledge: an encoding of a message `m`, not a `MsgSnap`, with `msgSent` and the deposit), `proto.Unmarshal` (a fresh `m`: `Unmarshal`'s `Proto.mergeDst`, made `msgRecv` by `RaftPb.msgRecv_intro.spec`; `RaftPb.msgEncodes` and `wire_fun` identify it with the sender's), the deposit opened with the ticket (`onceOnly`: a `POST`) for `msgCredit`, `Process(context.TODO(), m)` with the handler's thread token (`raftOk`), then `WriteHeader(204)`; on `procErr`: `errors.As` and `WriteTo`, or `http.Error` 500, `Flush`, `panic` (allowed by `serveDone`). `types.ID`'s `String()` on an addressable `ID` (log fields, headers) is 1c's `Types.ID.String_ptr.spec` (Goose's pointer receiver).

**Changes.** Restated over the new vocabulary (was over `specs-ref`'s `TransportState`/`TransportInv` records, `NetNames`, `netBundle`); same behaviour. The `netProcSlots` resource per invocation is now the handler goroutine's thread token. verify-round (A5 F4, A8 F8): the message handed to `Process` is `msgRecv` (`raftOk`'s), identified through raftpb's `msgEncodes`. verify-round (second pass): the sketch cites `Types.ID.String_ptr.spec`.

**Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Api

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

/-- (internal) **Serves a pipeline POST**: the body's message delivered to `Process` with `recvd` (its credit withdrawn with the request's ticket), answered `204`; or refused (`405`, `412`, `400`); or `Process`'s error written (`writerToResponse`), or `500` and a panic that `Serve` recovers. -/
def pipelineHandler.ServeHTTP.spec : Prop :=
  ∀ (hp : Loc) (ν : Net GF) (lid : w64) (w : GoInterface) (r : Loc) (R : Http.HReq) (τ : GName) (rd : GoInterface),
  ⊢ (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ phAt hp ν lid ∗ Http.servePre (raftProto ν) go!"/raft" w r R τ rd) -∗
    WP (App (App (Val (hp @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.pipelineHandler.ty @!! go!"ServeHTTP")) (Val #w)) (Val #r))
    {{ v, Http.serveDone (raftProto ν) w R τ v }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
