/-
`v3rpc.serverWatchStream.recvLoop` (`watch.go`). Lean-first (no Rocq counterpart); the
vocabulary is `v3rpc/InvWatchStream.lean` and `v3rpc/InvWatch.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvWatch

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.etcd.server.v3.etcdserver
  go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`sws.recvLoop()`**: receives the client's requests until the stream ends (`io.EOF`: `nil`;
another error: it), or `closec` is closed (`nil`): each create request is registered with the
mvcc watch stream (its watch token spent) or refused, each cancel request cancels, each progress
request asks for the progress of all; every create and cancel request answered by a control
response on the control stream (`ctrlP`: the response answers the request at its position, with
the answer token it mints from `ansPool` when it receives the request; the watch slice's unit
W-C).
Returns the control stream's producer token. -/
abbrev v3rpc.serverWatchStream.recvLoop.spec : Prop :=
  ∀ (sws : Loc) (r : v3rpc.WRun GF) (L : List v3rpc.WatchReqM) (sent : List Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ v3rpc.swsIs sws r ∗ v3rpc.srvRecvTok (Req := v3rpc.pbWatchRequest) r.γs L ∗
      spscProducer r.γctrl sent ∗ v3rpc.ansPool r.γa L.length ∗ v3rpc.recvRes r.srv }}
    (App (Val (sws @!! go.GoType.PointerType v3rpc.serverWatchStream.ty @!! go!"recvLoop")) (Val #()))
  {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil ∨ context.isTypedErr err⌝ ∗
      ∃ sent' : List Loc, spscProducer r.γctrl sent' }}

end spec

end EtcdGrove
end Perennial
