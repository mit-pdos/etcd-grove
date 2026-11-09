/-
## `(*pipeline).post(data)`

**Users.** `pipeline.handle`.

**Proof sketch.** `picker.pick` (a URL with `peerAddr`), `createPostRequest` (`POST /raft`, `bytes.NewBuffer(data)`: a body whose complete stream is `bs`), `context.WithCancel`, the canceller goroutine (`waitSchedule`); a fresh ticket `τ` (`Http.reqTicket_alloc`), the deposit `inv (msgCredit m ∨ reqTicket τ)` and `msgSent m` make `raftProto`'s request knowledge; `RoundTrip` (`roundTripperOk`) with the ticket; `io.ReadAll` of the body (`Http.readerAt_read`), `checkPostResponse`; on errors `picker.unreachable`, `reportCriticalError` for `errMemberRemoved`.

**Changes.** Restated over the new vocabulary (was over `specs-ref`'s `TransportState`/`TransportInv` records, `NetNames`, `netBundle`); same behaviour.

**Margin.** The error's kind is not stated.
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

/-- (internal) **POSTs one encoded message** to the peer's URL: the request carries the message's facts and its credit (deposited for the request's ticket); `nil` only for a `204`. -/
def pipeline.post.spec : Prop :=
  ∀ (pl : Loc) (ν : Net GF) (lid pid : w64) (data : GoSlice) (bs : List w8) (dq : DFrac) (m : Msg),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ pipeAt pl ν lid pid ∗ data ↦*{dq} bs ∗ ⌜pbEncodes bs m ∧ sendable lid m ∧ m.to ≠ W64 0⌝ ∗ msgSent ν.γ m ∗ msgCredit ν.γ m }}
    (App (Val (pl @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.pipeline.ty @!! go!"post")) (Val #data))
  {{ (err : GoInterface), RET #err; Http.errOk err }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
