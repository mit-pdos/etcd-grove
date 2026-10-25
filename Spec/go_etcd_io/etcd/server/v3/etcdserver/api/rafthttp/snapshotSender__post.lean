/-
`(*snapshotSender).post(req)` (`snapshot_sender.go`; rafthttp stage 7d, D42). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Snapshot

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`s.post(req)`** of a snapshot sender to `pid`, of a request built for `R` (a snapshot
request of the raft protocol to a host of `pid`, with its streamed body, of the kind the protocol
allows, `reqSendOk`) and its ticket: the request is sent on a goroutine (`RoundTrip`, then the
response's body read, a timer draining it after `snapResponseReadTimeout`); `post` returns
`errStopped` if the sender is stopped first, else the round trip's or the read's error, else
`checkPostResponse`'s. Its error is `snapPostErr`'s: `nil`, net/http's, or a leaf pointer error
other than `errMemberRemoved` (a member's snapshot response is never a `403`). -/
abbrev rafthttp.snapshotSender.post.spec : Prop :=
  ∀ (Rh : RaftHttp GF) (s : Loc) (pid : w64) (req : Loc) (R : http.HReq) (γk : GName)
    (Pre Φ : List w8 → Prop),
  R.path = snapPath → Rh.owner R.host = pid →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      snapSenderOk Rh pid s ∗ http.reqOwn req R ∗ http.reqStream req (.stream Pre Φ) ∗
      http.reqSendOk (raftHttpNet Rh) R γk (.stream Pre Φ) ∗ http.reqTicket γk ∗
      □ (raftProto Rh).req R γk }}
    (App (Val (s @!! go.GoType.PointerType rafthttp.snapshotSender.ty @!! go!"post")) (Val #req))
  {{ (err : GoInterface), RET #err; snapPostErr err }}

end spec

end EtcdGrove
end Perennial
