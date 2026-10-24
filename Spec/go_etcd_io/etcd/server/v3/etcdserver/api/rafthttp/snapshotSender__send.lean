/-
`(*snapshotSender).send(merged)` (`snapshot_sender.go`; rafthttp stage 7d, D42). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Snapshot
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Defs

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

/-- **`s.send(merged)`** of a snapshot sender to `pid` and a merged message for `pid` (with its
bundle and its reader: `snapBundleTo`): it posts the snapshot (`post`, a snapshot request of the
raft protocol, the message's one-shot part deposited under the request's ticket), reports the
outcome to the member's `Raft` (`ReportUnreachable` and `SnapshotFailure`, or `SnapshotFinish`),
closes the merged message (`CloseWithError`, of `post`'s error) and its body, and returns. It
reports no critical error: `errors.Is(err, errMemberRemoved)` is `false` of every error `post`
returns (`snapPostErr`, `netErrNotRemoved_spec`). -/
abbrev rafthttp.snapshotSender.send.spec : Prop :=
  ∀ (Rh : RaftHttp GF) (pid : w64) (s m ml : Loc) (rc : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      snapSenderOk Rh pid s ∗ snap.msgIs m ml rc ∗ snapBundleTo Rh.γn.N pid ml rc }}
    (App (Val (s @!! go.GoType.PointerType rafthttp.snapshotSender.ty @!! go!"send")) (Val #m))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
