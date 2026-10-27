/-
`(*Transport).SendSnapshot(m)` (`transport.go`): names-only (the snapshot stream, D22's contract:
the configuration's `!Transport.SendSnapshot`, `!peer.sendSnap`, `!snapshotSender.*`). Lean-first;
rafthttp stage 6d (2026-10-24): a trust-boundary axiom cut out of `Transport.Start`'s (the stage-6
choice (1), the user's), at its own function.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.TransportState

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

/-- **`t.SendSnapshot(m)`** on a started transport of the network `γn` (`trState`; D43 M5c: the
peers read under the lock, so not frozen), of a merged
snapshot message (`snap.msgIs m ml rc`) with its bundle (`netSnapBundle`): it returns.

Why it is true of the Go code (`transport.go:409-418`, `peer.go`, `snapshot_sender.go:66-140` at
the etcd pin): under the transport's read lock, the peer added for `m.GetTo()` takes `m`
(`peer.sendSnap` → `snapshotSender.send`, a goroutine) or, none added,
`m.CloseWithError(errMemberNotFound)`. The sender's goroutine posts the envelope (the raft
message, marshalled) and `m`'s reader's bytes to the peer's snapshot URL (a URL of the peer's
directory entry, `peerURL`: its hosts registered with the raft protocol, `pipeReg`), once (no
retry), then reports `ReportSnapshot(To, Finish|Failure)` to `t.Raft` (`netRaftOk`'s reports, at
any time) and closes `m` (`CloseWithError`: the reader closed, one value on `closeC`, the only send
on it). `m`'s raft message is only read (marshalled), `m`'s fields only read (`snap.msgIs`), its
reader read by this goroutine alone (`readerStreams`). The receiving side is the snapshot
handler's (`newSnapshotHandler`'s axiom): the bytes saved are a complete stream of the sender's
reader, `D` with the bundle's `□ γn.N.img i D`. The read lock is taken without one of the
lock's reader tokens (`trTok`): at most `2^30 - 1` goroutines hold it at once, physically (each
has its own stack; as `netProcSlots`). -/
abbrev rafthttp.Transport.SendSnapshot.spec : Prop :=
  ∀ (γn : NetNames GF) (t : Loc) (c : TrN GF) (m ml : Loc) (rc : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      trState γn t c ∗ snap.msgIs m ml rc ∗ netSnapBundle γn.N ml rc }}
    (App (Val (t @!! go.GoType.PointerType rafthttp.Transport.ty @!! go!"SendSnapshot")) (Val #m))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
