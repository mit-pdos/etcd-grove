/-
`(*rafthttp.Transport).CutPeer(id)` (`transport.go`): names-only. Lean-first (no Rocq counterpart);
the partition plan's stage S1 (2026-10-20, `notes/partition-plan.md`), an axiom at the trust
boundary, why it is true of the Go code below.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvBoot

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`t.CutPeer(id)`** on a started transport: it returns. From then on the transport drops every
message to and from member `id` (etcd's partition injection, used by its integration tests:
`tests/framework/integration/cluster.go`, `InjectPartition`), until `MendPeer`.

Why it is true of the Go code (`transport.go`, `peer.go`, `stream.go` at the etcd pin):
`CutPeer` takes the transport's read lock and looks `id` up in its peers and remotes (both
maps exist once `Start` ran; a missing entry does nothing). `id` is no remote (`transportRemotes
t rs`, `id ∉ rs`: `t.remotes` gets a key only through `AddRemote`), so only the peer's branch runs:
a remote's `Pause` stops its pipeline, and a second one panics
(`issues/etcd-rafthttp-cutpeer-twice-remote-panic.md`), which this premise excludes. On the peer
it calls `Pause`
(`peer.go`): under the peer's lock it sets `paused` and pauses the peer's two stream readers
(`stream.go`, `streamReader.pause`). A paused peer's `send` returns without sending (no
`ReportUnreachable` either), and a paused stream reader's `decodeLoop` discards every message it
decodes instead of handing it to `Raft.Process`. `Pause` is idempotent on a peer. Nothing is
resent later. Every message so dropped, outgoing or incoming, is one `Transport.Start`'s axiom
already allows to be lost ("each sent message possibly lost"), so the network model
(`Net.lean`) is unchanged: this axiom adds no assumption about delivery, only that the call
returns without a panic. -/
abbrev rafthttp.Transport.CutPeer.spec : Prop :=
  ∀ (γn : NetNames GF) (t : Loc) (id : w64) (rs : List w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      transportStarted γn t ∗ transportRemotes t rs ∗ ⌜id ∉ rs⌝ }}
    (App (Val (t @!! go.GoType.PointerType
      go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport.ty @!! go!"CutPeer")) (Val #id))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
