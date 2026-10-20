/-
`(*rafthttp.Transport).MendPeer(id)` (`transport.go`): names-only. Lean-first (no Rocq counterpart);
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

/-- **`t.MendPeer(id)`** on a started transport: it returns. From then on the transport no longer
drops the messages to and from member `id` that `CutPeer` made it drop (etcd's partition
recovery, used by its integration tests: `tests/framework/integration/cluster.go`,
`RecoverPartition`).

Why it is true of the Go code (`transport.go`, `peer.go`, `stream.go` at the etcd pin):
`MendPeer` takes the transport's read lock and looks `id` up in its peers and remotes (both
maps exist once `Start` ran; a missing entry does nothing). `id` is no remote (`transportRemotes
t rs`, `id ∉ rs`; a remote's `Resume` would start its pipeline's goroutines again, a leak but no
panic: the same premise as `CutPeer`'s, so that the two are used together), so only the peer's
branch runs. On the peer it calls `Resume`
(`peer.go`): under the peer's lock it clears `paused` and resumes the peer's two stream readers
(`stream.go`, `streamReader.resume`), so `send` sends again and `decodeLoop` hands what it decodes
to `Raft.Process` again. `Resume` is idempotent on a peer. Nothing dropped while paused is
resent. So the call changes nothing the network model describes (the messages sent from now on
reach `Process` or are lost, as `Transport.Start`'s axiom says of every message): this axiom
adds no assumption about delivery, only that the call returns without a panic. -/
abbrev rafthttp.Transport.MendPeer.spec : Prop :=
  ∀ (γn : NetNames GF) (t : Loc) (id : w64) (rs : List w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      transportStarted γn t ∗ transportRemotes t rs ∗ ⌜id ∉ rs⌝ }}
    (App (Val (t @!! go.GoType.PointerType
      go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport.ty @!! go!"MendPeer")) (Val #id))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
