/-
## `(*EtcdServer).CutPeer(id)` (`server.go:2196-2202`)

**Users.** `cluster3.PeerStep` (partitions, as etcd's integration tests'
`InjectPartition`). Snippet: `etcdserverboot/boot.go` (`ReqPartition`).

**Proof sketch.** The transport's `Pause` of the peer (2f), when `s.r.transport` is a
`*rafthttp.Transport` (it is: `NewServer` set it).

**Changes** (from `specs-ref`'s `EtcdServer__CutPeer.lean`, a reader token of the transport): over
`srvMember`.

**Margin.** None: a cut drops messages, which raft tolerates.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiBoot

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI EtcdModel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`CutPeer(id)`**: drop messages to and from member `id`. -/
def EtcdServer.CutPeer.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (id : Nat) (p : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ srvMember s γ id ∗ threadTok }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"CutPeer")) (Val #p))
  {{ RET #(); threadTok }}

end spec

end EtcdServer
end EtcdGrove
end Perennial
