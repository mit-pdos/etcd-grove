/-
## `(*peer).pick(m)`

**Users.** `peer.send`.

**Proof sketch.** `isMsgSnap`, the writers' `writec` (each a `msgChanAt`), `isMsgApp`.

**Changes.** Restated over the new vocabulary (was over `specs-ref`'s `TransportState`/`TransportInv` records, `NetNames`, `netBundle`); same behaviour.

**Margin.** The queue picked accepts `m` (`K m`: the msgappv2 writer's queue only `MsgApp`s). The post does not say which queue (the msgappv2 queue's frames need a `MsgApp`: its channel's invariant asks for it, and `pick` sends only `MsgApp`s there; stated inside `msgChanAt`'s realization per writer type).
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

/-- (internal) **Picks the queue for a message**: the pipeline's for a `MsgSnap`, the msgappv2 writer's for a `MsgApp` while it works, the message writer's while it works, else the pipeline's. -/
def peer.pick.spec : Prop :=
  ∀ (p : Loc) (ν : Net GF) (lid pid : w64) (ml : Loc) (dq : DFrac) (m : Msg),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ peerAt p ν lid pid ∗ msgPts ml dq m }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.peer.ty @!! go!"pick")) (Val #ml))
  {{ (ch : GoChan) (name : GoString), RET (PairV #ch #name); msgPts ml dq m ∗ ∃ K, msgChanAt ch ν lid pid K ∗ ⌜K m⌝ }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
