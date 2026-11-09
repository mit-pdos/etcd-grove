/-
## `newSnapshotSender(tr, picker, to, status)`

**Users.** `startPeer`.

**Proof sketch.** The literal, `stopc`.

**Changes.** Restated over the new vocabulary (was over `specs-ref`'s `TransportState`/`TransportInv` records, `NetNames`, `netBundle`); same behaviour.

**Margin.** None.
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

/-- (internal) The snapshot sender for peer `pid`. -/
def newSnapshotSender.spec : Prop :=
  ∀ (t : Loc) (ν : Net) (lid pid : w64) (pk st : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ isTransport t ν lid ∗ pickerAt pk ν ∗ statusAt st }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.newSnapshotSender)) (Val #t)) (Val #pk)) (Val #pid)) (Val #st))
  {{ (s : Loc), RET #s; ssAt s ν lid pid ∗ ssStopRight s }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
