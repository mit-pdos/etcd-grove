/-
## `(*peerStatus).deactivate(failure, reason)`

**Users.** the pipeline, the stream writer and reader, the snapshot sender.

**Proof sketch.** Under `mu`: `fmt.Sprintf`, `errors.New`, logs, gauges.

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

/-- (internal) Marks the peer inactive. -/
def peerStatus.deactivate.spec : Prop :=
  ∀ (s : Loc) (failure : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.failureType) (reason : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ statusAt s }}
    (App (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.peerStatus.ty @!! go!"deactivate")) (Val #failure)) (Val #reason))
  {{ RET #(); True }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
