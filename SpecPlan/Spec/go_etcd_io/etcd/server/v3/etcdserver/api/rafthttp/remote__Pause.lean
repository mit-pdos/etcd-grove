/-
## `(*remote).Pause()`

**Users.** `Transport.CutPeer`/`MendPeer`.

**Proof sketch.** `paused` under `mu` (idempotent: the fork's flag).

**Changes.** Restated over the new vocabulary (was over `specs-ref`'s `TransportState`/`TransportInv` records, `NetNames`, `netBundle`); same behaviour.

**Margin.** None.
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

/-- (internal) Sets the remote's `paused` flag (paused traffic). -/
def remote.Pause.spec : Prop :=
  ∀ (g : Loc) (ν : Net GF) (lid pid : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ remoteAt g ν lid pid }}
    (App (Val (g @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.remote.ty @!! go!"Pause")) (Val #()))
  {{ RET #(); True }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
