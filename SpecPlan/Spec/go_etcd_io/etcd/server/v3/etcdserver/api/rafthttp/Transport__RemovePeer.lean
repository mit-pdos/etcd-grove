/-
## `(*Transport).RemovePeer(id)`

**Users.** etcd's `applyConfChange` (`server.go:2085`, a removed member). Snippet: `transport.go` (`ReqMembership`).

**Proof sketch.** `Lock` (the map invariant: `trMaps`), `removePeer`, `Unlock`.

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

/-- **Removes a peer** (or does nothing for an unknown id): its goroutines stopped. -/
def Transport.RemovePeer.spec : Prop :=
  ∀ (t : Loc) (ν : Net GF) (lid pid : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ isTransport t ν lid }}
    (App (Val (t @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport.ty @!! go!"RemovePeer")) (Val #pid))
  {{ RET #(); True }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
