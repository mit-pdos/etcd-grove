/-
## `(*Transport).ActivePeers()`

**Users.** etcd's `adjustTicks` (`server.go:504`: fast-forwards election ticks when no peer is active). Snippet: `transport.go` (`ReqConnected`).

**Proof sketch.** `RLock`; count the peers whose `activeSince` is non-zero (at most the map's size, below `2^63`); `RUnlock`.

**Changes.** New (no old spec).

**Margin.** The count is not tied to any connection fact (a heuristic).
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

/-- **The number of active peers**: a non-negative count. -/
def Transport.ActivePeers.spec : Prop :=
  ∀ (t : Loc) (ν : Net GF) (lid : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ isTransport t ν lid ∗ threadTok }}
    (App (Val (t @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport.ty @!! go!"ActivePeers")) (Val #()))
  {{ (cnt : w64), RET #cnt; threadTok ∗ ⌜0 ≤ sint.Z cnt⌝ }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
