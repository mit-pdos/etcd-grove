/-
## `(*Transport).Resume()`

**Users.** etcd's `raftNode.resumeSending` (`raft.go:454`, through `rafthttp.Pausable`). Snippet: `transport.go` (`ReqStop`).

**Proof sketch.** `RLock`; each peer's `Pause`/`Resume`; `RUnlock`.

**Changes.** New (no old spec).

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

/-- **`Resume()`** (a test hook, `Pausable`): every peer's traffic paused or resumed. -/
def Transport.Resume.spec : Prop :=
  ∀ (t : Loc) (ν : Net) (lid : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ isTransport t ν lid ∗ threadTok }}
    (App (Val (t @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport.ty @!! go!"Resume")) (Val #()))
  {{ RET #(); threadTok }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
