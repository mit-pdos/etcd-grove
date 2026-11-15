/-
## `(*Transport).MendPeer(id)`

**Users.** etcd's `EtcdServer.MendPeer` (`server.go:2205`; `RecoverPartition`). Snippet: `transport.go` (`ReqStop`'s partition).

**Proof sketch.** `RLock`; the peer's `Pause`/`Resume` through the `Pausable` assertion (a `*peer`: the map holds only those), the remote's (the fork's `paused` flag: idempotent); `RUnlock`.

**Changes.** Restated; the old `trNoRemOr` premise has been gone since the fork's remote flag (`nonissues/etcd-rafthttp-cutpeer-twice-remote-panic.md`).

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

/-- **`MendPeer(id)`** (a test hook): pauses or resumes the traffic of peer or remote `id`. -/
def Transport.MendPeer.spec : Prop :=
  ∀ (t : Loc) (ν : Net GF) (lid pid : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ isTransport t ν lid ∗ threadTok }}
    (App (Val (t @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport.ty @!! go!"MendPeer")) (Val #pid))
  {{ RET #(); threadTok }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
