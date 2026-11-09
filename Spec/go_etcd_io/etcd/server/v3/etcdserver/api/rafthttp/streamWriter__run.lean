/-
## `(*streamWriter).run()`

**Users.** `startStreamWriter` (forked).

**Proof sketch.** `time.NewTicker(ConnReadTimeout / 3)` (positive); loop on a five-way `select`: a heartbeat (`encode` of a clone of the link heartbeat: its frame needs no deposit), a message from `msgc` (its credit deposited for its frame's index in the connection's reader tokens, then `encode`: `raftProto`'s stream response allows the frame), a connection from `connc` (`outConn`: the encoder for its type, `closeUnlocked` of the old one, `working`), `stopc` (`close`, `close(done)` with the loop's resources). Failures: `deactivate`, `close`, `ReportUnreachable`.

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

/-- (internal; a goroutine) **The writer loop**: encodes queued messages and heartbeats on the attached connection, replaces it on a new one, closes it on a failure (its queue dropped), until stopped (`done` closed). -/
def streamWriter.run.spec : Prop :=
  ∀ (cw : Loc) (ν : Net) (lid pid : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ swAt cw ν lid pid ∗ swRun cw }}
    (App (Val (cw @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.streamWriter.ty @!! go!"run")) (Val #()))
  {{ RET #(); True }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
