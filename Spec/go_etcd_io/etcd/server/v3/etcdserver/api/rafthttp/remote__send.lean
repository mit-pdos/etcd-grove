/-
## `(*remote).send(m)`

**Users.** `Transport.Send`.

**Proof sketch.** `paused` under `mu` (the fork's flag); a non-blocking send on the pipeline's `msgc`; full: logged.

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

/-- (internal) Queues a message on the remote's pipeline (non-blocking; dropped if full or paused). -/
def remote.send.spec : Prop :=
  ∀ (g : Loc) (ν : Net GF) (lid pid : w64) (ml : Loc) (m : Msg),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ remoteAt g ν lid pid ∗ outMsg ν lid ml m ∗ ⌜m.to = pid ∧ m.to ≠ W64 0⌝ }}
    (App (Val (g @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.remote.ty @!! go!"send")) (Val #ml))
  {{ RET #(); True }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
