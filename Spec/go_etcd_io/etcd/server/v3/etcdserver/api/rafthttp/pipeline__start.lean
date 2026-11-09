/-
## `(*pipeline).start()`

**Users.** `startPeer`, `startRemote`.

**Proof sketch.** `stopc`, `msgc` (`msgChanAt`), `wg.Add(4)` (the wait group backed by the workers' thread tokens: Perennial's `tokJoin`), four forks of `handle` with a `pipeWorker` each.

**Changes.** Restated over the new vocabulary (was over `specs-ref`'s `TransportState`/`TransportInv` records, `NetNames`, `netBundle`); same behaviour. The four `R`s are gone.

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

/-- (internal) **Starts the pipeline**: its queue (64) and four workers. -/
def pipeline.start.spec : Prop :=
  ∀ (pl : Loc) (ν : Net GF) (lid pid : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ pipeFresh pl ν lid pid }}
    (App (Val (pl @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.pipeline.ty @!! go!"start")) (Val #()))
  {{ RET #(); pipeAt pl ν lid pid ∗ pipeStopRight pl }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
