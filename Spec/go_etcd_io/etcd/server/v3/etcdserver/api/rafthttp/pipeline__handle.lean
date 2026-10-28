/-
`(*pipeline).handle` (`pipeline.go`; rafthttp stage 4d). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Handle

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `p.handle()`, a goroutine of the pipeline `p` to the peer `to` holding one of its `Raft`'s
resources `R`: posts each message it receives on `msgc` until `stopc` is closed, then hands `R`
to the pipeline's `wg.Done()`. -/
abbrev rafthttp.pipeline.handle.spec : Prop :=
  ∀ (Rh : RaftHttp GF) (p : Loc) (to : w64) (R : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      pipeHandleOk Rh p to R ∗ R ∗ sync.join.ownDone (p.[rafthttp.pipeline, go!"wg"]) R }}
    (App (Val (p @!! go.GoType.PointerType rafthttp.pipeline.ty @!! go!"handle")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
