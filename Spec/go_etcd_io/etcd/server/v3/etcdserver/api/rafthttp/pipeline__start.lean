/-
`(*pipeline).start` (`pipeline.go`; rafthttp stage 4d). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Handle

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `p.start()` of a pipeline `p` to the peer `to` with its fixed fields, given four of its
`Raft`'s resources `R`: makes its stop and message channels and starts its four goroutines
(`handle`), each with an `R`. -/
abbrev rafthttp.pipeline.start.spec : Prop :=
  ∀ (Rh : RaftHttp GF) (p : Loc) (to : w64) (R : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      pipeFixed Rh p to R ∗ (∃ sc : GoChan, p.[rafthttp.pipeline, go!"stopc"] ↦ sc) ∗
      (∃ mc : GoChan, p.[rafthttp.pipeline, go!"msgc"] ↦ mc) ∗
      sync.join.ownAdder (p.[rafthttp.pipeline, go!"wg"]) (W32 0) iprop(True) ∗ R ∗ R ∗ R ∗ R }}
    (App (Val (p @!! go.GoType.PointerType rafthttp.pipeline.ty @!! go!"start")) (Val #()))
  {{ RET #(); pipeStarted Rh p to R }}

end spec

end EtcdGrove
end Perennial
