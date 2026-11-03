/-
`(*pipeline).stop` (`pipeline.go`; rafthttp stage 4d). Lean-first.
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

/-- `p.stop()` of a started pipeline: closes its stop channel and waits for its goroutines (until
J8a-6, 2026-11-01, whose four resources `R` came back). -/
abbrev rafthttp.pipeline.stop.spec : Prop :=
  ∀ (Rh : RaftHttp GF) (p : Loc) (to : w64) (R : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      pipeStarted Rh p to R }}
    (App (Val (p @!! go.GoType.PointerType rafthttp.pipeline.ty @!! go!"stop")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
