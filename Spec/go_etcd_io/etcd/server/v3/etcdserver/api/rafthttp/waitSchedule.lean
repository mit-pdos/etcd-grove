/-
`waitSchedule()` (`pipeline.go`: `runtime.Gosched()`; names-only, rafthttp stage 4d; translated and proved 2026-11-19). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Sender

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

/-- `waitSchedule()` returns (it yields the processor). (2026-11-19, proved: the package's
initialization, which gives `runtime`'s, which `runtime.Gosched` needs; the one caller,
`pipeline.post`, has it.) -/
abbrev rafthttp.waitSchedule.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp }}
    (App (Val (@! rafthttp.waitSchedule)) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
