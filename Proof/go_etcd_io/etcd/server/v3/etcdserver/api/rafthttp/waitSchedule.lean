/-
The trust boundary: `waitSchedule` (`pipeline.go`), untranslated: `runtime.Gosched()`, which yields
the processor and returns (Perennial has no `runtime` proof). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.waitSchedule

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

axiom rafthttp.waitSchedule.wp_proof : rafthttp.waitSchedule.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
