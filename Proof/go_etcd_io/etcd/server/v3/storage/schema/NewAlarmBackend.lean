/-
The trust boundary: `schema.NewAlarmBackend(lg, be)` (`alarm.go`): names-only. Lean-first (no Rocq counterpart); the
server-construction unit, stage N0 (2026-10-16), for `NewServer`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.NewAlarmBackend

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

axiom schema.NewAlarmBackend.wp_proof : schema.NewAlarmBackend.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
