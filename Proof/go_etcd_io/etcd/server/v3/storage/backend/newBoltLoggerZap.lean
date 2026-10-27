/-
The trust boundary: `Spec/go_etcd_io/etcd/server/v3/storage/backend/newBoltLoggerZap.lean`
(names-only: its body is zap's logger wrapping).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.newBoltLoggerZap

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.backend

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

axiom backend.newBoltLoggerZap.wp_proof : backend.newBoltLoggerZap.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
