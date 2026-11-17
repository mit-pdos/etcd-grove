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

/-- **Trust boundary** (names-only zap). (S3e, 2026-11-17) `boltLogger` is now bbolt's own logger
contract at the program's file-extension instances (`bbolt.boltLogger`, `Spec/go_etcd_io/bbolt/Logger.lean`:
each of `Debugf`, `Errorf`, `Infof`, `Warningf`, called with a format bbolt uses and arguments it
lends, returns), `True` where there are none; until then an abstract predicate. Bbolt's
`Logger.lean` already stated that this axiom claims that contract of etcd's zap logger: zap's
`SugaredLogger` formats synchronously and never panics or exits at those levels, and
`zapBoltLogger.Warningf` calls `Warnf`. -/
axiom backend.newBoltLoggerZap.wp_proof : backend.newBoltLoggerZap.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
