/-
The trust boundary: `Spec/go_etcd_io/bbolt/Tx__Rollback_kv.lean` (bbolt is names-only here).
-/
module

public import Spec.go_etcd_io.bbolt.Tx__Rollback_kv

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.bbolt backend

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **Trust boundary** (2026-11-06, restated, `notes/begin-tok-plan.md`): why the post's
`threadTok` is faithful. In bbolt (the fork `upamanyus/bbolt` `743299d8cec8`, as upstream v1.5.0), `Tx.Rollback` (`tx.go:303`) of an open read transaction runs
`nonPhysicalRollback` (`tx.go:313`) → `close` (`tx.go:353`) → `db.removeTx` (`tx.go:378`), which
releases the transaction's `mmaplock` reader slot (`db.mmaplock.RUnlock()`, `db.go:951`), the slot
`DB.Begin(false)` took (`db.go:875`). The pre is the whole `txLive tx 1` with `rtxSnap tx D`, which
only a read-mode `DB.Begin_kv` gives (a write transaction has no `rtxSnap`), and it is consumed:
each token `DB.Begin_kv` took comes back once. -/
axiom bbolt.Tx.Rollback_kv.wp_proof : bbolt.Tx.Rollback_kv.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
