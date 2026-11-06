/-
The trust boundary: `Spec/go_etcd_io/bbolt/DB__Begin_kv.lean` (bbolt is names-only here).
-/
module

public import Spec.go_etcd_io.bbolt.DB__Begin_kv

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

/-- **Trust boundary** (2026-11-06, restated, `notes/begin-tok-plan.md`): why the read half's
`threadTok` is faithful. In bbolt (the fork `upamanyus/bbolt` `743299d8cec8`, as upstream v1.5.0), `DB.Begin(false)` (`db.go:841`) calls `beginTx` (`db.go:866`),
which takes `db.mmaplock.RLock()` (`db.go:875`) and keeps it past its return on success: it is
released only when the transaction ends, by `Tx.Rollback` (`tx.go:303`) → `nonPhysicalRollback`
(`tx.go:313`) → `close` (`tx.go:353`) → `db.removeTx` (`tx.go:378`), whose first statement is
`db.mmaplock.RUnlock()` (`db.go:951`). On `beginTx`'s errors it is released before returning
(`db.go:879`, `:886`): the error branch gives the token back. `sync.RWMutex` counts at most
`rwmutexMaxReaders = 2 ^ 30` readers (go1.27.3 `sync/rwmutex.go:47`; one more with a writer
pending fatals in `rUnlockSlow`, `:130-132`), so each open read transaction is charged a thread's
token, which `Tx.Rollback_kv` returns, and `Open_kv`'s `ThreadBoundLe GF (2 ^ 29)` bounds the
tokens (as the proved `DB.Begin.spec`, `Proof/go_etcd_io/bbolt/DB__Begin.lean`, lends it to
`mmaplock`'s reader pool). A write transaction (`beginRWTx`) takes no `mmaplock` reader slot
(`mmaplock`'s only uses are `db.go:492`, `:775`, `:875-886`, `:951`), so it is charged nothing. The rest
of the triple: `InvBbolt.lean` and `notes/decisions.md`, "The backend: the buffers, bbolt as a
key-value contract, the locks and the views". -/
axiom bbolt.DB.Begin_kv.wp_proof : bbolt.DB.Begin_kv.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
