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

/-- **Trust boundary** (2026-11-06, restated, `notes/begin-tok-plan.md`; reviewed with the `axiom`
skill, survives: `notes/axiom-review/begin-tok-restated.md`): why the read half's `threadTok` is
faithful. In bbolt (the fork `upamanyus/bbolt` `743299d8cec8`, as upstream v1.5.0), `DB.Begin(false)`
(`db.go:841`) calls `beginTx` (`db.go:866`), which takes `db.mmaplock.RLock()` (`db.go:875`) and keeps
it past its return on success: it is released only when the transaction ends, by `Tx.Rollback`
(`tx.go:303`), whose call of `nonPhysicalRollback` (`tx.go:308`) calls `close` (`tx.go:320`), whose
call of `db.removeTx` (`tx.go:378`) runs `db.mmaplock.RUnlock()` first (`db.go:951`). On `beginTx`'s
errors it is released before returning (`db.go:879`, `:886`): the error branch gives the token back.
`sync.RWMutex` (go1.27.3 `sync/rwmutex.go:47`, `rwmutexMaxReaders = 2 ^ 30`) fatals when a writer
(`DB.Close`, `db.go:775`, or a growing commit's `mmap`, `db.go:492`) subtracts `2 ^ 30` with exactly
`2 ^ 30` readers in, on the next `RUnlock` (`rUnlockSlow`, `:130-132`). So each open read transaction
is charged a thread's token, which `Tx.Rollback_kv` returns (as the proved `DB.Begin.spec`,
`Proof/go_etcd_io/bbolt/DB__Begin.lean`, lends it to `mmaplock`'s reader pool), and `Open_kv`'s
`ThreadBoundLe GF (2 ^ 29)` bounds the readers: paid readers ≤ tokens < `2 ^ 29`, and bbolt's
transient readers, taken through `beginTx` and released within one call by one thread (`View`,
`db.go:1011`; `freepages`, `db.go:1351`), are at most one per live thread, < `2 ^ 29`; so fewer than
`2 ^ 30` readers in all, which is why the bound is `2 ^ 29` and not `2 ^ 30`. A write transaction
(`beginRWTx`) takes no `mmaplock` reader slot, so it is charged nothing. The rest of the triple:
`InvBbolt.lean` and `notes/decisions.md`, "The backend: the buffers, bbolt as a key-value contract,
the locks and the views". -/
axiom bbolt.DB.Begin_kv.wp_proof : bbolt.DB.Begin_kv.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
