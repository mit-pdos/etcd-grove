/-
The trust boundary: `Spec/go_etcd_io/bbolt/Open_kv.lean` (bbolt is names-only here).
-/
module

public import Spec.go_etcd_io.bbolt.Open_kv

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

/-- **Trust boundary** (2026-11-06, restated with `[ThreadBoundLe GF (2 ^ 29)]`,
`notes/begin-tok-plan.md`, Q2; reviewed with the `axiom` skill, survives:
`notes/axiom-review/begin-tok-restated.md`): a stronger premise, so a weaker axiom. In bbolt (the
fork `upamanyus/bbolt` `743299d8cec8`, as upstream v1.5.0) each open read transaction holds a
`db.mmaplock` reader slot (`RLock` at `db.go:875`, `RUnlock` at `db.go:951`), and `DB.Close`
(`db.go:768-779`) or a growing commit's `mmap` (`db.go:492`) takes `mmaplock`'s write side; with
exactly `2 ^ 30` readers in when that writer subtracts, the next `RUnlock` fatals (go1.27.3
`sync/rwmutex.go:130-132`). The count under the bound: paid readers ≤ tokens < `2 ^ 29`
(`DB.Begin_kv` charges a `threadTok` per read transaction), and bbolt's transient readers (`View`,
`db.go:1011`; `freepages`, `db.go:1351`: one per live thread, released within the call) < `2 ^ 29`;
so fewer than `2 ^ 30` readers. That is why the bound is `2 ^ 29` and not `2 ^ 30` (the proved
`Open.spec`'s bound, D3). -/
axiom bbolt.Open_kv.wp_proof : bbolt.Open_kv.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
