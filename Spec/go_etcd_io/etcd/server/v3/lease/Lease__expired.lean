/-
`(*Lease).expired()` (`server/lease/lease.go:51-53`): `l.Remaining() <= 0`. Lean-first (no Rocq
counterpart). The spec the expiry loop uses (`findExpiredLeases`, `lessor.go:728-751`); a
trust-boundary axiom (`Proof/go_etcd_io/etcd/server/v3/lease/Lease__expired.lean`, since
prove-ps2-newlessor5, 2026-11-21, when `NewLessor` was proved over the real code: until then a
hypothesis of the expiry loop's proofs), the one `NewLessor`'s proof rests on (in place of
`NewLessor`'s whole axiom; `notes/axiom-review/lease-expired-payload.md`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.LessorBackend

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.lease lease

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- **`l.expired()` of a lease of a lessor's map, under the lessor's lock** (`leaseMeta id l q`, the
lock's share of the lease): `Remaining()` (`lease.go:117-124`, which read-locks `l.expiryMu` with a
slot of the lease's pool: the level-0 token and the thread bound, as `Remaining.spec`) compared with
`0`. The result is `true` only if the deployment premise `leasesNoExpiry` is false: `true` means the
lease's expiry is set and the clock is past it, i.e. the lease has expired while the program runs,
which `leasesNoExpiry` excludes for every lease of every lessor the program creates.

Why it is not proved: Perennial's `time.Now` (and `time.Until`, `Remaining`'s) returns an arbitrary
reading (the model has no clock), so `Remaining()`'s result is arbitrary and nothing in the model
ties it to `leasesNoExpiry`, an opaque premise about the real clock. The post is a pure implication
under the triple, not a pure fact: in the model `expired()` may return `true`, and a run of the
model where it does is one the premise excludes (a pure `b = true → ¬ leasesNoExpiry` outside a
triple would let Lean derive `¬ leasesNoExpiry` from the model). To be retired once Perennial
models `time.Now`'s monotonic reading (then `leasesNoExpiry` can be a statement about the readings
and this a lemma). -/
abbrev lease.Lease.expired.spec : Prop :=
  ∀ (γl : GName) (l : Loc) (id : w64) (q : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ isLeaseObj γl l ∗
      leaseMeta id l q ∗ levelTok leaseLvl ∗ ⌜threadBound GF ≤ 2 ^ 30 - 1⌝ }}
    (App (Val (l @!! go.GoType.PointerType Lease.ty @!! go!"expired")) (Val #()))
  {{ (b : Bool), RET #b; leaseMeta id l q ∗ levelTok leaseLvl ∗ ⌜b = true → ¬ leasesNoExpiry⌝ }}

end spec

end EtcdGrove
end Perennial
