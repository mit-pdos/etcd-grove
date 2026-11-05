/- Lean-first (no Rocq counterpart).

`checkRange(states, cur, q, res, err)` (`examples/mvccrand/mvccrand.go`): returns when the range
read's result `(res, err)` is what mvcc's API promises for the request `q` at revision `cur`.

**The triple**: the tester's states `states[r]` (maps, at any fractions) match the store's state
`stateAt L r` of a well-formed log `L` (`txn.LogOk`) for every revision `r ≤ cur`
(`Model.lean`'s `stMatch`); and `(res, err)` is `Txn.Range.contract`'s outcome at `L` and `cur`
when nothing is compacted (`rangeOutcome`, what `rangeOutcomeC` is at compaction revision `-1`,
`rangeOutcomeC_neg`), not the context's error (`res ≠ null`: `Range` of `context.TODO()`). Then it
returns, the states and the request's slices given back. This is the read contract's probe at the
Go level: every check of a read the tester makes (`ErrFutureRev` and its result; `Rev`; the count,
count-only or with the limit's cut; each key-value's key, revisions, version, value, lease) follows
from the contract.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.Model

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccrand mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- The tester's states: the maps `ms` hold `Ms`, at the fractions `dqs`. -/
def statesAt (ms : List Loc) (Ms : List (GMap GoString kvRec)) (dqs : List DFrac) : IProp GF :=
  iprop(⌜ms.length = Ms.length ∧ Ms.length = dqs.length⌝ ∗
    [∗list] x ∈ ms.zip (Ms.zip dqs), x.1 ↦${x.2.2} x.2.1)

/-- See the file header. -/
abbrev checkRange.spec : Prop :=
  ∀ (states : GoSlice) (dsl : DFrac) (ms : List Loc) (Ms : List (GMap GoString kvRec))
    (dqs : List DFrac) (cur : w64) (q : rangeReq) (kk e : GoString) (dk de : DFrac) (res : Loc)
    (err : GoInterface) (L : Log),
  txn.LogOk L → 0 ≤ sint.Z cur → sint.nat cur < ms.length →
  (∀ r : Nat, r ≤ sint.nat cur → ∃ M, Ms[r]? = some M ∧ stMatch M (stateAt L r)) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccrand ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      states ↦*{dsl} ms ∗ statesAt ms Ms dqs ∗ q.key' ↦*{dk} kk ∗ q.end' ↦*{de} e ∗
      ⌜res ≠ null⌝ ∗ rangeOutcome res err L cur (decide (q.end' = slice.nil)) kk e q.ro' }}
    (App (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.mvccrand.checkRange))
      (Val #states)) (Val #cur)) (Val #q)) (Val #res)) (Val #err))
  {{ RET #(); states ↦*{dsl} ms ∗ statesAt ms Ms dqs ∗ q.key' ↦*{dk} kk ∗ q.end' ↦*{de} e }}

end spec

end mvccrand
end EtcdGrove
end Perennial
