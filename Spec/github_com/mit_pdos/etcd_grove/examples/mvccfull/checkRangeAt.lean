/- Lean-first (no Rocq counterpart).

`checkRangeAt(keys, states, cur, cmp, q, res, err)` (`examples/mvccfull/mvccfull.go`): returns when
the range read's result `(res, err)` is what mvcc's API promises for the request `q` in a
transaction at revision `cur` of a store compacted at `cmp`.

**The triple** (mvccrand's `checkRange`, with the compaction): the keys `keys` are strictly
increasing (`runner.keys`, `keysOf_sorted`); the tester's states `states[r]` (maps, at any
fractions) match the store's state `stateAt L r` of a well-formed log `L` (`txn.LogOk`) over those
keys (`stMatch`) for every revision `r` from `cmp` to `cur` (the ones below `cmp` are never read: a
read there must fail); and `(res, err)` is `Txn.Range.contract`'s outcome at `L`, `cur` and the
compaction revision `cmp` (`rangeOutcomeC`: below `cmp`, `ErrCompacted` with `{nil, -1, 0}`; past
`cur`, `ErrFutureRev`; else `rangeOutcome`'s answer), not the context's error (`res ≠ null`). A
caller holding the contract's `rangeOutcomeC r err k.readLog k.readRev k.state.crev …` passes
`cmp` with `sint.Z cmp = k.state.crev` (the transaction's `FirstRev()`, `-1` when nothing is
compacted). Then it returns, everything given back.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.Pending

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- See the file header. -/
abbrev checkRangeAt.spec : Prop :=
  ∀ (keys : GoSlice) (ks : List GoString) (dks : DFrac) (states : GoSlice) (dsl : DFrac)
    (ms : List GoMap) (Ms : List (GMap GoString kvRec)) (dqs : List DFrac) (cur cmp : w64)
    (q : rangeReq) (kk e : GoString) (dk de : DFrac) (res : Loc) (err : GoInterface) (L : Log),
  ks.Pairwise go.GoStringLt → txn.LogOk L → 0 ≤ sint.Z cur → sint.nat cur < ms.length →
  (∀ r : Nat, sint.Z cmp ≤ (r : Int) → r ≤ sint.nat cur →
    ∃ M, Ms[r]? = some M ∧ stMatch ks M (stateAt L r)) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccfull ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      keys ↦*{dks} ks ∗ states ↦*{dsl} ms ∗ statesAt ms Ms dqs ∗ q.key' ↦*{dk} kk ∗
      q.end' ↦*{de} e ∗ ⌜res ≠ null⌝ ∗
      rangeOutcomeC res err L cur (sint.Z cmp) (decide (q.end' = slice.nil)) kk e q.ro' }}
    (App (App (App (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.mvccfull.checkRangeAt)) (Val #keys)) (Val #states))
      (Val #cur)) (Val #cmp)) (Val #q)) (Val #res)) (Val #err))
  {{ RET #(); keys ↦*{dks} ks ∗ states ↦*{dsl} ms ∗ statesAt ms Ms dqs ∗ q.key' ↦*{dk} kk ∗
      q.end' ↦*{de} e }}

end spec

end mvccfull
end EtcdGrove
end Perennial
