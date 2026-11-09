/- Lean-first (no Rocq counterpart). The proof of `runner.readOne`: Draft, to come.

The outline (member `i`'s part of `rdOwn`, its handles `isInc`, `isMvcc`'s shape by `shapes.law`):
the floors by `revLo_acc`/`cmpLo_acc` (`Int64.Load`), giving lower bounds `n ≥ lo`, `c ≥ clo + 1`;
`pick.specW` at `6` with `readMixOk` gives an alternative of positive weight, not `5`
(`readMixOk_ne5`). Each read's update is `reader_au` (`Q σ := ret share ∗ readQ σ ∗ n ≤ σ.rev ∧
c ≤ σ.crev + 1`), so the value read is in `[lo, ·]` and its ceiling (`inBounds` with
`revHi_acc`/`cmpHi_acc` at `readQ`'s lower bounds) holds:
- `Rev` (`KV.Rev.contract`: `W64 σ.rev`), `FirstRev` (`KV.FirstRev.contract`: `W64 σ.crev`,
  `-1 ≤ σ.crev`);
- a read transaction (`KV.Read.contract`, then `Txn.Rev`/`Txn.FirstRev` at `.read σ`): the bounds as
  above; the snapshot (`history.snapshot` from `readQ`'s lower bound) has the states up to `σ.rev`
  (`hist_match`); each `Txn.Range` gives `rangeOutcomeC` at `σ.log`, `σ.rev`, `σ.crev`, which is
  `checkRangeAt`'s premise at `(W64 σ.rev, W64 σ.crev)` (`txn.LogOk` from the range's `LogWf'` and
  `reach_bounds`); `Txn.End` returns the reader token;
- a read-only transaction: the same through `NewReadOnlyTxnWrite.spec` (`.read σ` kept), and
  `Txn.Changes` at `.read σ` gives `0` changes;
- the store's `Range` (`KV.Range.contract`, `todo`: `res ≠ null`): `checkStoreRange`'s premise
  with `Q` as above (`genRange` at the loaded `revHi`, any value). -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__readOne
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__checkStoreRange
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__genRange
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.pickW
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.choose
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.check
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.inBounds
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.history__snapshot
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.checkRangeAt
public import Spec.context.TODO

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccfull

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem runner.readOne.wp_proof
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hreach : mvcc.api.mvccState_reachable.law (GF := GF) (hG := hG))
    (wp_pickW : pick.specW (GF := GF) (hG := hG))
    (wp_inBounds : inBounds.spec (GF := GF) (hG := hG))
    (wp_traceTODO : traceutil.TODO.spec (GF := GF) (hG := hG))
    (wp_snapshot : history.snapshot.spec (GF := GF) (hG := hG))
    (wp_choose : choose.spec (GF := GF) (hG := hG))
    (wp_genRange : runner.genRange.spec (GF := GF) (hG := hG))
    (wp_ctxTODO : context.TODO.spec (GF := GF) (hG := hG))
    (wp_checkRangeAt : checkRangeAt.spec (GF := GF) (hG := hG))
    (wp_roTxn : mvcc.api.NewReadOnlyTxnWrite.spec (GF := GF) (hG := hG))
    (wp_check : check.spec (GF := GF) (hG := hG))
    (wp_checkStoreRange : runner.checkStoreRange.spec (GF := GF) (hG := hG)) :
    runner.readOne.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end mvccfull
end EtcdGrove
end Perennial
