/- Lean-first (no Rocq counterpart). The proof of `runner.checkStoreRange`: Draft, to come.

The outline: `err == ErrCompacted` (`errVars.law`: mvcc's error variables are distinct
`errors.New` values) holds exactly in `rangeOutcomeC`'s compacted case; there `rangeRev σ.rev ro.Rev
< σ.crev ≤ σ.rev` (`reach_bounds`) makes the revision `ro.Rev`, positive, and `cmpHi_acc` at the
compaction revision's lower bound (`readQ`) bounds `cmpHi` above it. Otherwise (the live case;
`res ≠ null` rules out the context's), the result's revision is `σ.rev` (every case of
`rangeOutcome`), `inBounds` holds by `lo ≤ σ.rev` and `revHi_acc`, the snapshot extends `readQ`'s
lower bound, and `checkRangeAt` at `(σ.rev, clo)` takes `rangeOutcomeC_lower` and `hist_match`. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__checkStoreRange
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.check
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.inBounds
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.history__snapshot
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.checkRangeAt

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

theorem runner.checkStoreRange.wp_proof
    (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (herr : mvcc.api.errVars.law (GF := GF) (hG := hG))
    (wp_check : check.spec (GF := GF) (hG := hG))
    (wp_inBounds : inBounds.spec (GF := GF) (hG := hG))
    (wp_snapshot : history.snapshot.spec (GF := GF) (hG := hG))
    (wp_checkRangeAt : checkRangeAt.spec (GF := GF) (hG := hG)) :
    runner.checkStoreRange.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end mvccfull
end EtcdGrove
end Perennial
