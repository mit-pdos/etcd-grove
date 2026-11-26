/- Lean-first (no Rocq counterpart).

# The WAL tester (`examples/etcd/wal`): the top-level robustness result, proved

`etcd_wal_safe`, stated in
`WalTester/Spec/github_com/mit_pdos/etcd_grove/examples/etcd/wal/TopLevelRobustness.lean`, from the
tester's bounded crash safety (`etcd_wal_crash_safety_bounded`, `Adequacy.lean`) through
`Robustness.Robust.of_single_crashing`, as the osfs examples (`osfs/bboltfs`: the thread bound from the
step bound, `RealCrashThreadsBelow.of_single`).
-/
module

public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.TopLevelRobustness
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.Adequacy

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode go_etcd_io.raft.v3 Fs WalEnc WalFs

attribute [local instance] fsExts fsExtsInterp tExtsSem tFsSem tFsSemOk tHasFs tSat tSatL

section statement
variable [GoGlobalContext]

/-- `etcd_wal_safe.spec`
(`WalTester/Spec/github_com/mit_pdos/etcd_grove/examples/etcd/wal/TopLevelRobustness.lean`). -/
theorem etcd_wal_safe : etcd_wal_safe.spec := by
  -- the Go context, the Go semantics, the packages' 25 assumptions, then the premises
  intro lctx sem _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  intro σ g e Hinit hRe hr ho hne Hfirst
  haveI : go.BasicIntoValInj := inferInstance
  refine Robustness.Robust.of_single_crashing fun hfr n κs t2 σ2 b hn Hsteps => ?_
  exact (etcd_wal_crash_safety_bounded (GF := fsGF) tAbsPre tStepBound (n + 2) (Nat.le_refl _)
    σ g e hfr.1 hfr.2.1 Hinit hRe hr ho hne Hfirst n κs t2 σ2 b Hsteps hn hfr.2.2
    (RealCrashThreadsBelow.of_single hfr.2.2)).2

end statement

end etcd_wal
end EtcdGrove
end Perennial

#print axioms Perennial.EtcdGrove.etcd_wal.etcd_wal_safe

end
