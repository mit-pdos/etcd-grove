/-
Lean-first (no Rocq counterpart). Trace-check's layer D, S7 (part 1) (2026-11-11).

`Main()` (`examples/raft/tracecheck/main.go`), the closed program: `RunConcurrent(cfg)` at
`DefaultCConfig()` with `cfg.Nodes = 1 + below(5)` (2026-11-24: until then `DefaultCConfig()`'s three), then `NewTrace(ConvertEvents(c.Events()))`, then `CheckTrace(tr, true)`, panicking if the cluster did
not start, if the trace is not one the specification reads, or unless the verdict is `TLCOK`. Its
spec: it returns (so it never panics: the trace of every run passes raft's TLA+ trace validation),
from package initialization and `context`'s `isClosedchanInit` (`RunConcurrent`'s proposer's
contexts; the adequacy theorem gets it from the program's initialization, as `raft_kv.Main.spec`),
for a time-receipt bound `tcRunFits GF` (`receiptBound GF + 5 ≤ 2^61`, named since 2026-11-12,
`Fits.lean`; `RunConcurrent.spec`'s: the traced cluster's at most five bootstrap entries within raft's
`readyFits`; it also bounds the event count below the checker's `numBound = 2^61`, through the
recorder's receipts), the thread bound `ThreadBoundLe GF (2^31)` and the bootstrap log's premise at
every size `Main` can draw (`tracecheck.premises nv (tracecheck.bootLog nv)`, `Defs.lean`; the log's
pure facts are proved, `tracecheck.bootLogFacts_bootLog`), passed to `RunConcurrent` at the size drawn
(`notes/trace-check-design.md` §2.1).
-/
module

public import RaftTla.Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Base
public import RaftTla.Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Defs
public import Perennial.ProgramLogic.Bounds
public import RaftTla.Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Fits

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace TraceCheck

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Assumptions]

/-- See the file header. -/
abbrev Main.spec : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 31)], tcRunFits GF →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck ∗
      context.isClosedchanInit ∗
      □ (∀ nv : Nat, ⌜1 ≤ nv ∧ nv ≤ tracecheck.maxNodes⌝ -∗
          tracecheck.premises nv (tracecheck.bootLog nv)) }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Main)) (Val #()))
  {{ RET #(); True }}

end spec

end TraceCheck
end EtcdGrove
end Perennial
