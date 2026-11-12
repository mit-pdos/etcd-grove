/-
Lean-first (no Rocq counterpart). Trace-check's layer D, S7 (part 1) (2026-11-11).

`Main()` (`examples/raft/tracecheck/main.go`), the closed program: `RunConcurrent(DefaultCConfig())`,
then `NewTrace(ConvertEvents(c.Events()))`, then `CheckTrace(tr, true)`, panicking if the cluster did
not start, if the trace is not one the specification reads, or unless the verdict is `TLCOK`. Its
spec: it returns (so it never panics: the trace of every run passes raft's TLA+ trace validation),
from package initialization and `context`'s `isClosedchanInit` (`RunConcurrent`'s proposer's
contexts; the adequacy theorem gets it from the program's initialization, as `raft_kv.Main.spec`),
for a time-receipt bound with `tcRunFits GF` (`receiptBound GF + 3 ≤ 2^61`, named since 2026-11-12,
`Fits.lean`; `RunConcurrent.spec`'s: the traced cluster's three bootstrap entries within raft's
`readyFits`; it also bounds the event count below the checker's `numBound = 2^61`, through the
recorder's receipts).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Fits

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace TraceCheck

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Assumptions]

/-- See the file header. -/
abbrev Main.spec : Prop :=
  tcRunFits GF →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck ∗
      context.isClosedchanInit }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Main)) (Val #()))
  {{ RET #(); True }}

end spec

end TraceCheck
end EtcdGrove
end Perennial
