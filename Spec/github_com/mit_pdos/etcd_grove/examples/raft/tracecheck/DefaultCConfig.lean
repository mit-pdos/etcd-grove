/-
Lean-first (no Rocq counterpart). Trace-check's layer D, S7 (part 1) (2026-11-11).
`DefaultCConfig()` (`examples/raft/tracecheck/concurrent.go`): the closed program's run, three voters,
60 proposals 10ms apart, settling 150ms, ticks every 10ms, delays below 10ms, 5% of the messages
dropped, no configuration change, no snapshot, three isolations of 200ms. Its spec: it returns that
value (`defaultCConfig`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace TraceCheck

open Iris Iris.BI

section defs
variable [GooseExts]

/-- `DefaultCConfig()`'s value (durations in nanoseconds, `time.Millisecond = 10^6`). -/
def defaultCConfig : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.CConfig :=
  { Nodes' := W64 3, ExtraNodes' := 0, Proposals' := W64 60, ConfChanges' := 0,
    ProposeGap' := W64 10 * W64 1000000, Settle' := W64 150 * W64 1000000,
    Tick' := W64 10 * W64 1000000, MaxDelay' := W64 10 * W64 1000000, DropPct' := W64 5,
    SnapshotEvery' := 0, Isolations' := W64 3, IsolateFor' := W64 200 * W64 1000000 }

end defs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Assumptions]

/-- See the file header. -/
abbrev DefaultCConfig.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.DefaultCConfig)) (Val #()))
  {{ RET #defaultCConfig; True }}

end spec

end TraceCheck
end EtcdGrove
end Perennial
