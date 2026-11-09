/-
Lean-first (no Rocq counterpart). Trace-check's layer D (2026-11-09).

`ConvertEvents(events)` (`examples/raft/tracecheck/main.go`): raft's events as the checker reads
them. Its spec: given a slice holding the trace `L` (`traceEventsRep`, what `Events` returns), whose
copied strings are ASCII (`TraceEv.Ascii`), it returns a slice holding `L.map evConv` as `NewTrace`
reads its input (`eventsRO`, read-only).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Recorder
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Convert

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace TraceCheck

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Assumptions]
variable [etcdraft_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

/-- See the file header. -/
abbrev ConvertEvents.spec : Prop :=
  ∀ (sl : GoSlice) (L : List TraceEv),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck ∗
      traceEventsRep sl L ∗ ⌜∀ e ∈ L, TraceEv.Ascii e⌝ }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.ConvertEvents)) (Val #sl))
  {{ (out : GoSlice), RET #out; Etcdraft.eventsRO out (L.map TraceSim.evConv) }}

end spec

end TraceCheck
end EtcdGrove
end Perennial
