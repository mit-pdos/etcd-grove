/-
Port of election_proof/spec_traceReplicate.v (feb5c73d4).
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `traceReplicate(r, es...)`: for each entry of `es` of type `EntryNormal`
(`es[i].GetType()`, read before the logger is), `traceNodeEvent(rsmReplicate, r)`; the entries
are only read. Under `TraceLoggerOk` (increment 1, `notes/trace-validation-hooks.md`: the logger is nil) no
event is reported. Until 2026-11-08 the translated build was the no-op one (`state_trace_nop.go`)
and the spec owned nothing; Draft S4 of `notes/trace-validation-plan.md` widens `TraceLoggerOk`
to a logger. -/
abbrev traceReplicate.spec : Prop :=
  ∀ (r : Loc) (es : GoSlice) (dq : DFrac) (ents : List EntryM) (tl : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ entsPts es dq ents ∗
      r.[raft, go!"traceLogger"] ↦□ tl ∗ ⌜TraceLoggerOk tl⌝ }}
    (App (App (Val #(functions traceReplicate [])) (Val #r)) (Val #es))
  {{ RET #(); entsPts es dq ents }}

end spec

end EtcdGrove
end Perennial
