-- The copy for the part `KvNet/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/InvTraceLogger.lean` (etc/copy-part.py; rerun it, do not edit).
/-
Lean-first (no Rocq counterpart). **The trace logger's contract, in raft's build without `with_tla`**
(`state_trace_nop.go`: `type TraceLogger interface{}`, and every trace hook an empty function), the
build this tree verifies and etcd ships.

`isTraceLogger γt tl`: `tl` is nil. In this build no value is a logger raft reports to: the hooks do
nothing, whatever `Config.TraceLogger` holds, so no trace is ever extended. The traced half of the
hooks' specs and of raft's capability (`trCapB (some γd) …`, `TraceFire (some γd) …`) asks for
`isTraceLogger` of a non-nil logger and is therefore empty here, which is what lets the empty hooks
meet the same specs as the `with_tla` build's (`RaftTla/`, whose module of this name has the real
contract: a `TraceEvent` method that appends the event to the trace). The proofs above the hooks
are the same text in both trees (`etc/gen-raft-tla.py`).
-/
module

public import KvNet.Proof.go_etcd_io.raft.v3.InvTrace

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section trace
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-! ## The logger's contract -/

/-- The trace logger's contract in the build without `with_tla`: nil (the file header). -/
def isTraceLogger (γt : GName) (tl : GoInterface) : IProp GF :=
  iprop(⌜tl = interface.nil⌝)

instance isTraceLogger_persistent (γt : GName) (tl : GoInterface) :
    Persistent (isTraceLogger (GF := GF) γt tl) := by
  unfold isTraceLogger; infer_instance

/-- A nil logger meets the contract, for any trace. -/
theorem isTraceLogger_nil (γt : GName) : ⊢ isTraceLogger (GF := GF) γt interface.nil := by
  unfold isTraceLogger
  ipureintro; rfl

/-- **No traced logger in this build**: the contract of a non-nil logger is absurd. What the empty
hooks' proofs use on the traced half of their specs. -/
theorem isTraceLogger_ne_nil (γt : GName) (tl : GoInterface) (h : tl ≠ interface.nil) :
    isTraceLogger (GF := GF) γt tl ⊢ False := by
  unfold isTraceLogger
  iintro %h'
  exact absurd h' h

end trace

end EtcdGrove
end Perennial
