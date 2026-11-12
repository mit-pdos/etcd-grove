/-
Lean-first (no Rocq counterpart). **The trace check's `Main`: its named premises** (Q32, the user's
decision, 2026-11-11; `notes/trace-check-design.md` §1.1), modelled on `etcd_putget.BootFacts` and
`etcd_putget.premises` (`examples/etcd/putget/Defs.lean`).

* **The pure facts** (`tracecheck.BootLogFacts`): the bootstrap log `StartNode` builds for the peers
  `1, 2, 3` (each `Peer{ID: i}`, `Context` nil), as Go computes it: three conf-change entries of term
  `1` whose data is the marshalled `ConfChange{Type: AddNode, NodeID: i}` (the node API's `BootLog`).
  Named apart from layer B's `TraceCheck.BootFacts C L` (`MainSim.lean`, over `newTrace`).
* **The Iris premise** (`tracecheck.premises`, persistent): `proto.Marshal`'s contract at the
  bootstrap log's conf changes. Each of the three `StartNode`s marshals `AddNode i`, and the call
  returns the bytes of `boot`'s `i`-th entry (`bootMarshal`). Raft's proof needs the three voters'
  logs to be one committed log; `proto.MarshalConfChange.spec` gives only bytes that decode to the
  change.

No axiom: the closed theorem takes both as premises (Q32: "follow the etcd examples").
-/
module

public import Spec.go_etcd_io.raft.v3.Api

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace tracecheck

open Iris Iris.BI go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- See the file header. -/
abbrev BootLogFacts (boot : List LogEntry) : Prop :=
  BootLog [W64 1, W64 2, W64 3] [[], [], []] boot

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **`Main`'s named premise** (see the file header). -/
abbrev premises (boot : List LogEntry) : IProp GF :=
  bootMarshal [W64 1, W64 2, W64 3] [[], [], []] (LogEntry.toEntries boot 0)

end defs

end tracecheck
end EtcdGrove
end Perennial
