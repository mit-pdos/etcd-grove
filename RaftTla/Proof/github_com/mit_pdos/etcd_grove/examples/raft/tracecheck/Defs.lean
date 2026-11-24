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

Until 2026-11-24 the closed theorem took both as premises (Q32: "follow the etcd examples"). Since then
(premises to axioms) the Iris premise is a theorem, `premises_of_spec`, from the trust-boundary axiom
`proto.MarshalBootConfChange.wp_proof` and the pure fact `BootWireFacts` (the log's bytes), which the
closed theorem takes in its place.

**Non-vacuity** (2026-11-24): until then `bootMarshal` began with `⌜∀ c ∈ ctxs, c ≠ []⌝`, false at
this harness's contexts `[[], [], []]`, so the premise was `⌜False⌝ ∗ …` and `raft_tracecheck_safe`
and `raft_tracecheck_robust` held vacuously (from `00e0cbcf74`, 2026-11-10, to the fix). Now an
empty context is the `nil` slice (`peersCtx`, `bootConfChange`), which is what `Peer{ID: i}` carries
(`tcPeers_ctx`), and `premises_of_marshal` below states that the premise follows from `proto.Marshal`'s
Go contract at the harness's conf changes alone, with no pure side condition: a premise change that
adds one breaks it.
-/
module

public import RaftTla.Spec.go_etcd_io.raft.v3.Api
public import RaftTla.Proof.go_etcd_io.raft.v3.BootMarshal

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

/-- **The bootstrap log's bytes** (premises to axioms, 2026-11-24; see the file header): the `i`-th
entry's data is `proto.Marshal`'s bytes of `ConfChange{Type: AddNode, NodeId: i}` (`bootWire`:
`ccBootWire i []`, the four bytes `0x10 0x00 0x18 i`; `TestBootWireVectors`). -/
abbrev BootWireFacts (boot : List LogEntry) : Prop :=
  bootWire [W64 1, W64 2, W64 3] [[], [], []] boot

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

/-- **The premise follows from `proto.Marshal`'s trust-boundary spec** (premises to axioms,
2026-11-24; until then a premise of the closed theorem): at the harness's conf changes (`AddNode i`, no
context: the `nil` slice), given the log's bytes (`BootWireFacts`) and `proto`'s initialization. -/
theorem premises_of_spec (wpM : proto.MarshalBootConfChange.spec (GF := GF) (hG := hG))
    (boot : List LogEntry) (Hw : BootWireFacts boot) :
    isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ⊢ premises (GF := GF) boot :=
  bootMarshal_of_spec wpM _ _ boot Hw

end defs

end tracecheck
end EtcdGrove
end Perennial
