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

/-- **The premise is `proto.Marshal`'s contract alone** (non-vacuity guard, 2026-11-24; see the file
header): for each of the three conf changes `Bootstrap` builds (`AddNode i`, no context: the `nil`
slice), `proto.Marshal` returns the `i`-th boot entry's bytes. No pure fact about the contexts or the
log is asked for, so the premise is as satisfiable as that Go fact is true. -/
theorem premises_of_marshal (boot : List LogEntry) :
    (□ ∀ (k : Nat) (p : Loc) (dq : DFrac) (m : ConfChangeM) (e : EntryM)
      (_ : [W64 1, W64 2, W64 3][k]? = some m.nodeId ∧
        ([[], [], []] : List (List w8))[k]? = some m.context ∧
        (LogEntry.toEntries boot 0)[k]? = some e ∧ m.type = W32 0 ∧ m.id = W64 0)
      (Φ : val → IProp GF),
      bootConfChange p dq m -∗
      (∀ (d : GoSlice), bootConfChange p dq m -∗ d ↦* e.Data' -∗ Φ (PairV #d #interface.nil)) -∗
      WP (App (Val (@! google_golang_org.protobuf.proto.Marshal))
            (Val #(interface.mkOk (go.GoType.PointerType raftpb.ConfChange.ty) #p))) {{ Φ }})
    ⊢ premises (GF := GF) boot := by
  unfold premises bootMarshal
  exact .rfl

end defs

end tracecheck
end EtcdGrove
end Perennial
