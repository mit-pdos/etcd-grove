/-
Lean-first (no Rocq counterpart). **The trace check's `Main`: its named premises** (Q32, the user's
decision, 2026-11-11; `notes/trace-check-design.md` §1.1), modelled on `etcd_putget.BootFacts` and
`etcd_putget.premises` (`examples/etcd/putget/Defs.lean`).

* **The pure facts** (`tracecheck.BootLogFacts n`): the bootstrap log `StartNode` builds for the peers
  `1, …, n` (each `Peer{ID: i}`, `Context` nil), as Go computes it: `n` conf-change entries of term
  `1` whose data is the marshalled `ConfChange{Type: AddNode, NodeID: i}` (the node API's `BootLog`).
  Named apart from layer B's `TraceCheck.BootFacts C L` (`MainSim.lean`, over `newTrace`).
  (2026-11-24) No longer a premise: `bootLog n` is the log Go computes for the voters `1 … n`
  (`ccBootWire`), and `bootLog_bootLog` proves its facts, since `ccDecodeV1` is a function
  (`cc1DecodeRaw`, checked against protobuf-go). The same day `Main` started drawing `n` in
  `1 … maxNodes` (until then `n = 3`).
* **The Iris premise** (`tracecheck.premises n`, persistent): `proto.Marshal`'s contract at the
  bootstrap log's conf changes. Each of the `n` `StartNode`s marshals `AddNode i`, and the call
  returns the bytes of `boot`'s `i`-th entry (`bootMarshal`). Raft's proof needs the voters'
  logs to be one committed log; `proto.MarshalConfChange.spec` gives only bytes that decode to the
  change.

Until 2026-11-24 the closed theorem took both as premises (Q32: "follow the etcd examples"). Since then
the pure facts are proved (`bootLog n` above), and (premises to axioms) the Iris premise is a theorem,
`premises_of_spec`, at `bootLog n` for every `n` `Main` can draw, from the trust-boundary axiom
`proto.MarshalBootConfChange.wp_proof` and the log's bytes (`bootWire_bootLog`).

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
public import RaftTla.Proof.go_etcd_io.raft.v3.CCModel

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace tracecheck

open Iris Iris.BI go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- **The most bootstrap voters `Main` starts** (`main.go`: `cfg.Nodes = 1 + below(5)`, 2026-11-24;
until then always `3`, `DefaultCConfig()`'s). -/
def maxNodes : Nat := 5

/-- The bootstrap voters `1, …, n` (`concurrent.go`: `Peer{ID: i}` for `i = 1 … cfg.Nodes`). -/
def bootVoters (n : Nat) : List w64 := (List.range n).map fun j => W64 ((j : Nat) + 1)

/-- See the file header: the bootstrap log of the `n` voters `1 … n` (`bootVoters`), no contexts
(until 2026-11-24 at `n = 3` only). -/
abbrev BootLogFacts (n : Nat) (boot : List LogEntry) : Prop :=
  BootLog (bootVoters n) (List.replicate n []) boot

/-- **The bootstrap log of `n` voters** (2026-11-24, until then a premise `boot` with its facts
`BootLogFacts boot`): the entries `StartNode` builds for the peers `1 … n`, each `Context` nil:
term `1`, type `EntryConfChange`, data the bytes `proto.Marshal` writes for `ConfChange{Type: AddNode,
NodeId: i}` (`ccBootWire`, checked against protobuf-go by `ConfChangeWireVectors.lean`). -/
def bootLog (n : Nat) : List LogEntry :=
  (bootVoters n).map fun i => ⟨W64 1, W32 1, ccBootWire i []⟩

/-- **`bootLog n` is the bootstrap log of the voters `1 … n` without contexts**: the facts that were the
premise `BootLogFacts`, now proved (the decoder is a function since 2026-11-24, `ccDecodeV1`). -/
theorem bootLog_bootLog (n : Nat) (hn : n < 2 ^ 61) :
    BootLog (bootVoters n) (List.replicate n []) (bootLog n) := by
  refine ⟨by simp [bootLog], by simp [bootLog, bootVoters]; omega, ?_⟩
  intro k e hk
  simp only [bootLog, List.getElem?_map, Option.map_eq_some_iff] at hk
  obtain ⟨i, hi, rfl⟩ := hk
  have hk : k < n := by
    have := (List.getElem?_eq_some_iff.1 hi).1
    simpa [bootVoters] using this
  refine ⟨i, [], hi, by simp [hk], rfl, rfl, ?_⟩
  exact ccDecodeV1_bootWire i [] (by simp)

/-- `BootLogFacts n` holds of `bootLog n`. -/
theorem bootLogFacts_bootLog (n : Nat) (hn : n < 2 ^ 61) : BootLogFacts n (bootLog n) :=
  bootLog_bootLog n hn

/-- **The bootstrap log's bytes** (premises to axioms, 2026-11-24; see the file header): the `i`-th
entry's data of `bootLog n` is `proto.Marshal`'s bytes of `ConfChange{Type: AddNode, NodeId: i}`
(`bootWire`: `ccBootWire i []`, the four bytes `0x10 0x00 0x18 i`; `TestBootWireVectors`), by
definition (until the merge with `Main`'s drawn size, a premise `BootWireFacts boot` at three voters). -/
theorem bootWire_bootLog (n : Nat) : bootWire (bootVoters n) (List.replicate n []) (bootLog n) := by
  intro k e id ctx he hid hctx
  simp only [bootLog, List.getElem?_map, Option.map_eq_some_iff] at he
  obtain ⟨i, hi, rfl⟩ := he
  rw [hi, Option.some.injEq] at hid
  subst hid
  rw [List.getElem?_replicate] at hctx
  split at hctx
  · rw [Option.some.injEq] at hctx
    subst hctx
    rfl
  · exact absurd hctx (by simp)

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **`Main`'s named premise** (see the file header), for `n` voters. -/
abbrev premises (n : Nat) (boot : List LogEntry) : IProp GF :=
  bootMarshal (bootVoters n) (List.replicate n []) (LogEntry.toEntries boot 0)

/-- **The premise follows from `proto.Marshal`'s trust-boundary spec** (premises to axioms,
2026-11-24; until then a premise of the closed theorem): at the harness's conf changes (`AddNode i`, no
context: the `nil` slice), for `n` voters, at `bootLog n` (its bytes, `bootWire_bootLog`), given
`proto`'s initialization. -/
theorem premises_of_spec (wpM : proto.MarshalBootConfChange.spec (GF := GF) (hG := hG)) (n : Nat) :
    isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ⊢
      premises (GF := GF) n (bootLog n) :=
  bootMarshal_of_spec wpM _ _ (bootLog n) (bootWire_bootLog n)

/-- **The premise is `proto.Marshal`'s contract alone** (non-vacuity guard, 2026-11-24; see the file
header): for each of the `n` conf changes `Bootstrap` builds (`AddNode i`, no context: the `nil`
slice), `proto.Marshal` returns the `i`-th boot entry's bytes. No pure fact about the contexts or the
log is asked for, so the premise is as satisfiable as that Go fact is true. -/
theorem premises_of_marshal (n : Nat) (boot : List LogEntry) :
    (□ ∀ (k : Nat) (p : Loc) (dq : DFrac) (m : ConfChangeM) (e : EntryM)
      (_ : (bootVoters n)[k]? = some m.nodeId ∧
        (List.replicate n ([] : List w8))[k]? = some m.context ∧
        (LogEntry.toEntries boot 0)[k]? = some e ∧ m.type = W32 0 ∧ m.id = W64 0)
      (Φ : val → IProp GF),
      bootConfChange p dq m -∗
      (∀ (d : GoSlice), bootConfChange p dq m -∗ d ↦* e.Data' -∗ Φ (PairV #d #interface.nil)) -∗
      WP (App (Val (@! google_golang_org.protobuf.proto.Marshal))
            (Val #(interface.mkOk (go.GoType.PointerType raftpb.ConfChange.ty) #p))) {{ Φ }})
    ⊢ premises (GF := GF) n boot := by
  unfold premises bootMarshal
  exact .rfl

end defs

end tracecheck
end EtcdGrove
end Perennial
