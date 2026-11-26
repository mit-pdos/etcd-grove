/-
Lean-first (no Rocq counterpart). #33 parity B1: the steps the proofs of `node.step` and the other
inputs share beyond `HarnessInput.lean`'s:
- `lcpLen_self`: an input that keeps the log keeps the in-progress boundary at the log's end;
- `nodeOwn_drained_reset`: after a drain, the cause cell reset (`n.cause = nil`), node `j` between
  inputs again (S4's, over `Fin R.N`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessInput

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- A list's common prefix with itself is all of it. -/
theorem lcpLen_self : ∀ (l : List EntryM), lcpLen l l = l.length
  | [] => by simp [lcpLen]
  | a :: l => by
    unfold lcpLen
    simp only [List.length_cons, lcpLen_self l, ite_true]

/-- **The run's mode without B1's off features** (`ModeRun`: `γ.R.md = scopeMd γ.scope`; `DrainB1`'s
scope bits): no snapshots, no conf changes, no forwarding, no async storage. -/
theorem rMd_flags {s : H.Scope} {m : H.Mode} {R : AntSim.RunCfg} (hmr : ModeRun s m R)
    (hb1 : DrainB1 s m) :
    R.md.snapshots = false ∧ R.md.confChanges = false ∧ R.md.forwarding = false ∧
      R.md.async = false := by
  rw [hmr.2.2.2.2.1]
  obtain ⟨-, -, -, -, -, -, h1, h2, h3, h4⟩ := hb1
  exact ⟨h1, h2, h3, h4⟩

/-- A transfer request keeps the log (`TransferEndR`: kept, or a leader's sends). -/
theorem transferEndR_log {id to : w64} {r r' : RState} (h : TransferEndR id r to r') :
    r'.p.log = r.p.log := by
  rcases AntSim.transferEndR_p h with h | ⟨-, ms, -, h⟩
  · rw [h]
  · rw [h]; rfl

/-- **The network's types in a run of B1's off features** (`netTypes` without snapshots or
forwarding): S4's, the pre-vote pair, the read-index pair. -/
theorem netTypes_cases {md : RnMode} {t : w32} (h : t ∈ netTypes md) (hs : md.snapshots = false)
    (hf : md.forwarding = false) :
    t = MsgApp ∨ t = MsgAppResp ∨ t = MsgVote ∨ t = MsgVoteResp ∨ t = MsgHeartbeat ∨
      t = MsgHeartbeatResp ∨ t = MsgPreVote ∨ t = MsgPreVoteResp ∨ t = MsgReadIndex ∨
      t = MsgReadIndexResp := by
  have hp : md.prevote = true ∨ md.prevote = false := by cases md.prevote <;> simp
  have hr : md.reads = true ∨ md.reads = false := by cases md.reads <;> simp
  rcases hp with hp | hp <;> rcases hr with hr | hr <;>
    simp only [netTypes, antStepTypes, hp, hr, hs, hf, Bool.false_eq_true, ↓reduceIte, List.append_nil,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at h <;>
    rcases h with h | h | h | h | h | h | h | h | h | h <;> simp_all

/-- The network's types are `RawNode.Step`'s at the mode. -/
theorem netTypes_sub_stepTypes {md : RnMode} {t : w32} (h : t ∈ netTypes md) : t ∈ stepTypes md := by
  unfold netTypes at h
  unfold stepTypes
  simp only [List.mem_append] at h ⊢
  rcases h with (((h | h) | h) | h) | h
  · exact .inl (.inl (.inl (.inl (.inl (.inl h)))))
  · exact .inl (.inl (.inl (.inl (.inl (.inr h)))))
  · exact .inl (.inl (.inl (.inl (.inr h))))
  · exact .inl (.inr h)
  · exact .inl (.inl (.inr h))

/-- **An in-flight protocol message read at its type** (`absMsgOf`, no snapshot): `absMsg`. -/
theorem netFacts_absMsg {R : AntSim.RunCfg} {st : MsgSt} {m : Msg} (h : NetFacts R st m)
    (hs : R.md.snapshots = false) (hf : R.md.forwarding = false) :
    ∃ ty, mtypeOf st.msg.Type' = some ty ∧ ty ≠ .snap ∧ absMsg ty st.msg st.ents st.ctx = m ∧
      (∀ ty', mtypeOf st.msg.Type' = some ty' → ty' = ty) ∧
      AntSim.msgTypeStr ty = msgTypeStr st.msg.Type' := by
  have hab := h.2.2.2.2.1
  unfold absMsgOf at hab
  rcases netTypes_cases h.2.1 hs hf with ht | ht | ht | ht | ht | ht | ht | ht | ht | ht <;>
    rw [ht] at hab ⊢ <;>
    exact ⟨_, rfl, by decide, Option.some.inj hab, fun _ h => (Option.some.inj h).symm, by decide⟩

/-- A message's protocol reading is addressed to its `To`. -/
theorem absMsgOf_dst {st : MsgSt} {m : Msg} (H : absMsgOf st = some m) : m.dst = st.msg.To' := by
  unfold absMsgOf at H
  split at H
  · cases H
  · obtain ⟨sv, -, rfl⟩ := Option.map_eq_some_iff.1 H; rfl
  · cases H; rfl

/-- The network's types are not `MsgSnap` (no snapshots). -/
theorem netFacts_ne_snap {R : AntSim.RunCfg} {st : MsgSt} {m : Msg} (h : NetFacts R st m)
    (hs : R.md.snapshots = false) (hf : R.md.forwarding = false) : st.msg.Type' ≠ MsgSnap := by
  have key : ∀ t : w32, t ∈ netTypes R.md → t ≠ MsgSnap := fun t ht => by
    rcases netTypes_cases ht hs hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide
  exact key _ h.2.1

/-- **What `Reach.input` and `ViewNormal` need of a received protocol message**: a nonzero term but
for a (forwarded, unstamped) read request, its entries normal, its index and log term below `2 ^ 61`,
not a proposal (no forwarding). -/
theorem netFacts_recv {R : AntSim.RunCfg} {st : MsgSt} {m : Msg} (h : NetFacts R st m)
    (hs : R.md.snapshots = false) (hf : R.md.forwarding = false) :
    (m.ty ≠ .readIndex → m.term ≠ W64 0) ∧ AllNormal m.entries ∧ uint.Z m.index < 2 ^ 61 ∧
      uint.Z m.logterm < 2 ^ 61 ∧ m.ty ≠ .propose := by
  obtain ⟨ty, hty, -, hm, -, -⟩ := netFacts_absMsg h hs hf
  subst hm
  obtain ⟨hok, htys, -, hn, -, -, -, -, hI, hL, -, -⟩ := h
  refine ⟨fun hr => (hok.2.1 ?_).2.1, hn, hI, hL, ?_⟩
  · show ¬ UnstampedType st.msg.Type'
    rcases netTypes_cases htys hs hf with ht | ht | ht | ht | ht | ht | ht | ht | ht | ht <;>
      rw [ht] at hty ⊢ <;> first | (unfold UnstampedType; decide +revert) |
        (exact absurd (Option.some.inj hty).symm hr)
  · show ty ≠ .propose
    rcases netTypes_cases htys hs hf with ht | ht | ht | ht | ht | ht | ht | ht | ht | ht <;>
      rw [ht] at hty <;> cases hty <;> decide

/-- **An in-flight message's `msgOf` report is the protocol message's** (`NetFacts`' bounds make
the Go `int(x)` readings `uint.Z`). -/
theorem msgOfSt_netFacts {R : AntSim.RunCfg} {st : MsgSt} {m : Msg} (h : NetFacts R st m)
    (hs : R.md.snapshots = false) (hf : R.md.forwarding = false) (to : w64) :
    msgOfSt st to = AntSim.msgOf m to := by
  obtain ⟨ty, -, -, hm, -, hstr⟩ := netFacts_absMsg h hs hf
  have hns := netFacts_ne_snap h hs hf
  subst hm
  obtain ⟨-, -, -, -, -, -, -, hT, hI, hL, hC, hE⟩ := h
  unfold msgOfSt AntSim.msgOf
  simp only [hns, decide_false, Bool.false_eq_true, ↓reduceIte, absMsg, absMsgFrom, Msg.mkV,
    hstr, AntSim.logOf]
  have e1 : sint.Z st.msg.Term' = uint.Z st.msg.Term' := by word
  have e2 : sint.Z st.msg.Index' = uint.Z st.msg.Index' := by word
  have e3 : sint.Z st.msg.LogTerm' = uint.Z st.msg.LogTerm' := by word
  have e4 : sint.Z st.msg.Commit' = uint.Z st.msg.Commit' := by word
  have e5 : st.ents.map entOfE = st.ents.map AntSim.entOf := by
    apply List.map_congr_left
    intro e he
    have := hE e he
    have e6 : sint.Z e.Term' = uint.Z e.Term' := by word
    unfold entOfE AntSim.entOf
    rw [e6]
  rw [e1, e2, e3, e4, e5]

end pure

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]

/-- **After a drain, the cause cell reset** (`n.cause = nil`, `node.step`'s last line): node `j` is
between inputs again. -/
theorem nodeOwn_drained_reset (c : Loc) (γ : AntNames) (j : Fin γ.R.N) (n : Loc) (v : AntSim.NodeView) :
    nodeOwn (GF := GF) c γ j n v .drained ⊢
      ∃ cl : Loc, n.[H.node, go!"cause"] ↦ cl ∗
        (n.[H.node, go!"cause"] ↦ (null : Loc) -∗ nodeOwn c γ j n v .idle) := by
  unfold nodeOwn
  iintro ⟨%d, %rn, %ms, %hsl, %cl, %csl, %role, %applied, #Hd, Hmem, Hrn, Hms, Hrole, Hhs, Hcause,
    Happ, Hconf, Hv, Hl, %HN, Hdisk, %si, %rs, %qs, %ip, %r, Hstor, %Hsto, Hraw, Hnr, %Hrv, #Hhsro,
    #Hcs, %Hc0, %Hph, -⟩
  iexists cl
  iframe Hcause
  iintro Hcause
  iexists d, rn, ms, hsl, null, csl, role, applied
  iframe Hd Hmem Hrn Hms Hrole Hhs Hcause Happ Hconf Hv Hl
  isplitr
  · ipureintro; exact HN
  dsimp only
  iframe Hdisk
  iexists si, rs, qs, ip, r
  iframe Hstor Hraw Hnr Hhsro Hcs
  ipureintro
  exact ⟨Hsto, Hrv, Hc0, Hph.1, Hph.2.1, Hph.2.2.1, Hph.2.2.2.1, Hph.2.2.2.2, rfl⟩

end laws

end AntHarness
end EtcdGrove
end Perennial
