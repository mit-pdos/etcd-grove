/-
Lean-first (no Rocq counterpart). #33 parity B1: the steps the proofs of `node.step` and the other
inputs share beyond `HarnessInput.lean`'s:
- `lcpLen_self`: an input that keeps the log keeps the in-progress boundary at the log's end;
- `nodeOwn_drained_reset`: after a drain, the cause cell reset (`n.cause = nil`), node `j` between
  inputs again (S4's, over `Fin R.N`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessInput
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Init
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.AckedTerm

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

/-- The network's types in a run without forwarding are not `MsgProp`. -/
theorem netFacts_ne_prop {R : AntSim.RunCfg} {st : MsgSt} {m : Msg} (h : NetFacts R st m)
    (hs : R.md.snapshots = false) (hf : R.md.forwarding = false) : st.msg.Type' ≠ MsgProp := by
  have key : ∀ t : w32, t ∈ netTypes R.md → t ≠ MsgProp := fun t ht => by
    rcases netTypes_cases ht hs hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide
  exact key _ h.2.1

/-- The network's types in B1 are not a transfer request. -/
theorem netFacts_ne_transfer {R : AntSim.RunCfg} {st : MsgSt} {m : Msg} (h : NetFacts R st m)
    (hs : R.md.snapshots = false) (hf : R.md.forwarding = false) :
    st.msg.Type' ≠ MsgTransferLeader := by
  have key : ∀ t : w32, t ∈ netTypes R.md → t ≠ MsgTransferLeader := fun t ht => by
    rcases netTypes_cases ht hs hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide
  exact key _ h.2.1

/-- The network's types in B1 are not `MsgTimeoutNow`. -/
theorem netFacts_ne_timeoutNow {R : AntSim.RunCfg} {st : MsgSt} {m : Msg} (h : NetFacts R st m)
    (hs : R.md.snapshots = false) (hf : R.md.forwarding = false) :
    st.msg.Type' ≠ MsgTimeoutNow := by
  have key : ∀ t : w32, t ∈ netTypes R.md → t ≠ MsgTimeoutNow := fun t ht => by
    rcases netTypes_cases ht hs hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide
  exact key _ h.2.1

/-- A transfer message's type: neither a snapshot nor a proposal nor a read request, and no
protocol reading. -/
theorem xnetFacts_types {R : AntSim.RunCfg} {st : MsgSt} {x : XMsg} (h : XNetFacts R st x) :
    st.msg.Type' ≠ MsgSnap ∧ st.msg.Type' ≠ MsgProp ∧ st.msg.Type' ≠ MsgReadIndex ∧
      mtypeOf st.msg.Type' = none := by
  rcases h.2.2.1 with ⟨ht, -⟩ | ⟨ht, -⟩ <;> rw [ht] <;>
    exact ⟨by simp [MsgTimeoutNow, MsgTransferLeader, MsgSnap],
      by simp [MsgTimeoutNow, MsgTransferLeader, MsgProp],
      by simp [MsgTimeoutNow, MsgTransferLeader, MsgReadIndex], rfl⟩

/-- A transfer message's type is `RawNode.Step`'s at the run's mode (transfers on), and not a
heartbeat response. -/
theorem xnetFacts_stepTypes {R : AntSim.RunCfg} {st : MsgSt} {x : XMsg} (h : XNetFacts R st x) :
    st.msg.Type' ∈ stepTypes R.md ∧ st.msg.Type' ≠ MsgHeartbeatResp := by
  have ht := h.1
  rcases h.2.2.1 with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] <;> unfold stepTypes <;>
    simp [ht, MsgTimeoutNow, MsgTransferLeader, MsgHeartbeatResp]

/-- A transfer message's transfer reading (`xmsgOf`) is its `XMsg`. -/
theorem xnetFacts_xmsgOf {R : AntSim.RunCfg} {st : MsgSt} {x : XMsg} (h : XNetFacts R st x) :
    xmsgOf st = some x := by
  obtain ⟨-, -, hty, hsrc, hdst, hterm, -⟩ := h
  obtain ⟨xty, xs, xd, xt⟩ := x
  simp only at hsrc hdst hterm
  subst hsrc hdst hterm
  unfold xmsgOf
  rcases hty with ⟨ht, hx⟩ | ⟨ht, hx⟩
  · simp only at hx; subst hx; rw [if_pos ht]
  · simp only at hx; subst hx
    rw [if_neg (by rw [ht]; simp [MsgTransferLeader, MsgTimeoutNow]), if_pos ht]

/-- **A transfer message's `msgOf` report at its destination is `xmsgOf`'s** (`XNetFacts`' zero
fields; the term below `2 ^ 61`). -/
theorem msgOfSt_xnetFacts {R : AntSim.RunCfg} {st : MsgSt} {x : XMsg} (h : XNetFacts R st x) :
    msgOfSt st x.dst = AntSim.xmsgOf x := by
  obtain ⟨-, -, hty, hsrc, -, hterm, -, -, hT, hI, hL, hC, hE, hR⟩ := h
  have e1 : sint.Z st.msg.Term' = uint.Z st.msg.Term' := by word
  unfold msgOfSt AntSim.xmsgOf
  rcases hty with ⟨ht, hx⟩ | ⟨ht, hx⟩ <;>
    simp only [ht, hx, hI, hL, hC, hE, hR, hsrc, hterm, e1, List.map_nil] <;> rfl

/-- The `recv` report of an in-flight message has its numbers within the checker's bound. -/
theorem evRecv_numsOk {R : AntSim.RunCfg} {st : MsgSt} {m : Msg} (h : NetFacts R st m)
    (hs : R.md.snapshots = false) (hf : R.md.forwarding = false) (id : w64) :
    (AntSim.evRecv id m).NumsOk := by
  obtain ⟨ty, -, -, hm, -, -⟩ := netFacts_absMsg h hs hf
  subst hm
  obtain ⟨-, -, -, -, -, -, -, hT, hI, hL, hC, hE⟩ := h
  simp only [AntSim.evRecv, AntCheck.Event.NumsOk, AntCheck.optNumOk, AntSim.msgOf,
    AntCheck.Msg.NumsOk, AntCheck.numOk, AntCheck.numBound, absMsg, absMsgFrom, Msg.mkV,
    AntCheck.entriesOk, AntSim.logOf]
  and_intros
  all_goals try exact True.intro
  all_goals try (intro _ h; cases h; done)
  intro mm hmm
  cases hmm
  refine ⟨⟨by word, by word⟩, ⟨by word, by word⟩, ⟨by word, by word⟩, ⟨by word, by word⟩, ?_⟩
  intro es hes
  cases hes
  intro e he
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he
  have := hE x hx
  have e : (AntSim.entOf x).term = uint.Z x.Term' := by
    unfold AntSim.entOf; split <;> (try split) <;> rfl
  rw [e]; exact ⟨by word, by word⟩

/-- The `recv` report's weight: the message's entries and two. -/
theorem evRecv_weight {R : AntSim.RunCfg} {st : MsgSt} {m : Msg} (h : NetFacts R st m)
    (hs : R.md.snapshots = false) (hf : R.md.forwarding = false) (id : w64) :
    (AntSim.evRecv id m).weight = st.ents.length + 2 := by
  obtain ⟨ty, -, -, hm, -, -⟩ := netFacts_absMsg h hs hf
  subst hm
  simp [AntSim.evRecv, AntCheck.Event.weight, AntCheck.Event.size, AntCheck.Msg.size, AntSim.msgOf,
    AntSim.logOf, absMsg, absMsgFrom, Msg.mkV]

/-- The `recv` report of a transfer message has its numbers within the checker's bound. -/
theorem evRecvX_numsOk {R : AntSim.RunCfg} {st : MsgSt} {x : XMsg} (h : XNetFacts R st x)
    (id : w64) : (AntSim.evRecvX id x).NumsOk := by
  obtain ⟨-, -, -, -, -, hterm, -, -, hT, -⟩ := h
  have hT' : uint.Z x.term < 2 ^ 61 := hterm ▸ hT
  simp only [AntSim.evRecvX, AntCheck.Event.NumsOk, AntCheck.optNumOk, AntSim.xmsgOf,
    AntCheck.Msg.NumsOk, AntCheck.numOk, AntCheck.numBound, AntCheck.entriesOk]
  and_intros
  all_goals try exact True.intro
  all_goals try (intro _ h; cases h; done)
  intro mm hmm
  cases hmm
  have h0 : (0 : Int) ≤ uint.Z x.term := by word
  refine ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
    ⟨by omega, by omega⟩, ?_⟩
  intro es hes
  cases hes
  intro e he
  cases he

/-- The `recv` report of a transfer message weighs two. -/
theorem evRecvX_weight (x : XMsg) (id : w64) : (AntSim.evRecvX id x).weight = 2 := by
  simp [AntSim.evRecvX, AntCheck.Event.weight, AntCheck.Event.size, AntCheck.Msg.size,
    AntSim.xmsgOf]

/-- **A run without non-voters has every node a voter** (`InScope`: `Voters = Nodes` unless the
scope has non-voters): node `i`'s id is an initial voter. -/
theorem nodeId_mem_voters0 {s : H.Scope} {m : H.Mode} {R : AntSim.RunCfg} (hin : InScope s m)
    (hmr : ModeRun s m R) (hnv : R.md.nonVoters = false) (i : Fin R.N) :
    AntSim.nodeId i ∈ R.voters0 := by
  have hK : R.K = R.N := by
    rw [hmr.1, hmr.2.1]
    rcases hin.2.1 with h | ⟨h, -, -⟩
    · rw [h]
    · rw [hmr.2.2.2.2.1] at hnv
      simp only [scopeMd] at hnv
      rw [hnv] at h; cases h
  exact (AntSim.mem_voters0 R i.isLt).mpr (by have := i.isLt; omega)


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

/-- **The cause cell after a protocol message's input** (`n.cause = &cause`, `cause := msgOf(m,
n.id)`): the report of the message, sent, with its receipts (`msgOf`'s, one per entry, and two more). -/
theorem causeOwn_recv (γ : AntNames) (j : Fin γ.R.N) (v : AntSim.NodeView) (cl : Loc)
    (g : AntCheck.G.Msg) {st : MsgSt} {m : Msg} (hf : NetFacts γ.R st m)
    (hs : γ.R.md.snapshots = false) (hfw : γ.R.md.forwarding = false)
    (hd : m.dst = AntSim.nodeId j) (hcl : cl ≠ null) :
    cl ↦ g ∗ AntCheck.msgRO (GF := GF) g (msgOfSt st (AntSim.nodeId j)) ∗ sentW γ m ∗
        ⧗ st.ents.length ∗ ⧗ 1 ∗ ⧗ 1 ⊢
      causeOwn γ j (v.noteInput (.recv m)) cl := by
  unfold causeOwn
  simp only [AntSim.NodeView.noteInput, AntSim.Input.byE, AntSim.Input.cause, AntSim.Input.xcause,
    and_self, ↓reduceIte]
  rw [msgOfSt_netFacts hf hs hfw]
  iintro ⟨Hc, #Hg, Hs, Hr, Hr1, Hr2⟩
  ileft
  iexists m
  rw [evRecv_weight hf hs hfw]
  iframe Hs
  isplitr
  · ipureintro; exact ⟨rfl, hd, evRecv_numsOk hf hs hfw _⟩
  isplitl [Hc]
  · iunfold pendingCause
    iright
    iexists g, AntSim.msgOf m (AntSim.nodeId j)
    iframe Hc Hg
    ipureintro; exact ⟨hcl, rfl⟩
  iapply (receipt_add (GF := GF) (st.ents.length + 1) 1).2
  iframe Hr2
  iapply (receipt_add (GF := GF) st.ents.length 1).2
  iframe Hr Hr1

/-- **The cause cell after a transfer message's input**: its report (`xmsgOf`), sent, with two
receipts. -/
theorem causeOwn_recvX (γ : AntNames) (j : Fin γ.R.N) (v : AntSim.NodeView) (cl : Loc)
    (g : AntCheck.G.Msg) {st : MsgSt} {x : XMsg} (hf : XNetFacts γ.R st x)
    (hd : x.dst = AntSim.nodeId j) (hcl : cl ≠ null) :
    cl ↦ g ∗ AntCheck.msgRO (GF := GF) g (msgOfSt st (AntSim.nodeId j)) ∗ xsentW γ x ∗
        ⧗ 1 ∗ ⧗ 1 ⊢
      causeOwn γ j (v.noteInput (.recvX x)) cl := by
  unfold causeOwn
  simp only [AntSim.NodeView.noteInput, AntSim.Input.byE, AntSim.Input.cause, AntSim.Input.xcause,
    and_self, ↓reduceIte]
  rw [← hd, msgOfSt_xnetFacts hf]
  iintro ⟨Hc, #Hg, Hs, Hr1, Hr2⟩
  iright
  iexists x
  rw [evRecvX_weight]
  iframe Hs
  isplitr
  · ipureintro; exact ⟨rfl, rfl, evRecvX_numsOk hf _⟩
  isplitl [Hc]
  · iunfold pendingCause
    iright
    iexists g, AntSim.xmsgOf x
    iframe Hc Hg
    ipureintro; exact ⟨hcl, rfl⟩
  iapply (receipt_add (GF := GF) 1 1).2
  iframe Hr1 Hr2

/-- **A `MsgTimeoutNow`'s acknowledgement against the receiver's disk** (what `node.step` uses for a
received `MsgTimeoutNow`): an acknowledgement past index `0` of node `j` is at a term at most its
disk's. `isAcked_term_le` on `nodeRaft`'s `ownDurGhost γ id rs.dur`, whose term is the disk's by
`RsView`'s last conjunct. -/
theorem nodeOwn_acked (c : Loc) (γ : AntNames) (j : Fin γ.R.N) (n : Loc) (v : AntSim.NodeView)
    (t i : w64) :
    nodeOwn (GF := GF) c γ j n v .idle ∗ isAcked γ.raft.raftNames (AntSim.nodeId j) t i ⊢
      ⌜uint.Z i ≠ 0 → uint.Z t ≤ uint.Z v.dur.term⌝ ∗ nodeOwn c γ j n v .idle := by
  unfold nodeOwn
  iintro ⟨⟨%d, %rn, %ms, %hsl, %cl, %csl, %role, %applied, #Hd, Hmem, Hrn, Hms, Hrole, Hhs, Hcause,
    Happ, Hconf, Hv, Hl, %HN, Hdisk, %si, %rs, %qs, %ip, %r, Hstor, %Hsto, Hraw, Hnr, %Hrv, #Hhsro,
    #Hcs, %Hc0, %Hph⟩, Ha⟩
  iunfold nodeRaft at Hnr
  icases Hnr with ⟨%x, %g, Hgv, Hsf, Hdg, Htc, Hb, %Hst⟩
  icases isAcked_term_le (GF := GF) γ.raft.raftNames (AntSim.nodeId j) t i rs.dur $$ Hdg Ha with
    ⟨%hle, Hdg⟩
  isplitr
  · ipureintro; intro hi; rw [← Hrv.1.2.2.2.2.2.2.2]; exact hle hi
  iexists d, rn, ms, hsl, cl, csl, role, applied
  iframe Hd Hmem Hrn Hms Hrole Hhs Hcause Happ Hconf Hv Hl
  isplitr
  · ipureintro; exact HN
  dsimp only
  iframe Hdisk
  iexists si, rs, qs, ip, r
  iframe Hstor Hraw Hhsro Hcs
  isplitr
  · ipureintro; exact Hsto
  isplitl [Hgv Hsf Hdg Htc Hb]
  · iunfold nodeRaft
    iexists x, g
    iframe Hgv Hsf Hdg Htc Hb
    ipureintro; exact Hst
  ipureintro; exact ⟨Hrv, Hc0, Hph⟩

/-- A receipt for a premise that may be off (`rnBudget_step`'s `⧗ (if P then 1 else 0)`). -/
theorem receipt_ite (P : Prop) [Decidable P] :
    (⧗ 1 : IProp GF) ⊢ ⧗ (if P then 1 else 0) := by
  by_cases hP : P
  · rw [if_pos hP]
  · rw [if_neg hP]
    iintro H
    icases receipt_zero_of (GF := GF) 1 $$ H with ⟨H0, -⟩
    iexact H0

end laws

end AntHarness
end EtcdGrove
end Perennial
