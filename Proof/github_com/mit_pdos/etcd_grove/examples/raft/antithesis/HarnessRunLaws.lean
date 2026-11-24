/-
Lean-first (no Rocq counterpart). #33 S4: the laws `Cluster.run`'s proof
(`Cluster__run.lean`) uses over `HarnessInv.lean`'s vocabulary:

- an in-flight message's readings (`NetFacts`): its `msgOf` report is the protocol message's
  (`msgOfSt_netFacts`), the report's numbers within the checker's bound (`evRecv_numsOk`), its
  weight its entries plus two (`evRecv_weight`), its term nonzero, its protocol reading `absMsg`
  at its type;
- a proposal's message is `AntSim.propMsg` (`absMsg_propose`);
- the node's state between inputs opened (`nodeOwn_idle_open`, with what rebuilds a drain's loop
  head after an input), after a drain closed back to between inputs (`nodeOwn_drained_reset`,
  `nodeOwn_drained_idle`), its raft ghost state opened (`nodeRaft_open`);
- **the input noted in the view** (`view_input`): the run's invariant opened in an update (no
  step), the view's halves moved to `noteInput` (`antSim_quiet`'s `Quiet.input`), a lower bound of
  the sent list taken.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessInv
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Quiet

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-! ## Pure laws -/

section pure
variable [GooseExts]

theorem lcpLen_le_left : ∀ (l l' : List EntryM), lcpLen l l' ≤ l.length
  | [], _ => by simp [lcpLen]
  | _ :: _, [] => by simp [lcpLen]
  | a :: xs, b :: ys => by
    simp only [lcpLen, List.length_cons]
    split
    · have := lcpLen_le_left xs ys; omega
    · omega

/-- The harness's network types are all stamped. -/
theorem antStepTypes_stamped {t : w32} (h : t ∈ antStepTypes) : ¬ UnstampedType t := by
  simp only [antStepTypes, List.mem_cons, List.not_mem_nil, or_false] at h
  unfold UnstampedType
  rcases h with h | h | h | h | h | h <;> subst h <;> decide

/-- The harness's network types are not `MsgSnap`. -/
theorem antStepTypes_ne_snap {t : w32} (h : t ∈ antStepTypes) : t ≠ MsgSnap := by
  simp only [antStepTypes, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h <;> subst h <;> decide

/-- The harness's network types are not `MsgTimeoutNow`. -/
theorem antStepTypes_ne_timeoutNow {t : w32} (h : t ∈ antStepTypes) : t ≠ MsgTimeoutNow := by
  simp only [antStepTypes, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h <;> subst h <;> decide

/-- The harness's network types are not `MsgTransferLeader`. -/
theorem antStepTypes_ne_transfer {t : w32} (h : t ∈ antStepTypes) : t ≠ MsgTransferLeader := by
  simp only [antStepTypes, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h <;> subst h <;> decide

/-- The harness's network types are not `MsgReadIndex`. -/
theorem antStepTypes_ne_readIndex {t : w32} (h : t ∈ antStepTypes) : t ≠ MsgReadIndex := by
  simp only [antStepTypes, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h <;> subst h <;> decide

/-- A message of the network's types read at its type: `absMsg`, which is its reading. -/
theorem netFacts_absMsg {st : MsgSt} {m : Msg} (h : NetFacts st m) :
    ∃ ty, mtypeOf st.msg.Type' = some ty ∧ ty ≠ .snap ∧ absMsg ty st.msg st.ents st.ctx = m ∧
      (∀ ty', mtypeOf st.msg.Type' = some ty' → ty' = ty) := by
  have hab := h.2.2.2.2.1
  have hty := h.2.1
  simp only [antStepTypes, List.mem_cons, List.not_mem_nil, or_false] at hty
  unfold absMsgOf at hab
  rcases hty with ht | ht | ht | ht | ht | ht <;> rw [ht] at hab ⊢ <;>
    simp only [mtypeOf_MsgApp, mtypeOf_MsgAppResp, mtypeOf_MsgVote, mtypeOf_MsgVoteResp,
      mtypeOf_MsgHeartbeat, mtypeOf_MsgHeartbeatResp, Option.some.injEq] at hab ⊢ <;>
    exact ⟨_, rfl, by decide, hab, fun _ h => h.symm⟩

/-- A message's protocol reading is addressed to its `To`. -/
theorem absMsgOf_dst {st : MsgSt} {m : Msg} (H : absMsgOf st = some m) :
    m.dst = st.msg.To' := by
  unfold absMsgOf at H
  split at H
  · cases H
  · obtain ⟨sv, -, rfl⟩ := Option.map_eq_some_iff.1 H; rfl
  · cases H; rfl

/-- An in-flight message's entries are normal. -/
theorem netFacts_normal {st : MsgSt} {m : Msg} (h : NetFacts st m) : AllNormal m.entries := by
  obtain ⟨ty, -, -, hm, -⟩ := netFacts_absMsg h
  subst hm
  exact h.2.2.2.1

theorem mtypeOf_eq_hb {t : w32} (H : mtypeOf t = some .heartbeat) : t = MsgHeartbeat := by
  unfold mtypeOf at H; split at H <;> simp_all; rename_i h; exact uint_Z_inj.1 (by rw [h]; rfl)

/-- An in-flight heartbeat carries no context. -/
theorem netFacts_hbCtx {st : MsgSt} {m : Msg} (h : NetFacts st m) : m.ty = .heartbeat → m.ctx = [] := by
  obtain ⟨ty, hty, -, hm, -⟩ := netFacts_absMsg h
  subst hm
  intro hhb
  exact h.2.2.1 (.inl (mtypeOf_eq_hb (by rw [hty]; exact congrArg some hhb)))

/-- The view after an input keeps its entries normal (the handled message's, for `recv`). -/
theorem viewNormal_noteInput {v : AntSim.NodeView} {inp : AntSim.Input} (hN : ViewNormal v)
    (h : ∀ m, inp.cause = some m → AllNormal m.entries ∧ (m.ty = .heartbeat → m.ctx = []) ∧
      AntSim.InNums (2 ^ 61) m ∧ m.ty ≠ .propose) :
    ViewNormal (v.noteInput inp) :=
  ⟨hN.1, h⟩

/-- An in-flight message is not a proposal (the network's types). -/
theorem netFacts_notProp {st : MsgSt} {m : Msg} (h : NetFacts st m) : m.ty ≠ .propose := by
  obtain ⟨ty, hty, -, hm, -⟩ := netFacts_absMsg h
  subst hm
  show ty ≠ .propose
  have ht := h.2.1
  simp only [antStepTypes, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with ht | ht | ht | ht | ht | ht <;> rw [ht] at hty <;>
    simp only [mtypeOf_MsgApp, mtypeOf_MsgAppResp, mtypeOf_MsgVote, mtypeOf_MsgVoteResp,
      mtypeOf_MsgHeartbeat, mtypeOf_MsgHeartbeatResp, Option.some.injEq] at hty <;>
    subst hty <;> decide

/-- A handled message's index and log term below `2 ^ 61` (`NetFacts`). -/
theorem netFacts_inNums {st : MsgSt} {m : Msg} (h : NetFacts st m) : AntSim.InNums (2 ^ 61) m := by
  obtain ⟨ty, -, -, hm, -⟩ := netFacts_absMsg h
  subst hm
  exact ⟨h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1⟩

/-- An in-flight message's term is nonzero (stamped). -/
theorem netFacts_term {st : MsgSt} {m : Msg} (h : NetFacts st m) : m.term ≠ W64 0 := by
  obtain ⟨ty, -, -, hm, -⟩ := netFacts_absMsg h
  subst hm
  exact (h.1.2.1 (antStepTypes_stamped h.2.1)).2.1

/-- An in-flight message's sender is a voter of the harness's cluster. -/
theorem netFacts_from {st : MsgSt} {m : Msg} (h : NetFacts st m) :
    st.msg.From' ∈ AntSim.voters3 := by
  obtain ⟨ty, -, -, hm, -⟩ := netFacts_absMsg h
  obtain ⟨i, hi⟩ := h.2.2.2.2.2.2.1
  have hs : m.src = st.msg.From' := by subst hm; rfl
  rw [← hs, hi]
  unfold AntSim.voters3
  rw [GMap.elem_of_list_to_set]
  rcases i with ⟨_ | _ | _ | k, hk⟩
  · simp [AntSim.nodeId]
  · simp [AntSim.nodeId]
  · simp [AntSim.nodeId]
  · omega

theorem msgTypeStr_of {t : w32} {ty : MsgType} (h : t ∈ antStepTypes) (hty : mtypeOf t = some ty) :
    msgTypeStr t = AntSim.msgTypeStr ty := by
  simp only [antStepTypes, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h <;> subst h <;>
    simp only [mtypeOf_MsgApp, mtypeOf_MsgAppResp, mtypeOf_MsgVote, mtypeOf_MsgVoteResp,
      mtypeOf_MsgHeartbeat, mtypeOf_MsgHeartbeatResp, Option.some.injEq] at hty <;> subst hty <;>
    decide

/-- **An in-flight message's `msgOf` report is the protocol message's** (`NetFacts`' bounds make
the Go `int(x)` readings `uint.Z`). -/
theorem msgOfSt_netFacts {st : MsgSt} {m : Msg} (h : NetFacts st m) (to : w64) :
    msgOfSt st to = AntSim.msgOf m to := by
  obtain ⟨ty, hty, -, hm, -⟩ := netFacts_absMsg h
  subst hm
  obtain ⟨-, htys, -, -, -, -, -, hT, hI, hL, hC, hE⟩ := h
  have hns : st.msg.Type' ≠ MsgSnap := antStepTypes_ne_snap htys
  unfold msgOfSt AntSim.msgOf
  simp only [hns, decide_false, Bool.false_eq_true, ↓reduceIte, absMsg, absMsgFrom, Msg.mkV,
    msgTypeStr_of htys hty, AntSim.logOf]
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

/-- The `recv` report of an in-flight message has its numbers within the checker's bound. -/
theorem evRecv_numsOk {st : MsgSt} {m : Msg} (h : NetFacts st m) (id : w64) :
    (AntSim.evRecv id m).NumsOk := by
  obtain ⟨ty, -, -, hm, -⟩ := netFacts_absMsg h
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
  unfold AntSim.entOf
  split <;> exact ⟨by word, by word⟩

/-- The `recv` report's weight: the message's entries and two. -/
theorem evRecv_weight {st : MsgSt} {m : Msg} (h : NetFacts st m) (id : w64) :
    (AntSim.evRecv id m).weight = st.ents.length + 2 := by
  obtain ⟨ty, -, -, hm, -⟩ := netFacts_absMsg h
  subst hm
  simp [AntSim.evRecv, AntCheck.Event.weight, AntCheck.Event.size, AntCheck.Msg.size, AntSim.msgOf,
    AntSim.logOf, absMsg, absMsgFrom, Msg.mkV]

/-- `RawNode.Propose`'s message is `AntSim.propMsg`. -/
theorem absMsg_propose (id : w64) (data : List w8) :
    absMsg .propose { propMsgM with From' := id } [propEntryM data] = AntSim.propMsg id data := by
  rfl

theorem byE_tick_ne : AntSim.Input.byE .tick ≠ go!"recv" := by
  simp only [AntSim.Input.byE]; decide

theorem byE_propose_ne (d : List w8) : AntSim.Input.byE (.propose d) ≠ go!"recv" := by
  simp only [AntSim.Input.byE]; decide

/-- The configuration the harness's cluster has. -/
theorem rnCfg_cfgM3 {γ : RaftNames} (h : γ.reCfg = AntSim.voters3) : rnCfg γ = AntSim.cfgM3 := by
  unfold rnCfg AntSim.cfgM3; rw [h]

/-- `RsView` reads none of the term, the ceiling, `psnap`; nor the view's input fields. -/
theorem rsView_input {rs rs' : RNState} {v v' : AntSim.NodeView} (h : RsView rs v)
    (hphs : rs'.phs = rs.phs) (hrole : rs'.role = rs.role) (hdur : rs'.dur = rs.dur)
    (hdel : rs'.delivered = rs.delivered) (hsteps : rs'.steps = rs.steps)
    (hun : rs'.unpersisted = rs.unpersisted) (hflw : rs'.flw = rs.flw)
    (hps : v'.ps = v.ps) (hd : v'.delivered = v.delivered) (hce : v'.ce = v.ce) : RsView rs' v' := by
  unfold RsView at h ⊢
  rw [hphs, hrole, hdur, hdel, hsteps, hun, hflw, hps, hd, hce]
  exact h

end pure

/-! ## The node's state -/

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]

/-- **Node `j`'s raft ghost state, opened**: the ceiling's bound, the budget (persistent, by its
law), the cluster's static facts, and what closes it at a state of the same durable state and a
ceiling bounded. -/
theorem nodeRaft_open (hbp : rnBudget_persistent.law (GF := GF)) (γ : AntNames) (j : Fin 3)
    (rs : RNState) :
    nodeRaft (GF := GF) γ j rs ⊢
      rnTermLB γ.raft rs.tc ∗ □ rnBudget γ.raft ∗
      ⌜γ.raft.raftNames.reTrace = none ∧ γ.raft.raftNames.reCfg = AntSim.voters3 ∧
        γ.raft.raftNames.maxData = none⌝ ∗
      (∀ rs' : RNState, ⌜rs'.dur = rs.dur⌝ -∗ rnTermLB γ.raft rs'.tc -∗ nodeRaft γ j rs') := by
  haveI := hbp γ.raft
  unfold nodeRaft
  iintro ⟨%x, %g, Hgv, Hsf, Hdg, Htc, #Hb, %Hst⟩
  iframe Htc
  isplitr
  · iexact Hb
  isplitr
  · ipureintro; exact ⟨Hst.1, Hst.2.1, Hst.2.2.1⟩
  iintro %rs' %hd Htc'
  iexists x, g
  rw [hd]
  iframe Hgv Hsf Hdg Htc' Hb
  ipureintro; exact Hst

/-- **Node `j` between inputs, opened** (`Cluster.run` taking an input): its `RawNode` at the
view's state, its raft ghost state opened (`nodeRaft_open`), the cause cell `nil`, the view fragment
and the right to report, and what makes a drain's loop head of it after an input (the `RawNode` at
the input's end, first, so that it names the client's record; reached from the noted view). -/
theorem nodeOwn_idle_open (hbp : rnBudget_persistent.law (GF := GF)) (c : Loc) (γ : AntNames)
    (j : Fin 3) (n : Loc) (v : AntSim.NodeView) :
    nodeOwn (GF := GF) c γ j n v .idle ⊢
      ∃ (rn : Loc) (rs : RNState),
        n.[H.node, go!"rn"] ↦□ rn ∗
        rawNode γ.raft.raftNames rn (AntSim.nodeId j) rs v.ps [] v.ps.log.length ∗
        rnTermLB γ.raft rs.tc ∗ □ rnBudget γ.raft ∗
        ⌜γ.raft.raftNames.reTrace = none ∧ γ.raft.raftNames.reCfg = AntSim.voters3 ∧
          γ.raft.raftNames.maxData = none⌝ ∗
        n.[H.node, go!"cause"] ↦ (null : Loc) ∗ viewFrag γ j v ∗ nodeLive γ j ∗
        ⌜RsView rs v ∧ v.Idle ∧ PIdle rs v.ps ∧ ViewNormal v⌝ ∗
        (∀ (rs' : RNState) (ps₁ : PState) (ip' : Nat) (v' : AntSim.NodeView) (net₀ : List Msg)
            (cl : Loc),
          rawNode γ.raft.raftNames rn (AntSim.nodeId j) rs' ps₁ [] ip' -∗
          ⌜rs'.storage = rs.storage ∧ rs'.dur = rs.dur ∧ RsView rs' v' ∧ v'.ps = v.ps ∧
            AntSim.Reach (AntSim.nodeId j) net₀ v' ps₁ ∧ ip' = lcpLen v.ps.log ps₁.log ∧
            ByOk v'.byE ∧ ViewNormal v'⌝ -∗
          rnTermLB γ.raft rs'.tc -∗
          n.[H.node, go!"cause"] ↦ cl -∗ viewFrag γ j v' -∗ nodeLive γ j -∗ sentLb γ net₀ -∗
          causeOwn γ j v' cl -∗ nodeOwn c γ j n v' (.loop net₀ ps₁)) := by
  unfold nodeOwn
  iintro ⟨%rn, %ms, %si, %rs, %ps, %qs, %ip, %cl, %applied, #Hrn, #Hms, Hbs, %Hsto, Hraw, Hnr,
    %Hrv, Hrole, Hterm, Hvote, Hcommit, Happ, Hcause, Hv, Hl, %HN, %Hph⟩
  obtain ⟨hI, rfl, rfl, rfl, hP, rfl⟩ := Hph
  icases nodeRaft_open hbp γ j rs $$ Hnr with ⟨Htc, #Hb, %Hst, Hnrc⟩
  iexists rn, rs
  iframe Hrn Hraw Htc Hcause Hv Hl
  isplitr
  · iexact Hb
  isplitr
  · ipureintro; exact Hst
  isplitr
  · ipureintro; exact ⟨Hrv, hI, hP, HN⟩
  iintro %rs' %ps₁ %ip' %v' %net₀ %cl' Hraw %Hf Htc Hcause Hv Hl Hlb Hco
  obtain ⟨hsto, hdur, hrv, hps, hR, hip, hby, hN'⟩ := Hf
  ihave Hnr := Hnrc $$ %rs' %hdur Htc
  iexists rn, ms, si, rs', ps₁, [], ip', cl', applied
  rw [hps]
  dsimp only
  iframe Hrn Hms Hbs Hraw Hnr Hrole Hterm Hvote Hcommit Happ Hcause Hv Hl Hlb Hco
  ipureintro
  exact ⟨by rw [hsto]; exact Hsto, hrv, hN', rfl, hR, rfl, hip, hby⟩

/-- **After a drain, the cause cell reset** (`n.cause = nil` in `run`'s `recv` arm): node `j` is
between inputs again. -/
theorem nodeOwn_drained_reset (c : Loc) (γ : AntNames) (j : Fin 3) (n : Loc) (v : AntSim.NodeView) :
    nodeOwn (GF := GF) c γ j n v .drained ⊢
      ∃ cl : Loc, n.[H.node, go!"cause"] ↦ cl ∗
        (n.[H.node, go!"cause"] ↦ (null : Loc) -∗ nodeOwn c γ j n v .idle) := by
  unfold nodeOwn
  iintro ⟨%rn, %ms, %si, %rs, %ps, %qs, %ip, %cl, %applied, #Hrn, #Hms, Hbs, %Hsto, Hraw, Hnr,
    %Hrv, Hrole, Hterm, Hvote, Hcommit, Happ, Hcause, Hv, Hl, %HN, %Hph, -⟩
  iexists cl
  iframe Hcause
  iintro Hcause
  iexists rn, ms, si, rs, ps, qs, ip, null, applied
  iframe Hrn Hms Hbs Hraw Hnr Hrole Hterm Hvote Hcommit Happ Hcause Hv Hl
  ipureintro
  exact ⟨Hsto, Hrv, HN, Hph.1, Hph.2.1, Hph.2.2.1, Hph.2.2.2.1, Hph.2.2.2.2, rfl⟩

/-- **After a drain not caused by a message**, the cause cell is `nil` (`causeOwn`): node `j` is
between inputs again. -/
theorem nodeOwn_drained_idle (c : Loc) (γ : AntNames) (j : Fin 3) (n : Loc) (v : AntSim.NodeView)
    (h : v.byE ≠ go!"recv") :
    nodeOwn (GF := GF) c γ j n v .drained ⊢ nodeOwn c γ j n v .idle := by
  have hco : ∀ cl, causeOwn (GF := GF) γ j v cl = iprop(⌜cl = null⌝) := by
    intro cl; unfold causeOwn; simp only [h, false_and, ↓reduceIte]
  unfold nodeOwn
  iintro ⟨%rn, %ms, %si, %rs, %ps, %qs, %ip, %cl, %applied, #Hrn, #Hms, Hbs, %Hsto, Hraw, Hnr,
    %Hrv, Hrole, Hterm, Hvote, Hcommit, Happ, Hcause, Hv, Hl, %HN, %Hph, Hco⟩
  rw [hco]
  icases Hco with %Hnil
  iexists rn, ms, si, rs, ps, qs, ip, cl, applied
  iframe Hrn Hms Hbs Hraw Hnr Hrole Hterm Hvote Hcommit Happ Hcause Hv Hl
  ipureintro
  exact ⟨Hsto, Hrv, HN, Hph.1, Hph.2.1, Hph.2.2.1, Hph.2.2.2.1, Hph.2.2.2.2, Hnil⟩

/-- **The cause cell after a message's input** (`n.cause = &cause`, `cause := msgOf(inp.msg, n.id)`):
the report of the message, sent, with its receipts (`msgOf`'s, one per entry, and two more). -/
theorem causeOwn_recv (γ : AntNames) (j : Fin 3) (v : AntSim.NodeView) (cl : Loc) (g : AntCheck.G.Msg)
    {st : MsgSt} {m : Msg} (hf : NetFacts st m) (hd : m.dst = AntSim.nodeId j) :
    cl ↦ g ∗ AntCheck.msgRO (GF := GF) g (msgOfSt st (AntSim.nodeId j)) ∗ sentW γ m ∗
        ⧗ st.ents.length ∗ ⧗ 1 ∗ ⧗ 1 ⊢
      causeOwn γ j (v.noteInput (.recv m)) cl := by
  have hco : causeOwn (GF := GF) γ j (v.noteInput (.recv m)) cl =
      iprop(∃ (m' : Msg) (g' : AntCheck.G.Msg), ⌜some m = some m' ∧ m'.dst = AntSim.nodeId j ∧
          (AntSim.evRecv (AntSim.nodeId j) m').NumsOk⌝ ∗
        cl ↦ g' ∗ AntCheck.msgRO g' (AntSim.msgOf m' (AntSim.nodeId j)) ∗ sentW γ m' ∗
        ⧗ (AntSim.evRecv (AntSim.nodeId j) m').weight) := by
    unfold causeOwn
    simp only [AntSim.NodeView.noteInput, AntSim.Input.byE, AntSim.Input.cause, and_self,
      ↓reduceIte]
  rw [hco, msgOfSt_netFacts hf]
  iintro ⟨Hc, Hg, Hs, Hr, Hr1, Hr2⟩
  iexists m, g
  rw [evRecv_weight hf]
  iframe Hc Hg Hs
  isplitr
  · ipureintro; exact ⟨rfl, hd, evRecv_numsOk hf _⟩
  iapply (receipt_add (GF := GF) (st.ents.length + 1) 1).2
  iframe Hr2
  iapply (receipt_add (GF := GF) st.ents.length 1).2
  iframe Hr Hr1

/-- **The cause cell after a tick or a proposal**: `nil`. -/
theorem causeOwn_noRecv (γ : AntNames) (j : Fin 3) (v : AntSim.NodeView) (inp : AntSim.Input)
    (h : inp.byE ≠ go!"recv") :
    ⊢ causeOwn (GF := GF) γ j (v.noteInput inp) null := by
  unfold causeOwn
  simp only [AntSim.NodeView.noteInput, h, false_and, ↓reduceIte]
  iintro; ipureintro; trivial

/-! ## The input noted in the view -/

/-- **The view notes an input** (`Quiet.input`, `antSim_quiet`): node `j`'s view between inputs,
the input's message (if any) sent to it; the run's invariant is opened in an update (no step: it
is timeless), its view halves moved to `v.noteInput inp`, the relation re-proved, and a lower bound
of the sent list taken, which has the message. -/
theorem view_input (γ : AntNames) (j : Fin 3) (v : AntSim.NodeView) (inp : AntSim.Input)
    (hI : v.Idle) (hd : ∀ m, inp = .recv m → m.dst = AntSim.nodeId j) :
    inv antN (antInv (GF := GF) γ) ∗ □ (∀ m, ⌜inp = .recv m⌝ -∗ sentW γ m) ∗ viewFrag γ j v ∗
        nodeLive γ j ⊢
      |={⊤}=> ∃ net₀ : List Msg, viewFrag γ j (v.noteInput inp) ∗ nodeLive γ j ∗ sentLb γ net₀ ∗
        ⌜∀ m, inp = .recv m → m ∈ net₀⌝ := by
  iintro ⟨#Hinv, #Hs, Hv, Hl⟩
  iinv Hinv with >Hi Hclose
  iunfold antInv at Hi
  icases Hi with (Hi | Hover)
  · iunfold antOpen at Hi
    icases Hi with ⟨%evs, %S, %V, %net, %G, Hstr, H0, H1, H2, Hnet, %Hpure, #HF⟩
    ihave %Hmem : ⌜∀ m, inp = .recv m → m ∈ net⌝ $$ [Hnet]
    · cases inp with
      | recv m =>
        ihave #Hsm := Hs $$ %m %rfl
        iunfold sentW at Hsm
        icases Hsm with ⟨%i, #Hidx⟩
        ihave %Hlk := mono_list_auth_idx_lookup (GF := GF) γ.sent 1 net i m $$ Hnet Hidx
        ipureintro
        intro m' hm'
        cases hm'
        exact List.mem_of_getElem? Hlk
      | tick => ipureintro; intro m' hm'; cases hm'
      | propose d => ipureintro; intro m' hm'; cases hm'
    ihave #Hlb := monoListLbOwn_get (GF := GF) γ.sent 1 net $$ Hnet
    imod view_update _ γ j V v (v.noteInput inp) $$ [Hv H0 H1 H2] with ⟨%HVj, Hv, H0, H1, H2⟩
    · iframe Hv H0 H1 H2
    obtain ⟨hR, hL, hG, hlogs⟩ := Hpure
    obtain ⟨hP, hA, hB, hCB, hC⟩ := hR
    have hq : AntSim.Quiet (AntSim.nodeId j) net (V j) (v.noteInput inp) := by
      rw [HVj]
      exact AntSim.Quiet.input v inp hI (fun m hm => ⟨Hmem m hm, hd m hm⟩)
    have hA' := AntSim.antSim_quiet S V net G j (v.noteInput inp) hA hL hG hq
    imod Hclose $$ [Hstr H0 H1 H2 Hnet] with -
    · inext
      iunfold antInv
      ileft
      iunfold antOpen
      iexists evs, S, AntSim.setV V j (v.noteInput inp), net, G
      iframe Hstr H0 H1 H2 Hnet HF
      ipureintro
      refine ⟨⟨hP, hA', hB, hCB, hC⟩, hL, hG, ?_⟩
      intro i
      unfold AntSim.setV
      split
      · subst_vars; exact hlogs _
      · exact hlogs i
    imodintro
    iexists net
    iunfold sentLb
    iframe Hv Hl Hlb
    ipureintro; exact Hmem
  · iexfalso
    iapply nodeLive_over γ j
    iframe Hl Hover

end laws

end AntHarness
end EtcdGrove
end Perennial
