/-
Lean-first (no Rocq counterpart). #33 parity B1, driver group E: **the drain's `Ready` read at the
loop head** (node.drain's report `if`): `drain_peekRecsB1` (the run's invariant at the node's view:
its relation's facts at sent lists past the caller's lower bounds, the view's full log certified),
`readyOutP_b1` (raft's `Ready` post is the Sim's `ReadyOutP` there, `readyOutP_of` with the facts the
invariant gives).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB1Phases
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB1Ext
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.MsgShape
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

/-- **Raft's `Ready` at a loop head is the Sim's `ReadyOutP`** (`readyOutP_of`), with what the run's
relation gives at sent lists past the loop head's (`ReachIn`, `NodeOk`, `NetOk`): the view's disk its
protocol log (`SyncDisk`), no ghost prefix (`reach_fp`, `snap0`), the messages' destinations servers
(`dst_reach`), log matching from the two logs' records (`logMatch_of_recs`). The transfer messages'
`XPendOk` (`hx`) is the caller's (`xPendOk_of` over their certificates). Also: the node's full log is
its protocol log. -/
theorem readyOutP_b1 {R : AntSim.RunCfg} {dec : CCDec} {Adm : List EntryM → CCState → Prop}
    {S : AntCheck.State} {net : List Msg} {xnet : List XMsg} {j : Fin R.N} {v : AntSim.NodeView}
    {rs : RNState} {r : RState} {h : HardStateM} {es ce : List EntryM} {ms : List QMsg}
    {ss : Option (w64 × StateType)} {qs : List Msg} {sts : List ReadStateM} {ip : Nat}
    (hin : AntSim.InMask AntSim.mskB1 R net xnet) (hnet : AntSim.NetOk R S net)
    (hok : AntSim.NodeOk R dec S net j v) (hri : AntSim.ReachIn AntSim.mskB1 R dec Adm net xnet j v r)
    (hrv : RsView rs v) (hip : ip = lcpLen v.r.p.log r.p.log)
    (hout : ReadyOut (AntSim.nodeId j) rs r.p h es ce ms ss none)
    (hfirst : ∀ e0 ∈ es.head?, uint.nat e0.Index' = ip + 1)
    (hqs : qs.Perm (r.p.outbox.filter (fun m => decide (m.dst = AntSim.nodeId j))))
    (hpk : roleAfter rs.role ss = StatePreCandidate → (R.k j).prevote = true)
    (hx : ∀ x ∈ ms.filterMap (fun q => xmsgOf q.st), AntSim.XPendOk R.N (AntSim.nodeId j) r.p x)
    (hsts : sts = r.p.rd.states)
    (hns : r.p.base = base0 ∧ ∀ m ∈ r.p.outbox, m.ty ≠ .snap)
    (hwf : PlogWf base0 r.p.log) (hvidx : AntSim.LogIdx v.r.full)
    (hag : RecsAgree base0 v.r.full base0 r.p.log) :
    AntSim.ReadyOutP R j v r (readyDOf r (roleAfter rs.role ss) es ce ms qs sts) ∧
      r.full = r.p.log ∧ v.r.full = v.r.p.log ∧ v.dur.log = v.r.full := by
  obtain ⟨hmd, hbt, hpar, hspl, -, -⟩ := hin.b1 mskB1_le
  have hsn : R.md.snapshots = false := by rw [hmd]
  have hsd := (hok.sync (by rw [hmd]) hbt hspl hpar).2.1
  have hfp := AntSim.reach_fp mskB1_le hin hok hri
  have hfp0 := (hok.facts.snap0 hsn).2.1
  have hfull : r.full = r.p.log := by simp [RState.full, hfp, hfp0]
  have hvfull : v.r.full = v.r.p.log := by simp [RState.full, hfp0]
  have hdl : v.dur.log = v.r.full := by rw [hsd]; rfl
  have hidx := logIdx_of_wf hwf
  have hds := AntSim.dst_reach mskB1_le hin hnet hok hri
  refine ⟨readyOutP_of hrv (reach_ce hri.reach) (hfp.trans hfp0) (hdl.trans hvfull) hip hout hfirst hqs hpk
    (by rw [hmd]) hx hsts (fun _ => hns) (by rw [hfull]; exact hidx) ?_ ?_, hfull, hvfull, hdl⟩
  · intro k e f he hf ht
    rw [hdl] at he
    rw [hfull] at hf
    have htk := logMatch_of_recs hvidx hidx hag k e f he hf ht
    have h1 : (v.r.full.take (k + 1))[k]? = some e := by
      rw [List.getElem?_take]; simp [he]
    have h2 : (r.p.log.take (k + 1))[k]? = some f := by
      rw [List.getElem?_take]; simp [hf]
    rw [htk, h2] at h1
    exact (Option.some.inj h1).symm
  · intro q hq
    have hq' := (hout.2.2.2.2.1.mem_iff).mp hq
    rw [List.mem_filter] at hq'
    exact hds q hq'.1 (of_decide_eq_true hq'.2)

/-- The Sim's role string of a `Ready`'s view is Go's role string of the role after it. -/
theorem roleS_drainOf {v : AntSim.NodeView} {rs : RNState} {r : RState} {h : HardStateM}
    {es ce : List EntryM} {ms : List QMsg} {ss : Option (w64 × StateType)} {qs : List Msg}
    {sts : List ReadStateM} {id : w64} (hout : ReadyOut id rs r.p h es ce ms ss none) :
    AntSim.roleS (v.drainOf r (readyDOf r (roleAfter rs.role ss) es ce ms qs sts)) =
      roleStr (roleAfter rs.role ss) := by
  rw [← readyDOf_roleStr (es := es) (ce := ce) (ms := ms) (qs := qs) (sts := sts) hout.1.1]
  rfl

/-- **The view after a reported `Ready`** (`afterReady`) against the record after it and the
write's handshake (`rs₂`, its steps for `Advance`), its entries normal. -/
theorem drainView_rep {I : DrainIterB1} {id : w64} (b : Bool)
    (hrv : RsView I.rs I.v) (hce : I.v.ce = [])
    (hout : ReadyOut id I.rs I.r.p I.h I.es I.ce I.ms I.ss none) (hfull : I.r.full = I.r.p.log)
    (hN : ViewNormal I.v) (hnorm : AllNormal I.r.full) :
    RsView { I.rs₂ with steps := [] } ({ I.v with told := b }.afterReady I.r
        (readyDOf I.r (roleAfter I.rs.role I.ss) I.es I.ce I.ms I.qs I.sts)) ∧
      ViewNormal ({ I.v with told := b }.afterReady I.r
        (readyDOf I.r (roleAfter I.rs.role I.ss) I.es I.ce I.ms I.qs I.sts)) := by
  obtain ⟨-, -, hdel, -, -, hflw, -, -⟩ := hrv
  have hph := hout.2.1
  have hents := hout.2.2.1
  have hrole := roleS_drainOf (v := { I.v with told := b }) (qs := I.qs) (sts := I.sts) hout
  refine ⟨⟨?_, ?_, ?_, rfl, rfl, hflw, ?_, ?_⟩, ?_, hN.2⟩
  · simp only [DrainIterB1.rs₂, AntSim.NodeView.afterReady, AntSim.durOf, AntSim.accepted]; exact hph
  · show (readyDurable I.rs.dur (phsNext I.rs.phs I.h) none I.es).ents = (AntSim.accepted I.r).full
    rw [hents]; exact hfull.symm
  · simp only [DrainIterB1.rs₂, AntSim.NodeView.afterReady, AntSim.NodeView.drainOf, readyDOf]
    rw [hdel, hce]; simp
  · exact hrole.symm
  · simp only [DrainIterB1.rs₂, AntSim.NodeView.afterReady, AntSim.durOf, AntSim.accepted,
      readyDurable, RaftState.next]
    have := congrArg HardStateM.Term' hph
    simpa using this
  · simpa [AntSim.NodeView.afterReady, AntSim.NodeView.drainOf, AntSim.accepted, RState.full] using hnorm

/-- **The view after a silent `Ready`** (`drainOf`: no hard state, no entries) against the record
after it (`rs₂`, its steps for `Advance`), its entries normal. -/
theorem drainView_silent {I : DrainIterB1} {id : w64}
    (hrv : RsView I.rs I.v) (hce : I.v.ce = [])
    (hout : ReadyOut id I.rs I.r.p I.h I.es I.ce I.ms I.ss none) (hfv : I.r.full = I.v.r.full)
    (hN : ViewNormal I.v) (hn : ¬ HsNew I.h) (hes : I.es = []) :
    RsView { I.rs₂ with steps := [] } (I.v.drainOf I.r
        (readyDOf I.r (roleAfter I.rs.role I.ss) I.es I.ce I.ms I.qs I.sts)) ∧
      ViewNormal (I.v.drainOf I.r
        (readyDOf I.r (roleAfter I.rs.role I.ss) I.es I.ce I.ms I.qs I.sts)) := by
  obtain ⟨hphs, hdents, hdel, -, -, hflw, -, hdt⟩ := hrv
  have hpn : phsNext I.rs.phs I.h = I.rs.phs := phsNext_empty _ _ (Classical.not_not.mp hn)
  have hrole := roleS_drainOf (v := I.v) (qs := I.qs) (sts := I.sts) hout
  refine ⟨⟨?_, ?_, ?_, rfl, rfl, hflw, ?_, ?_⟩, ?_, hN.2⟩
  · simp only [DrainIterB1.rs₂, AntSim.NodeView.drainOf]; rw [hpn]; exact hphs
  · simp only [DrainIterB1.rs₂, AntSim.NodeView.drainOf]
    rw [hes, readyDurable_nil]; exact hdents
  · simp only [DrainIterB1.rs₂, AntSim.NodeView.drainOf, readyDOf]
    rw [hdel, hce]; simp
  · exact hrole.symm
  · simp only [DrainIterB1.rs₂, AntSim.NodeView.drainOf, readyDurable, RaftState.next, hpn]
    rw [hphs]
  · have : (AntSim.accepted I.r).full = I.v.r.full := by
      simpa [AntSim.accepted, RState.full] using hfv
    simp only [AntSim.NodeView.drainOf]; rw [this]; exact hN.1

/-- `Reach` does not read `told` (the drain's `reportCause` sets it). -/
theorem reach_told_b1 {R : AntSim.RunCfg} {dec : CCDec} {Adm : List EntryM → CCState → Prop}
    {net : List Msg} {xnet : List XMsg} {n : Fin R.N} {v : AntSim.NodeView} {r₁ : RState} (b : Bool)
    (h : AntSim.Reach R dec Adm net xnet n v r₁) :
    AntSim.Reach R dec Adm net xnet n { v with told := b } r₁ := by
  cases h with
  | stay hI hb => exact .stay { v with told := b } hI hb
  | input inp r₁ hI h1 h2 h3 h4 h5 h6 => exact .input _ inp _ hI h1 h2 h3 h4 h5 h6
  | advance r₁ h1 h2 h3 h4 h5 h6 h7 => exact .advance _ _ h1 h2 h3 h4 h5 h6 h7

/-- The `ready` report's numbers: the state's within `2 ^ 61`, the entries the log's. -/
theorem evReady_numsOk_b1 {id : w64} {b r : AntCheck.Str} {ps : PState} {vo : w64}
    {es : List EntryM} (hsn : AntSim.StateNums (2 ^ 61) ps) (ht : uint.Z ps.term < 2 ^ 61)
    (hes : ∀ e ∈ es, e ∈ ps.log) :
    (AntSim.evReady id b r ps.term vo ps.commit es).NumsOk := by
  have hE : ∀ e ∈ es, uint.Z e.Term' < 2 ^ 61 ∧ uint.Z e.Index' < 2 ^ 61 :=
    fun e he => hsn.2.2.2.2 e (hes e he)
  have hc := hsn.2.2.2.1
  have hf : 0 ≤ AntSim.firstOf es ∧ AntSim.firstOf es < 2 ^ 61 := by
    cases es with
    | nil => simp only [AntSim.firstOf]; omega
    | cons e _ =>
      have := (hE e List.mem_cons_self).2
      simp only [AntSim.firstOf]; constructor <;> word
  simp only [AntSim.evReady, AntCheck.Event.NumsOk, AntCheck.optNumOk, AntCheck.numOk,
    AntCheck.numBound, AntCheck.entriesOk, AntSim.logOf, Option.map_none]
  and_intros
  all_goals try exact True.intro
  all_goals try (intro _ h; cases h; done)
  all_goals first
    | (intro es' hes'
       simp only [Option.some.injEq] at hes'
       subst hes'
       intro x hx
       obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
       have h0 := (hE e he).1
       have h1 : (AntSim.entOf e).term = uint.Z e.Term' := by
         unfold AntSim.entOf; split <;> (try split) <;> rfl
       rw [h1]
       have h2 := uint_Z_nonneg e.Term'
       omega)
    | omega
    | (clear hf hE hes hsn; word)

theorem evReady_weight_b1 (id : w64) (b r : AntCheck.Str) (t vo c : w64) (es : List EntryM) :
    (AntSim.evReady id b r t vo c es).weight = es.length + 2 := by
  simp [AntSim.evReady, AntCheck.Event.weight, AntCheck.Event.size, AntSim.logOf]

theorem evReady_chgOk_b1 (id : w64) (b r : AntCheck.Str) (t vo c : w64) (es : List EntryM) :
    (AntSim.evReady id b r t vo c es).ChgOk 0 := by
  intro l hl e he
  simp only [AntCheck.Event.entryLists, AntSim.evReady, AntSim.logOf, Option.getD_some,
    Option.getD_none, Option.map_none, List.nil_append, List.cons_append, List.mem_cons,
    List.not_mem_nil, or_false, List.flatMap_nil, List.append_nil] at hl
  subst hl
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 he
  exact Nat.le_of_eq (entOf_chgSize x)

/-- **Go's `ready` report** (`withByRole(stateEv("ready", hs, ents), by, role)`, recorded at the
node) is the Sim's `evReady` (numbers within `2 ^ 61`). -/
theorem stateEv_ready (id : w64) (b r : AntCheck.Str) (hs : HardStateM) (es : List EntryM)
    (ht : uint.Z hs.Term' < 2 ^ 61) (hc : uint.Z hs.Commit' < 2 ^ 61)
    (hE : ∀ e ∈ es, uint.Z e.Term' < 2 ^ 61 ∧ uint.Z e.Index' < 2 ^ 61) :
    atNode (AntSim.nameOf id) (withByRoleM (stateEvM go!"ready" hs es) b r) =
      AntSim.evReady id b r hs.Term' hs.Vote' hs.Commit' es := by
  have e1 : sint.Z hs.Term' = uint.Z hs.Term' := by word
  have e2 : sint.Z hs.Commit' = uint.Z hs.Commit' := by word
  have e3 : sint.Z (firstIdx es) = AntSim.firstOf es := by
    cases es with
    | nil => simp [firstIdx, AntSim.firstOf]
    | cons e t =>
      have := (hE e List.mem_cons_self).2
      simp only [firstIdx, List.head?_cons, Option.map_some, Option.getD_some, AntSim.firstOf]
      word
  have e4 : es.map entOfE = AntSim.logOf es := by
    unfold AntSim.logOf
    apply List.map_congr_left
    intro e he
    have := (hE e he).1
    have e6 : sint.Z e.Term' = uint.Z e.Term' := by word
    unfold entOfE AntSim.entOf
    rw [e6]
  simp only [atNode, withByRoleM, stateEvM, AntSim.evReady, e1, e2, e3, e4, Option.map_none]

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [AntStor GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]

/-- **The run's invariant at node `j`'s view** (B1's `drain_peekRecs`): the relation's facts at the
invariant's sent lists, past the caller's lower bounds (in B1's mask, the network's and node `j`'s),
and the view's full log certified (`raftFactsOwn`'s `logs`). -/
theorem drain_peekRecsB1 (h_vu : view_update.law (GF := GF)) (h_lo : nodeLive_over.law (GF := GF))
    (h_mask : runInMask.law AntSim.mskB1) (γ : AntNames) (j : Fin γ.R.N) (v : AntSim.NodeView)
    (net₀ : List Msg) (xnet₀ : List XMsg)
    (hrun : InScope γ.scope γ.mode ∧ ModeRun γ.scope γ.mode γ.R) (hb1 : DrainB1 γ.scope γ.mode) :
    inv antN (antInv (GF := GF) γ) ∗ sentLb γ net₀ ∗ xsentLb γ xnet₀ ∗ viewFrag γ j v ∗
        nodeLive γ j ⊢
      |={⊤}=> ⌜∃ (S : AntCheck.State) (net : List Msg) (xnet : List XMsg), net₀ <+: net ∧
          xnet₀ <+: xnet ∧ AntSim.InMask AntSim.mskB1 γ.R net xnet ∧ AntSim.NetOk γ.R S net ∧
          AntSim.NodeOk γ.R γ.dec S net j v⌝ ∗
        logRecs γ.raft.raftNames base0 v.r.full ∗ ⌜AntSim.LogIdx v.r.full⌝ ∗
        viewFrag γ j v ∗ nodeLive γ j := by
  iintro ⟨#Hinv, #Hlb, #Hxlb, Hv, Hl⟩
  iunfold sentLb at Hlb
  iunfold xsentLb at Hxlb
  iinv Hinv with >Hi Hclose
  iunfold antInv at Hi
  icases Hi with (Hi | Hover)
  · iunfold antOpen at Hi
    icases Hi with ⟨%evs, %S, %V, %net, %xnet, %G, Hstr, Hviews, Hnet, Hxnet, %Hpure, #HF⟩
    ihave %Hpre := mono_list_auth_lb_valid (GF := GF) γ.sent 1 net net₀ $$ Hnet Hlb
    ihave %Hxpre := mono_list_auth_lb_valid (GF := GF) γ.xsent 1 xnet xnet₀ $$ Hxnet Hxlb
    imod h_vu (⊤ \ ↑antN) γ j V v v $$ [Hv Hviews] with ⟨%HVj, Hv, Hviews⟩
    · iframe Hv Hviews
    rw [setV_self_s HVj]
    ihave #HF' := HF
    iunfold raftFactsOwn at HF'
    icases HF' with ⟨-, -, #Hlogs, -, -, -⟩
    have hmem : v.r.full ∈ G.logs := by rw [← HVj]; exact Hpure.2.2.2 j
    ihave ⟨#Hrv, %Hli⟩ := BigSepL.bigSepL_mem
      (Φ := fun l => iprop(logRecs γ.raft.raftNames base0 l ∗ ⌜AntSim.LogIdx l⌝)) hmem $$ Hlogs
    have hin := h_mask γ evs S V net xnet hrun.1 hrun.2 hb1 Hpure.1
    imod Hclose $$ [Hstr Hviews Hnet Hxnet] with -
    · inext
      iunfold antInv
      ileft
      iunfold antOpen
      iexists evs, S, V, net, xnet, G
      iframe Hstr Hviews Hnet Hxnet HF
      ipureintro; exact Hpure
    imodintro
    iframe Hv Hl Hrv
    ipureintro
    have hA := Hpure.1.2.1
    exact ⟨⟨S, net, xnet, Hpre.2, Hxpre.2, hin, hA.2.2.1, by rw [← HVj]; exact hA.2.2.2.2 j⟩, Hli⟩
  · iexfalso
    iapply h_lo γ j
    iframe Hl Hover

/-- **The `Ready`'s transfer messages are `XPendOk`** (`readyOutP_b1`'s `hx`): each one's
`XReadyOk` (raft's `Ready` post) and its destination a server (`xdst_server`, over raft's
certificates and the cluster's names facts). -/
theorem xPend_of_msgs {R : AntSim.RunCfg} (γr : RaftNames) (md : RnMode) (id : w64) (p : PState)
    (ms : List QMsg)
    (hok : ∀ q ∈ ms, ∀ x, xmsgOf q.st = some x → XReadyOk γr md id p x)
    (hacks : ∀ a : w64, (γr.reAcks !! a).isSome → ∃ j : Fin R.N, a = AntSim.nodeId j)
    (hwins : ∀ a : w64, (γr.reWins !! a).isSome → ∃ j : Fin R.N, a = AntSim.nodeId j) :
    ([∗list] q ∈ ms, isRaftMsg (GF := GF) γr id q.st) ⊢
      ⌜∀ x ∈ ms.filterMap (fun q => xmsgOf q.st), AntSim.XPendOk R.N id p x⌝ := by
  induction ms with
  | nil => iintro -; ipureintro; intro x hx; simp at hx
  | cons q ms ih =>
    iintro ⟨#Hq, Hms⟩
    ihave %Hc := isRaftMsg_xdst γr id q.st $$ Hq
    ihave %Hr := ih (fun q' hq' => hok q' (List.mem_cons_of_mem _ hq')) $$ Hms
    ipureintro
    intro x hx
    rw [List.filterMap_cons] at hx
    cases hq : xmsgOf q.st with
    | none => rw [hq] at hx; exact Hr x hx
    | some y =>
      rw [hq] at hx
      rcases List.mem_cons.1 hx with rfl | hx'
      · have hxo := hok q List.mem_cons_self x hq
        have hd := xdst_server (R := R) hq Hc hacks hwins hxo.2.2.1
        exact xPendOk_of hxo (fun _ => hd) (fun _ => hd)
      · exact Hr x hx'

/-- A sent message's witness and a lower bound of the sent list: a lower bound past both. -/
theorem sentLb_join (γ : AntNames) (net₀ : List Msg) (m : Msg) :
    sentW (GF := GF) γ m ∗ sentLb γ net₀ ⊢ ∃ net₁, sentLb γ net₁ ∗ ⌜net₀ <+: net₁ ∧ m ∈ net₁⌝ := by
  unfold sentW sentLb monoListIdxOwn
  iintro ⟨⟨%i, %l1, %Hl1, #H1⟩, #H0⟩
  icases mono_list_lb_valid γ.sent net₀ l1 $$ H0 H1 with %Hpre
  rcases Hpre with Hpre | Hpre
  · iexists l1; iframe H1; ipureintro; exact ⟨Hpre, List.mem_of_getElem? Hl1⟩
  · iexists net₀; iframe H0; ipureintro
    exact ⟨List.prefix_refl _, List.mem_of_getElem? (prefix_getElem? Hpre Hl1)⟩

/-- A sent transfer message's witness and a lower bound of the sent list: a lower bound past both. -/
theorem xsentLb_join (γ : AntNames) (xnet₀ : List XMsg) (x : XMsg) :
    xsentW (GF := GF) γ x ∗ xsentLb γ xnet₀ ⊢
      ∃ xnet₁, xsentLb γ xnet₁ ∗ ⌜xnet₀ <+: xnet₁ ∧ x ∈ xnet₁⌝ := by
  unfold xsentW xsentLb monoListIdxOwn
  iintro ⟨⟨%i, %l1, %Hl1, #H1⟩, #H0⟩
  icases mono_list_lb_valid γ.xsent xnet₀ l1 $$ H0 H1 with %Hpre
  rcases Hpre with Hpre | Hpre
  · iexists l1; iframe H1; ipureintro; exact ⟨Hpre, List.mem_of_getElem? Hl1⟩
  · iexists xnet₀; iframe H0; ipureintro
    exact ⟨List.prefix_refl _, List.mem_of_getElem? (prefix_getElem? Hpre Hl1)⟩

theorem evRecv_chgOk (id : w64) (m : Msg) : (AntSim.evRecv id m).ChgOk 0 := by
  intro l hl e he
  simp only [AntCheck.Event.entryLists, AntSim.evRecv, AntCheck.Msg.entryLists, AntSim.msgOf,
    Option.map_some, Option.getD_some, Option.getD_none, List.nil_append, List.cons_append,
    List.mem_cons, List.not_mem_nil, or_false, List.flatMap_nil, List.append_nil] at hl
  rcases hl with rfl | rfl
  · cases he
  · obtain ⟨x, -, rfl⟩ := List.mem_map.1 he
    exact Nat.le_of_eq (entOf_chgSize x)

theorem evRecvX_chgOk (id : w64) (x : XMsg) : (AntSim.evRecvX id x).ChgOk 0 := by
  intro l hl e he
  simp only [AntCheck.Event.entryLists, AntSim.evRecvX, AntCheck.Msg.entryLists, AntSim.xmsgOf,
    Option.map_some, Option.getD_some, Option.getD_none, List.nil_append, List.cons_append,
    List.mem_cons, List.not_mem_nil, or_false, List.flatMap_nil, List.append_nil] at hl
  rcases hl with rfl | rfl <;> cases he

/-- **`reportCause`'s reports** (the drain's first report of an iteration): from the cause cell
against the view (`causeOwn`), the pending report `o` and `reports` of it: the handled message's
`recv` (`antSim_recv_in` / `antSim_recvX_in`, the view `told`), or nothing; the caller's `Φ` at the
view with `told` set as `Told` needs, the sent lists' lower bounds grown. -/
theorem causeOwn_report (h_vu : view_update.law (GF := GF)) (h_lo : nodeLive_over.law (GF := GF))
    (c : Loc) (γ : AntNames) (j : Fin γ.R.N) (v : AntSim.NodeView) (net₀ : List Msg)
    (xnet₀ : List XMsg) (cl : Loc) (Φ : IProp GF)
    (hinm : ∀ S V net xnet, AntSim.AntSim γ.R γ.dec S V net xnet →
      AntSim.InMask AntSim.mskB1 γ.R net xnet) :
    antCluster c γ ∗ sentLb γ net₀ ∗ xsentLb γ xnet₀ ∗ causeOwn γ j v cl ∗ viewFrag γ j v ∗
        nodeLive γ j ∗
        (∀ (b : Bool) (net : List Msg) (xnet : List XMsg),
          ⌜(v.byE = go!"recv" → b = true) ∧ net₀ <+: net ∧ xnet₀ <+: xnet⌝ -∗ sentLb γ net -∗
            xsentLb γ xnet -∗ viewFrag γ j { v with told := b } -∗ nodeLive γ j -∗ Φ) ⊢
      ∃ o : Option AntCheck.Event, pendingCause cl o ∗
        reports γ.strm (o.toList.map (atNode (AntSim.nameOf (AntSim.nodeId j)))) Φ := by
  iintro ⟨#Hc, #Hlb, #Hxlb, Hco, Hv, Hl, HΦ⟩
  unfold causeOwn
  by_cases hp : v.byE = go!"recv" ∧ v.told = false
  · rw [if_pos hp]
    icases Hco with (⟨%m, %Hm, Hpc, #Hw, Hr⟩ | ⟨%x, %Hx, Hpc, #Hw, Hr⟩)
    · ihave ⟨%net₁, #Hlb1, %Hn1⟩ := sentLb_join γ net₀ m $$ [$Hw $Hlb]
      iexists some (recvEvM (AntSim.msgOf m (AntSim.nodeId j)))
      iframe Hpc
      have hev : atNode (AntSim.nameOf (AntSim.nodeId j)) (recvEvM (AntSim.msgOf m (AntSim.nodeId j))) =
          AntSim.evRecv (AntSim.nodeId j) m := rfl
      simp only [Option.toList, List.map_cons, List.map_nil, hev]
      iapply report_upd h_vu h_lo c γ j v { v with told := true } (AntSim.evRecv (AntSim.nodeId j) m)
        net₁ [] xnet₀ [] (fun G0 G => G = G0) Φ Hm.2.2 (evRecv_chgOk _ _)
      · intro evs S V net xnet G0 G hpre hlogs hQ hVj hn hx
        subst hQ
        refine ⟨?_, hpre.2.2.1, ?_⟩
        · simp only [List.append_nil]
          have := AntSim.antSim_recv_in AntSim.mskB1 mskB1_le γ.R γ.dec S V net xnet evs G j m
            (hinm S V net xnet hpre.2.1) hpre (hn.subset Hn1.2) Hm.2.1 (by rw [hVj]; exact Hm.1)
          rw [hVj] at this; exact this
        · exact setV_logs hlogs (fun _ h => h) (by rw [← hVj]; exact hlogs j)
      iframe Hc Hlb1 Hxlb Hr Hv Hl
      isplitr
      · iapply factsExt_none
      iintro ⟨Hv, Hl, %net, %xnet, #Hlb2, #Hxlb2, %Hp2⟩
      iapply HΦ $$ %true %net %xnet [] Hlb2 Hxlb2 Hv Hl
      ipureintro; exact ⟨fun _ => rfl, Hn1.1.trans Hp2.1, Hp2.2.2.1⟩
    · ihave ⟨%xnet₁, #Hxlb1, %Hx1⟩ := xsentLb_join γ xnet₀ x $$ [$Hw $Hxlb]
      iexists some (recvEvM (AntSim.xmsgOf x))
      iframe Hpc
      have hev : atNode (AntSim.nameOf (AntSim.nodeId j)) (recvEvM (AntSim.xmsgOf x)) =
          AntSim.evRecvX (AntSim.nodeId j) x := rfl
      simp only [Option.toList, List.map_cons, List.map_nil, hev]
      iapply report_upd h_vu h_lo c γ j v { v with told := true } (AntSim.evRecvX (AntSim.nodeId j) x)
        net₀ [] xnet₁ [] (fun G0 G => G = G0) Φ Hx.2.2 (evRecvX_chgOk _ _)
      · intro evs S V net xnet G0 G hpre hlogs hQ hVj hn hx
        subst hQ
        refine ⟨?_, hpre.2.2.1, ?_⟩
        · simp only [List.append_nil]
          have := AntSim.antSim_recvX_in AntSim.mskB1 mskB1_le γ.R γ.dec S V net xnet evs G j x
            (hinm S V net xnet hpre.2.1) hpre (hx.subset Hx1.2) Hx.2.1 (by rw [hVj]; exact Hx.1)
          rw [hVj] at this; exact this
        · exact setV_logs hlogs (fun _ h => h) (by rw [← hVj]; exact hlogs j)
      iframe Hc Hlb Hxlb1 Hr Hv Hl
      isplitr
      · iapply factsExt_none
      iintro ⟨Hv, Hl, %net, %xnet, #Hlb2, #Hxlb2, %Hp2⟩
      iapply HΦ $$ %true %net %xnet [] Hlb2 Hxlb2 Hv Hl
      ipureintro; exact ⟨fun _ => rfl, Hp2.1, Hx1.1.trans Hp2.2.2.1⟩
  · rw [if_neg hp]
    iexists none
    iframe Hco
    simp only [Option.toList, List.map_nil, reports]
    iapply HΦ $$ %v.told %net₀ %xnet₀ [] Hlb Hxlb Hv Hl
    ipureintro
    refine ⟨fun hb => ?_, List.prefix_refl _, List.prefix_refl _⟩
    cases ht : v.told
    · exact absurd ⟨hb, ht⟩ hp
    · rfl

end proof

end AntHarness
end EtcdGrove
end Perennial
