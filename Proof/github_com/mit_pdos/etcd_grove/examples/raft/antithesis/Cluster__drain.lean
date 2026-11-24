/-
Lean-first (no Rocq counterpart). #33 S4: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/Cluster__drain.lean`: a loop whose
invariant is the loop head (`nodeOwn … (.loop net₀ ps₁)`, the `by` kept); `HasReady` false ends it
(`drain_exit`); otherwise `Ready` (its *enter* under the crash token, `readyExt` growing raft's facts),
the `ready` report and the write if the hard state, the entries or the role changed (`report_au`,
`readyStep`; `Append`, `SetHardState`, `rawNode_appended`), or the silent `Ready` (`quiet_upd`,
`Quiet.silentReady`); the rest of the iteration is `DrainPhases.lean`'s `drainSend.stmt` and
`drainAdvance.stmt`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster__drain
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainReadyPure
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainBounds
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainExt
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainMsgs
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.roleOf
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Name
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster__reportCause
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Recorder__record
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.entriesOf
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetIndex
public import Spec.go_etcd_io.raft.v3.raftpb.HardState__GetTerm
public import Spec.go_etcd_io.raft.v3.raftpb.HardState__GetVote
public import Spec.go_etcd_io.raft.v3.raftpb.HardState__GetCommit
public import Spec.go_etcd_io.raft.v3.IsEmptyHardState
public import Spec.go_etcd_io.raft.v3.IsEmptySnap
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Append
public import Spec.go_etcd_io.raft.v3.MemoryStorage__SetHardState
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainSteps
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainStore
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainPure
public import Proof.ReceiptTactics

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- Log matching read entrywise: at the same index and term, the same entry. -/
theorem logMatch_eq {l1 l2 : List EntryM} (h1 : AntSim.LogIdx l1) (h2 : AntSim.LogIdx l2)
    (hR : RecsAgree base0 l1 base0 l2) :
    ∀ (k : Nat) (e f : EntryM), l1[k]? = some e → l2[k]? = some f → e.Term' = f.Term' → e = f := by
  intro k e f he hf ht
  have h := congrArg (fun l => l[k]?) (logMatch_of_recs h1 h2 hR k e f he hf ht)
  simp only [List.getElem?_take, Nat.lt_succ_self, ↓reduceIte, he, hf] at h
  exact Option.some.inj h

/-- The `ready` report's numbers: the state's within `2 ^ 61`, its term too, the entries the log's. -/
theorem evReady_numsOk {id : w64} {b : AntCheck.Str} {r : Role} {ps : PState} {vo : w64}
    {es : List EntryM} (hsn : AntSim.StateNums (2 ^ 61) ps) (ht : uint.Z ps.term < 2 ^ 61)
    (hes : ∀ e ∈ es, e ∈ ps.log) :
    (AntSim.evReady id b r ps.term vo ps.commit es).NumsOk := by
  have hE : ∀ e ∈ es, uint.Z e.Term' < 2 ^ 61 ∧ uint.Z e.Index' < 2 ^ 61 :=
    fun e he => hsn.2.2.2.2 e (hes e he)
  have hc := hsn.2.2.2.1
  simp only [AntSim.evReady, AntCheck.Event.NumsOk, AntCheck.optNumOk, AntCheck.numOk,
    AntCheck.numBound, AntCheck.entriesOk, AntSim.logOf]
  and_intros
  all_goals try exact True.intro
  all_goals try (intro _ h; cases h; done)
  all_goals first
    | (intro es' hes'
       simp only [Option.some.injEq] at hes'
       subst hes'
       intro x hx
       obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
       have := (hE e he).1
       unfold AntSim.entOf
       split <;> exact ⟨by word, by word⟩)
    | (cases es with
        | nil => simp only [AntSim.firstOf]; omega
        | cons e _ =>
          have := (hE e List.mem_cons_self).2
          simp only [AntSim.firstOf]; word)
    | word

theorem evReady_weight (id : w64) (b : AntCheck.Str) (r : Role) (t vo c : w64) (es : List EntryM) :
    (AntSim.evReady id b r t vo c es).weight = es.length + 2 := by
  simp [AntSim.evReady, AntCheck.Event.weight, AntCheck.Event.size, AntSim.logOf]

/-- **(interim) A `Ready`'s messages are read and go to voters**: `drainReady_pure`'s `habs` and
`hvot`, until raft's `Ready` post states them (`mtypeOf ≠ none`, `To' ∈ γ.reCfg`: the raft helper's
pass); then this premise goes. -/
abbrev readyMsgsOk.law : Prop :=
  ∀ (id : w64) (rs : RNState) (ps : PState) (h : HardStateM) (es ce : List EntryM) (ms : List QMsg)
    (ss : Option (w64 × StateType)),
  ReadyOut id rs ps h es ce ms ss none →
  (∀ q ∈ ms, (absMsgOf q.st).isSome) ∧
    ∀ q ∈ ms.filterMap (fun q => absMsgOf q.st), ∃ j : Fin 3, q.dst = AntSim.nodeId j

end pure

section peek
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]

/-- `drain_peek`, with the view's log's records (raft's facts certify each view's log). -/
theorem drain_peekRecs (γ : AntNames) (j : Fin 3) (v : AntSim.NodeView) (net₀ : List Msg) :
    inv antN (antInv (GF := GF) γ) ∗ sentLb γ net₀ ∗ viewFrag γ j v ∗ nodeLive γ j ⊢
      |={⊤}=> ⌜∃ (S : AntCheck.State) (net : List Msg), AntSim.NetOk S net ∧
          AntSim.NodeOk S net j v ∧ net₀ <+: net⌝ ∗
        logRecs γ.raft.raftNames base0 v.ps.log ∗ ⌜AntSim.LogIdx v.ps.log⌝ ∗
        viewFrag γ j v ∗ nodeLive γ j := by
  iintro ⟨#Hinv, #Hlb, Hv, Hl⟩
  iunfold sentLb at Hlb
  iinv Hinv with >Hi Hclose
  iunfold antInv at Hi
  icases Hi with (Hi | Hover)
  · iunfold antOpen at Hi
    icases Hi with ⟨%evs, %S, %V, %net, %G, Hstr, H0, H1, H2, Hnet, %Hpure, #HF⟩
    ihave %Hpre := mono_list_auth_lb_valid (GF := GF) γ.sent 1 net net₀ $$ Hnet Hlb
    imod view_update _ γ j V v v $$ [Hv H0 H1 H2] with ⟨%HVj, Hv, H0, H1, H2⟩
    · iframe Hv H0 H1 H2
    rw [setV_self HVj]
    ihave #HF' := HF
    iunfold raftFactsOwn at HF'
    icases HF' with ⟨-, -, #Hlogs, -, -, -⟩
    have hmem : v.ps.log ∈ G.logs := by rw [← HVj]; exact Hpure.2.2.2 j
    ihave ⟨#Hrv, %Hli⟩ := BigSepL.bigSepL_mem
      (Φ := fun l => iprop(logRecs γ.raft.raftNames base0 l ∗ ⌜AntSim.LogIdx l⌝)) hmem $$ Hlogs
    imod Hclose $$ [Hstr H0 H1 H2 Hnet] with -
    · inext
      iunfold antInv
      ileft
      iunfold antOpen
      iexists evs, S, V, net, G
      iframe Hstr H0 H1 H2 Hnet HF
      ipureintro; exact Hpure
    imodintro
    iframe Hv Hl Hrv
    ipureintro
    obtain ⟨-, hA, -⟩ := Hpure.1
    exact ⟨⟨S, net, hA.2.2.1, by rw [← HVj]; exact hA.2.2.2 j, Hpre.2⟩, Hli⟩
  · iexfalso
    iapply nodeLive_over γ j
    iframe Hl Hover

/-- A `Ready`'s soft state: `nil` with none, or its `RaftState` field read-only. -/
theorem softStateIs_cases (p : Loc) (ss : Option (w64 × StateType)) :
    softStateIs (GF := GF) p ss ⊢
      ⌜ss = none ∧ p = null⌝ ∨
        ∃ (ld : w64) (st : StateType), ⌜ss = some (ld, st) ∧ p ≠ null⌝ ∗
          structFieldRef SoftState go!"RaftState" p ↦□ st := by
  cases ss with
  | none =>
    iintro H; iunfold softStateIs at H; ileft; icases H with %H; ipureintro; exact ⟨rfl, H⟩
  | some x =>
    obtain ⟨ld, st⟩ := x
    iintro H; iunfold softStateIs at H; iright
    icases H with ⟨%Hn, -, #Hst⟩
    iexists ld, st; iframe Hst; ipureintro; exact ⟨rfl, Hn⟩

end peek

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

set_option maxHeartbeats 4000000 in
theorem Cluster.drain.wp_proof
    (wp_HasReady : RawNode.HasReady.apiSpec (GF := GF) (hG := hG))
    (wp_Ready : RawNode.Ready.apiSpec (GF := GF) (hG := hG))
    (hsend : drainSend.stmt (GF := GF) (hG := hG))
    (hadv : drainAdvance.stmt (GF := GF) (hG := hG))
    (h_vote : rawNode_vote.law (GF := GF) (hG := hG))
    (h_wf : rawNode_wf.law (GF := GF) (hG := hG))
    (h_ns : rawNode_noSnap.law (GF := GF) (hG := hG))
    (h_lt : rawNode_logTerms.law (GF := GF) (hG := hG))
    (h_ttc : rawNode_term_tc.law (GF := GF) (hG := hG))
    (h_bp : rnBudget_persistent.law (GF := GF) (hG := hG))
    (h_tlp : rnTermLB_persistent.law (GF := GF) (hG := hG))
    (h_rb : rnTermLB_rb.law (GF := GF) (hG := hG))
    (h_recs : rawNode_logRecs.law (GF := GF) (hG := hG))
    (h_cinv : rawNode_commitInv.law (GF := GF) (hG := hG))
    (h_commit : rawNode_commit.law (GF := GF) (hG := hG))
    (h_committed : rawNode_committed.law (GF := GF) (hG := hG))
    (h_leader : rawNode_leader.law (GF := GF) (hG := hG))
    (h_rdm : readyMsgsOk.law) (hshape : AntSim.msgShape.stmt)
    (wp_roleOf : roleOf.spec (GF := GF) (hG := hG))
    (wp_IsEmptyHardState : IsEmptyHardState.spec (GF := GF) (hG := hG))
    (wp_GetTerm : raftpb.HardState.GetTerm.spec (GF := GF) (hG := hG))
    (wp_GetVote : raftpb.HardState.GetVote.spec (GF := GF) (hG := hG))
    (wp_GetCommit : raftpb.HardState.GetCommit.spec (GF := GF) (hG := hG))
    (wp_IsEmptySnap : IsEmptySnap.spec (GF := GF) (hG := hG)) :
    Cluster.drain.spec (GF := GF) (hG := hG) := by
  intro _ c γ n j v net₀ ps₁ q
  wp_start as ⟨#Hc, #Hn, Hown, Had, Htok⟩
  iapply wp_fupd
  ihave #Hc' := Hc
  iunfold antCluster at Hc'
  icases Hc' with ⟨%cfg, %r, %ns, %stop, #Hcfg, %Hcok, #Hr, #Hrec, #Hro, %Hlen, #Hn0, #Hn1, #Hn2,
    #Hstop, #Hbc, #Hnj, #Hinv, %Hfits⟩
  ihave #Hrpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  wp_auto
  irename «by» => Hbp
  irename c => Hcp
  irename n => Hnp
  ihave IH : iprop(∃ (v' : AntSim.NodeView) (net : List Msg) (ps : PState),
      nodeOwn c γ j n v' (.loop net ps) ∗ ⌜v'.byE = v.byE⌝ ∗ netAdder c γ q ∗ threadTok)
      $$ [Hown Had Htok]
  · iexists v, net₀, ps₁; iframe Hown Had Htok; ipureintro; rfl
  wp_for_core
  icases IH with ⟨%v₀, %net, %ps, Hown, %Hby, Had, Htok⟩
  icases nodeOwn_loop_open c γ j n v₀ net ps $$ Hown with ⟨%rn, %rs, %ip, #Hrn, Hraw, %Hst, Hrest⟩
  wp_auto
  wp_apply wp_HasReady γ.raft.raftNames rn (AntSim.nodeId j) rs ps [] ip $$ [$Hrpkg $Hraw] as %b ⟨Hraw, %Hb⟩
  wp_if_destruct
  · obtain ⟨hrv, hR, hip⟩ := Hst
    iunfold loopRest at Hrest
    icases Hrest with ⟨%ms, %si, %cl, %applied, #Hms, Hbs, %Hsto, Hnr, Hrole, Hterm, Hvote, Hcommit,
      Hapl, Hcause, Hv, Hl, #Hlb, Hco, %hbyok, %HN⟩
    iunfold nodeRaft at Hnr
    icases Hnr with ⟨%x, %g, Hgv, Hfree, Hdur, Htlb, Hbud, %Hγ⟩
    -- the node's facts at the loop head
    icases h_wf _ _ _ _ _ _ _ $$ Hraw with ⟨%Hwf, Hraw⟩
    icases h_ns _ _ _ _ _ _ _ $$ Hraw with ⟨%Hns, Hraw⟩
    icases h_lt _ _ _ _ _ _ _ $$ Hraw with ⟨%Hlt, Hraw⟩
    icases h_ttc _ _ _ _ _ _ _ $$ Hraw with ⟨%Httc, Hraw⟩
    haveI := h_tlp γ.raft rs.tc
    haveI := h_bp γ.raft
    ihave #Htlb := Htlb
    ihave #Hbud := Hbud
    imod h_rb γ.raft rs.tc ⊤ (by solve_ndisj) $$ Hbud Htlb with %Hrb
    have htc : uint.Z rs.tc < 2 ^ 61 := by
      unfold antRunFits at Hfits
      have : uint.Z rs.tc = (uint.nat rs.tc : Int) := by word
      omega
    have hterm61 : ∀ e ∈ ps.log, uint.Z e.Term' < 2 ^ 61 := fun e he => by
      have := Hlt e he; omega
    imod rawNode_stateNums h_wf h_ns h_recs γ.raft.raftNames rn _ rs ps [] ip Hγ.2.2.2.1 Hfits
      hterm61 $$ Hraw with ⟨%Hsn, Hraw⟩
    icases h_recs _ _ _ _ _ _ _ $$ Hraw with ⟨#Hrecs, Hraw⟩
    icases h_cinv _ _ _ _ _ _ _ $$ Hraw with ⟨#Hcinv, Hraw⟩
    icases h_commit _ _ _ _ _ _ _ $$ Hraw with ⟨#Hcmt, Hraw⟩
    icases h_leader _ _ _ _ _ _ _ $$ Hraw with ⟨#Hld, Hraw⟩
    ihave Hcd := h_committed γ.raft.raftNames rn _ rs ps [] ip $$ Hraw
    imod (fupd_mask_mono CoPset.subseteq_top) $$ Hcd with ⟨#Hcmtd, Hraw⟩
    imod drain_peekRecs γ j v₀ net $$ [$Hinv $Hlb $Hv $Hl] with ⟨%Hpeek, #Hvrecs, %Hvidx, Hv, Hl⟩
    have hidx := logIdx_of_wf Hwf.1
    ihave %Hag := recs_pair γ.raft.raftNames v₀.ps.log ps.log $$ [$Hvrecs $Hrecs]
    · ipureintro; exact hidx
    have hmatch := logMatch_eq Hvidx hidx Hag.1
    wp_apply wp_Ready γ.raft.raftNames rn (AntSim.nodeId j) x rs ps [] ip 1 g hrv.2.2.2.2.1
      hrv.2.2.2.2.2.1 Hγ.1 $$ [$Hrpkg $Hraw $Hgv $Hfree]
      as %rd %ce %es %rms %sts %h %steps %L %ss %W %qs' %ip' Hpost
    icases Hpost with ⟨Hraw, Hlive, Henter, #Hlead, #Hsnapto, #Hsrcs, #Hss, #Hce, #Hcommitted,
      #Hents, Hmsgs, Hmsgs_cap, Hmsgs_own, -, %Hmsgs_term, Hsnapz, %Hpsn, -, -, #Hhard, #Hhsw, Happ,
      #Hfrz, -, %Hout⟩
    obtain ⟨hqs', hro, hfirst, hip', hhne⟩ := Hout trivial
    have hL : L = none := hro.2.2.2.2.2.2.2.2
    subst hL
    iapply (wp_ncfupd _ _ (by rfl))
    unfold ncfupd
    iintro Hnc
    imod Henter $$ %⊤ %(1 : Qp) %CoPset.subseteq_top Hnc [$Hdur $Hlive] with
      ⟨Hnc, Hdur, Hlive, Hfree, Hdf, #Hmok⟩
    ihave Hvd := h_vote γ.raft.raftNames (AntSim.nodeId j) _ $$ Hdur
    imod (fupd_mask_mono CoPset.subseteq_top) $$ Hvd with ⟨#Hvt, Hdur⟩
    -- raft's facts for the `ready` report (`readyExt`)
    have hS : (readyDurable rs.dur (phsNext rs.phs h) none es).term = ps.term ∧
        (readyDurable rs.dur (phsNext rs.phs h) none es).vote = ps.vote := by
      have h2 := hro.2.1
      simp only [readyDurable, RaftState.next, Option.map_none, h2]
      and_intros <;> first | trivial | rfl
    ihave #Hsrc : readySrc γ.raft.raftNames (AntSim.nodeId j) ps $$ []
    · iunfold readySrc
      iframe Hcinv Hrecs Hcmt Hcmtd Hld
      isplitr
      · rw [← hS.1, ← hS.2]; iexact Hvt
      ipureintro
      refine ⟨Hwf.1, ?_, Hγ.2.2.2.1⟩
      have := Hwf.2.1
      simp only [plogLastIndexZ, base0] at this
      have h0 : uint.Z (W64 0) = 0 := by word
      rw [h0] at this
      word
    ihave #Hext := readyExt γ (AntSim.nodeId j) ps Hγ.2.2.2.2 $$ Hsrc
    obtain ⟨Sx, netx, hnet, hnok, hpre⟩ := Hpeek
    obtain ⟨habs, hvot⟩ := h_rdm _ _ _ _ _ _ _ _ hro
    have hpure := drainReady_pure hshape hrv hR hip hro hqs' hfirst Hns.1 hidx hmatch habs hvot hnet hnok
      hpre HN Hsn Hmsgs_term
    imodintro
    iframe Hnc
    -- the role (`rd.SoftState`)
    icases softStateIs_cases _ _ $$ Hss with (%Hsn0 | ⟨%ld, %st, %Hsn1, #Hst⟩)
    focus
      rw [Hsn0.2]
      wp_auto
      have hr : roleStr (roleGo v₀.ps.role) = roleStr (roleAfter rs.role ss) := by
        rw [Hsn0.1, ← hrv.2.1]; rfl
      rw [hr]
    rotate_left
    focus
      have hnn : decide (rd.SoftState' = null) = false := decide_eq_false Hsn1.2
      rw [hnn]
      wp_auto
      ihave #Hrpkg' : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis $$ []
      · iexact Hpkg
      wp_apply wp_roleOf st $$ [$Hpkg]
      have hr : roleStr st = roleStr (roleAfter rs.role ss) := by rw [Hsn1.1]; rfl
      rw [hr]
    rotate_left
    all_goals
      -- the hard state (`hsNew`); the term, vote and commit after it are the state's
      have hphs := hrv.1
      have hnext := hro.2.1
      have hold : ¬ HsNew h → ps.term = v₀.ps.term ∧ ps.vote = v₀.ps.vote ∧ ps.commit = v₀.ps.commit := by
        intro hn
        unfold HsNew at hn; simp only [Classical.not_not] at hn
        rw [phsNext_empty _ _ hn, hphs] at hnext
        obtain ⟨a, b, c⟩ := hardStateM_mk_inj hnext
        exact ⟨a.symm, b.symm, c.symm⟩
      have hnew : HsNew h → h.Term' = ps.term ∧ h.Vote' = ps.vote ∧ h.Commit' = ps.commit := by
        intro hn
        rw [phsNext_ne _ _ hn] at hnext
        rw [hnext]; exact ⟨rfl, rfl, rfl⟩
      ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
      · iPkgInit
      ihave #Hhard' := Hhard
      iunfold hsOptC at Hhard'
      icases Hhard' with (%Hh0 | #Hhro)
      focus
        have hd : decide (rd.HardState' = null) = true := decide_eq_true Hh0.1
        rw [hd]
        wp_auto
        have hn : ¬ HsNew h := by rw [Hh0.2]; unfold HsNew; simp
        obtain ⟨e1, e2, e3⟩ := hold hn
        rw [← e1, ← e2, ← e3]
        first
          | rw [show (!true) = decide (HsNew h) by simp [hn]]
          | rw [show false = decide (HsNew h) by simp [hn]]
      rotate_left
      focus
        ihave %hnn : ⌜rd.HardState' ≠ null⌝ $$ [Hhro]
        · iunfold hsROC at Hhro
          icases Hhro with ⟨%pt, %pv, %pc, %Hnn, -⟩
          ipureintro; exact Hnn
        have hd : decide (rd.HardState' = null) = false := decide_eq_false hnn
        rw [hd]
        wp_auto
        ihave #Hho := hsOptC_hsOpt _ _ $$ Hhard
        wp_apply wp_IsEmptyHardState rd.HardState' h $$ [$Hrpkg $Hho]
        ihave #Hhr := hsROC_hsRO _ _ $$ Hhro
        by_cases hn : HsNew h
        focus
          have hz : decide (h.Term' = W64 0 ∧ h.Vote' = W64 0 ∧ h.Commit' = W64 0) = false :=
            decide_eq_false hn
          rw [hz]
          wp_auto
          wp_apply wp_GetTerm.1 rd.HardState' h $$ [$Hpb $Hhr]
          wp_apply wp_GetVote.1 rd.HardState' h $$ [$Hpb $Hhr]
          wp_apply wp_GetCommit.1 rd.HardState' h $$ [$Hpb $Hhr]
          obtain ⟨e1, e2, e3⟩ := hnew hn
          rw [e1, e2, e3]
          first
            | rw [show (!false) = decide (HsNew h) by simp [hn]]
            | rw [show true = decide (HsNew h) by simp [hn]]
        rotate_left
        focus
          have hz : decide (h.Term' = W64 0 ∧ h.Vote' = W64 0 ∧ h.Commit' = W64 0) = true :=
            decide_eq_true (by unfold HsNew at hn; simpa using hn)
          rw [hz]
          wp_auto
          obtain ⟨e1, e2, e3⟩ := hold hn
          rw [← e1, ← e2, ← e3]
          first
            | rw [show (!true) = decide (HsNew h) by simp [hn]]
            | rw [show false = decide (HsNew h) by simp [hn]]
        rotate_left
      rotate_left
      all_goals
        -- no snapshot
        iunfold rdSnapOut at Hsnapz
        icases Hsnapz with %Hsnull
        rw [Hsnull]
        ihave Hso : snapOpt (GF := GF) null DFrac.discard none $$ []
        · simp only [snapOpt]; ipureintro; trivial
        wp_apply wp_IsEmptySnap null DFrac.discard none $$ [$Hrpkg $Hso] as %bs ⟨%Hbs, -⟩
        simp only [Option.elim] at Hbs
        subst Hbs
        wp_auto
        -- `write`
        have hmd : γ.raft.raftNames.maxData.isSome = false := by rw [Hγ.2.2.1]; rfl
        ihave #Hents' := entsROz_entsRO _ _ _ $$ Hents
        ihave %Heslen := entsPts_len _ _ _ $$ Hents'
        have hwrite : ∀ b : Bool, (b = true ↔ HsNew h ∨ es ≠ []) → b = decide (HsNew h ∨ es ≠ []) :=
          fun b hb => by cases b <;> simp_all
        wp_if_destruct
        focus
          (try wp_auto)
          rw [hwrite true (by simp [Hif])]
        rotate_left
        focus
          (try wp_auto)
          rw [hwrite (decide (sint.Z (W64 0) < sint.Z rd.Entries'.len)) (by
            have h0 : sint.Z (W64 0) = 0 := by word
            have hl : es ≠ [] ↔ 0 < es.length :=
              by cases es <;> simp
            rw [h0, decide_eq_true_iff, hl]
            have := Heslen.1
            have h2 : sint.nat rd.Entries'.len = (sint.Z rd.Entries'.len).toNat := rfl
            constructor
            · intro hh; right; omega
            · rintro (hh | hh)
              · exact absurd hh Hif
              · omega)]
        rotate_left
        all_goals sorry
  · have hb : b = false := by cases b; rfl; exact absurd rfl Hif
    subst hb
    obtain ⟨hP, hip⟩ := Hb rfl
    wp_if_destruct
    · try simp only [decide_true, decide_True, ↓reduceIte]
      try wp_auto
      imod drain_exit c γ j n v₀ net ps rn rs ip Hst.1 Hst.2.1 hP hip $$ [$Hinv $Hrn $Hraw $Hrest]
        with Hown
      imodintro
      iapply HΦ
      iframe Hown Had Htok
      ipureintro; exact Hby
    · exact absurd rfl ‹¬(#false : val) = #false›
