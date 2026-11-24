/-
Lean-first (no Rocq counterpart). #33 S4: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/Cluster__drain.lean`: a loop whose
invariant is the loop head (`nodeOwn … (.loop net₀ ps₁)`, the `by` kept); `HasReady` false ends it
(`drain_exit`); otherwise `Ready` (its *enter* under the crash token, `readyExt` growing raft's facts),
the `ready` report and the write if the hard state, the entries or the role changed (`report_au`,
`readyStep`; `Append`, `SetHardState`, `rawNode_appended`), or the silent `Ready` (`quiet_upd`,
`Quiet.silentReady`); the rest of the iteration is `DrainPhases.lean`'s `drainSend.stmt` and
`drainAdvance.stmt`. Each of the iteration's `if`s is proved under `wp_bind` and `wp_wand` with a
postcondition both arms meet, so the rest of the iteration is proved once. Two interim premises wait
for raft's laws: `readyMsgsOk.law` (a `Ready`'s messages are read and go to voters) and
`rawNode_phsTerm.law` (the last hard state handed out is at most the node's term; now raft's,
`RawNodeApi.lean`).
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
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainAdvWp
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

/-- `Reach` does not read `told` (the drain's `reportCause` sets it). -/
theorem reach_told {id : w64} {net : List Msg} {v : AntSim.NodeView} {ps : PState} (b : Bool)
    (h : AntSim.Reach id net v ps) : AntSim.Reach id net { v with told := b } ps := by
  cases h with
  | stay hi => exact .stay _ hi
  | input inp _ hi hb hc hm hs => exact .input _ inp _ hi hb hc hm hs
  | advance _ hp hc hb ha => exact .advance _ _ hp hc hb ha

theorem roleStr_roleGo (r : Role) : roleStr (roleGo r) = AntSim.roleOf r := by
  cases r <;> rfl

/-- A `Ready`'s entries are in the log (`ReadyOut`'s `drop`). -/
theorem readyEnts_mem {ps : PState} {es : List EntryM}
    (h : ∀ e0 ∈ es.head?, ps.log.drop (uint.nat e0.Index' - 1) = es) : ∀ e ∈ es, e ∈ ps.log := by
  intro e he
  cases hes : es with
  | nil => rw [hes] at he; cases he
  | cons e0 t =>
    have hd := h e0 (by rw [hes]; rfl)
    rw [hes] at hd he
    rw [← hd] at he
    exact List.mem_of_mem_drop he

/-- A `Ready`'s entries' indices from the first (`ReadyOut`'s `drop` of a log whose indices are its
positions): `Append`'s premise. -/
theorem readyEnts_idx {l es : List EntryM} (hl : AntSim.LogIdx l)
    (hd : ∀ e0 ∈ es.head?, l.drop (uint.nat e0.Index' - 1) = es) (k : Nat)
    (hk : ∀ e0 ∈ es.head?, k = uint.nat e0.Index') :
    ∀ (i : Nat) (e : EntryM), es[i]? = some e → uint.nat e.Index' = k + i := by
  intro i e he
  cases hes : es with
  | nil => rw [hes] at he; simp at he
  | cons e0 t =>
    have hd0 := hd e0 (by rw [hes]; rfl)
    have hk0 := hk e0 (by rw [hes]; rfl)
    rw [hes] at hd0 he
    have h0 : l[uint.nat e0.Index' - 1 + 0]? = some e0 := by
      rw [← List.getElem?_drop, hd0]; rfl
    have hi : l[uint.nat e0.Index' - 1 + i]? = some e := by
      rw [← List.getElem?_drop, hd0]; exact he
    have a0 := hl _ _ h0
    have ai := hl _ _ hi
    have : uint.nat e0.Index' = (uint.Z e0.Index').toNat := rfl
    have : uint.nat e.Index' = (uint.Z e.Index').toNat := rfl
    omega

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

/-- The cause cell after a `Ready` (`afterReady` keeps the `by`, the cause and `told`). -/
theorem causeOwn_afterReady (γ : AntNames) (j : Fin 3) (v : AntSim.NodeView) (ps : PState)
    (rd : AntSim.ReadyD) (cl : Loc) :
    causeOwn (GF := GF) γ j (({ v with told := v.told } : AntSim.NodeView).afterReady ps rd) cl =
      causeOwn γ j v cl := rfl

end peek

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

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
    (wp_IsEmptySnap : IsEmptySnap.spec (GF := GF) (hG := hG))
    (h_app : rawNode_appended.law (GF := GF) (hG := hG))
    (h_phs : rawNode_phsTerm.law (GF := GF))
    (hready : AntSim.antSim_ready.stmt)
    (wp_reportCause : Cluster.reportCause.spec (GF := GF) (hG := hG))
    (wp_record : Recorder.record.spec (GF := GF) (hG := hG))
    (wp_entriesOf : entriesOf.spec (GF := GF) (hG := hG))
    (wp_Name : Name.spec (GF := GF) (hG := hG))
    (wp_EGetIndex : raftpb.Entry.GetIndex.spec (GF := GF) (hG := hG))
    (wp_Append : MemoryStorage.Append.spec (GF := GF) (hG := hG))
    (wp_SetHardState : MemoryStorage.SetHardState.spec (GF := GF) (hG := hG)) :
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
    icases h_phs _ _ _ _ _ _ _ $$ Hraw with ⟨%Hphst, Hraw⟩
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
      and_intros <;> trivial
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
    wp_bind (If _ _ _)
    iapply (wp_wand (Φ := fun w => iprop(⌜w = executeVal⌝ ∗
        role_ptr ↦ roleStr (roleAfter rs.role ss) ∗ rd_ptr ↦ rd))) $$ [role rd]
    · icases softStateIs_cases _ _ $$ Hss with (%Hsn0 | ⟨%ld, %st, %Hsn1, #Hst⟩)
      · rw [Hsn0.2]
        wp_auto
        have hr : roleStr (roleGo v₀.ps.role) = roleStr (roleAfter rs.role ss) := by
          rw [Hsn0.1, ← hrv.2.1]; rfl
        rw [hr]
        iframe
        ipureintro; rfl
      · have hnn : decide (rd.SoftState' = null) = false := decide_eq_false Hsn1.2
        rw [hnn]
        wp_auto
        wp_apply wp_roleOf st $$ [$Hpkg]
        have hr : roleStr st = roleStr (roleAfter rs.role ss) := by rw [Hsn1.1]; rfl
        rw [hr]
        iframe
        ipureintro; rfl
    iintro %w ⟨%Hw, role, rd⟩
    subst Hw
    wp_auto
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
    wp_bind (If _ _ _)
    iapply (wp_wand (Φ := fun w => iprop(⌜w = #(decide (HsNew h))⌝ ∗ rd_ptr ↦ rd))) $$ [rd]
    · ihave #Hhard' := Hhard
      iunfold hsOptC at Hhard'
      icases Hhard' with (%Hh0 | #Hhro)
      · have hd : decide (rd.HardState' = null) = true := decide_eq_true Hh0.1
        rw [hd]
        wp_auto
        have hn : ¬ HsNew h := by rw [Hh0.2]; unfold HsNew; simp
        iframe
        ipureintro; simp [hn]
      · ihave %hnn : ⌜rd.HardState' ≠ null⌝ $$ [Hhro]
        · iunfold hsROC at Hhro
          icases Hhro with ⟨%pt, %pv, %pc, %Hnn, -⟩
          ipureintro; exact Hnn
        have hd : decide (rd.HardState' = null) = false := decide_eq_false hnn
        rw [hd]
        wp_auto
        ihave #Hho := hsOptC_hsOpt _ _ $$ Hhard
        wp_apply wp_IsEmptyHardState rd.HardState' h $$ [$Hrpkg $Hho]
        iframe
        ipureintro; unfold HsNew; simp
    iintro %w ⟨%Hw, rd⟩
    subst Hw
    wp_auto
    wp_bind (If _ _ _)
    iapply (wp_wand (Φ := fun w => iprop(⌜w = executeVal⌝ ∗ rd_ptr ↦ rd ∗ term_ptr ↦ ps.term ∗
        vote_ptr ↦ ps.vote ∗ commit_ptr ↦ ps.commit))) $$ [rd term vote commit]
    · by_cases hn : HsNew h
      · rw [decide_eq_true hn]
        wp_auto
        ihave #Hhr : hsRO rd.HardState' h $$ []
        · ihave #Hhard' := Hhard
          iunfold hsOptC at Hhard'
          icases Hhard' with (%Hh0 | #Hhro)
          · exfalso; apply hn; rw [Hh0.2]; exact ⟨rfl, rfl, rfl⟩
          · iapply hsROC_hsRO _ _ $$ Hhro
        wp_apply wp_GetTerm.1 rd.HardState' h $$ [$Hpb $Hhr]
        wp_apply wp_GetVote.1 rd.HardState' h $$ [$Hpb $Hhr]
        wp_apply wp_GetCommit.1 rd.HardState' h $$ [$Hpb $Hhr]
        obtain ⟨e1, e2, e3⟩ := hnew hn
        rw [e1, e2, e3]
        iframe
        ipureintro; rfl
      · rw [decide_eq_false hn]
        wp_auto
        obtain ⟨e1, e2, e3⟩ := hold hn
        rw [e1, e2, e3]
        iframe
        ipureintro; rfl
    iintro %w ⟨%Hw, rd, term, vote, commit⟩
    subst Hw
    wp_auto
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
    wp_bind (If _ _ _)
    iapply (wp_wand (Φ := fun w => iprop(⌜w = #(decide (HsNew h ∨ es ≠ []))⌝ ∗ rd_ptr ↦ rd ∗
        hsNew_ptr ↦ decide (HsNew h)))) $$ [rd hsNew]
    · by_cases hn : HsNew h
      · rw [decide_eq_true hn]
        wp_auto
        iframe
        ipureintro; simp [hn]
      · rw [decide_eq_false hn]
        wp_auto
        iframe
        ipureintro
        have h0 : sint.Z (W64 0) = 0 := by word
        have hl : es ≠ [] ↔ 0 < es.length := by cases es <;> simp
        have := Heslen.1
        have h2 : sint.nat rd.Entries'.len = (sint.Z rd.Entries'.len).toNat := rfl
        have : (0 < sint.Z rd.Entries'.len) ↔ (HsNew h ∨ es ≠ []) := by
          rw [hl]; constructor
          · intro hh; right; omega
          · rintro (hh | hh)
            · exact absurd hh hn
            · omega
        rw [h0]
        simp only [this]
    iintro %w ⟨%Hw, rd, hsNew⟩
    subst Hw
    wp_auto
    -- `write || role != n.role`
    wp_bind (If (Val _) _ _)
    iapply (wp_wand (Φ := fun w => iprop(⌜w = #(decide (HsNew h ∨ es ≠ [] ∨
        roleStr (roleAfter rs.role ss) ≠ roleStr (roleGo v₀.ps.role)))⌝ ∗
        role_ptr ↦ roleStr (roleAfter rs.role ss) ∗ n_ptr ↦ n ∗
        n.[github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node, go!"role"] ↦
          roleStr (roleGo v₀.ps.role)))) $$ [role Hnp Hrole]
    · by_cases hw : HsNew h ∨ es ≠ []
      · rw [decide_eq_true hw]
        wp_auto
        iframe
        ipureintro
        have : HsNew h ∨ es ≠ [] ∨ roleStr (roleAfter rs.role ss) ≠ roleStr (roleGo v₀.ps.role) := by
          rcases hw with hw | hw
          · exact Or.inl hw
          · exact Or.inr (Or.inl hw)
        rw [decide_eq_true this]
      · rw [decide_eq_false hw]
        wp_auto
        iframe
        ipureintro
        simp only [not_or, Classical.not_not] at hw
        by_cases hc : roleStr (roleAfter rs.role ss) = roleStr (roleGo v₀.ps.role)
        · simp [hc, hw]
        · simp [hc, hw]
    iintro %w ⟨%Hw, role, Hnp, Hrole⟩
    subst Hw
    obtain ⟨rdD, hrdD⟩ : ∃ x, x = readyDOf ps es (rms.filterMap fun q => absMsgOf q.st) qs' ce :=
      ⟨_, rfl⟩
    rw [← hrdD] at hpure
    have hRepIff : (HsNew h ∨ es ≠ [] ∨
        roleStr (roleAfter rs.role ss) ≠ roleStr (roleGo v₀.ps.role)) ↔ AntSim.Reported v₀ rdD := by
      rw [hrdD, ← hrv.2.1]
      exact goReport_iff _ _ _ hrv.1 hrv.2.1 hro.1 hro.2.1 hhne
    have hr2 : roleStr (roleAfter rs.role ss) = roleStr (roleGo ps.role) := by rw [hro.1]
    rw [← Hby]
    wp_bind (If _ _ _)
    iapply (wp_wand (Φ := fun w => iprop(⌜w = executeVal⌝ ∗ rd_ptr ↦ rd ∗ n_ptr ↦ n ∗ c_ptr ↦ c ∗
        by_ptr ↦ v₀.byE ∗
        ∃ (b : Bool) (net₁ : List Msg) (cl' : Loc),
          n.[github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node, go!"role"] ↦ roleStr (roleGo ps.role) ∗
          n.[github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node, go!"term"] ↦ ps.term ∗
          n.[github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node, go!"vote"] ↦ ps.vote ∗
          n.[github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node, go!"commit"] ↦ ps.commit ∗
          n.[github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node, go!"cause"] ↦ cl' ∗
          nodeStor si ms (HardStateM.mk ps.term ps.vote ps.commit) ∗
          appendReceipt rs.storage es [] ∗
          viewFrag γ j (AntSim.NodeView.afterReady { v₀ with told := b } ps rdD) ∗ nodeLive γ j ∗
          sentLb γ net₁ ∗ causeOwn γ j (AntSim.NodeView.afterReady { v₀ with told := b } ps rdD) cl')))
      $$ [rd Hnp Hcp Hbp role Hrole Hterm Hvote Hcommit Hcause Hbs Happ Hv Hl Hco term vote commit
          hsNew write]
    · by_cases hrep : HsNew h ∨ es ≠ [] ∨
          roleStr (roleAfter rs.role ss) ≠ roleStr (roleGo v₀.ps.role)
      · rw [decide_eq_true hrep]
        have hesMem := readyEnts_mem hro.2.2.2.1
        have hesN : ∀ e ∈ es, uint.Z e.Term' < 2 ^ 61 ∧ uint.Z e.Index' < 2 ^ 61 :=
          fun e he => Hsn.2.2.2.2 e (hesMem e he)
        have hesNorm : AllNormal es := fun e he => hpure.2.1 e (hesMem e he)
        have hv0t : uint.Z v₀.ps.term < 2 ^ 61 := by
          have : rs.phs.Term' = v₀.ps.term := by rw [hrv.1]
          rw [← this]; have := Hwf.2.2; omega
        ihave #Hn' := Hn
        iunfold nodeRO at Hn'
        icases Hn' with ⟨%ch, #Hid, #Hname, #Hin, #Hbag⟩
        wp_take_receipt as Hr1
        wp_apply wp_reportCause c γ n j v₀ cl $$ [$Hpkg $Hc $Hn $Hcause $Hco $Hv $Hl]
          as ⟨Hcause, Hco, Hv, Hl⟩
        -- `first`
        ihave ⟨%els, #Hsl, #Hbig⟩ := entsRO_open _ _ $$ Hents'
        wp_bind (If _ _ _)
        iapply (wp_wand (Φ := fun w => iprop(⌜w = executeVal⌝ ∗ rd_ptr ↦ rd ∗
            ∃ fw : w64, first_ptr ↦ fw ∗ ⌜sint.Z fw = AntSim.firstOf es⌝))) $$ [rd first]
        · wp_if_destruct
          · have hpos : 0 < es.length := by
              have h1 := Heslen.1
              have : sint.Z (W64 0) = 0 := by word
              rw [this] at Hif; rw [h1]
              show 0 < (sint.Z rd.Entries'.len).toNat
              omega
            obtain ⟨e0, he0⟩ : ∃ e0, es[0]? = some e0 := ⟨_, List.getElem?_eq_getElem hpos⟩
            ihave ⟨%l0, %hl0, #He0⟩ := entsBig_lookup els es 0 e0 he0 $$ Hbig
            have hz : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z rd.Entries'.len := ⟨by word, Hif⟩
            simp only [hz, _root_.and_self, ↓reduceIte]
            wp_apply (wp_load_slice_index (t := go.GoType.PointerType raftpb.Entry.ty)
              rd.Entries' (sint.Z (W64 0)) els DFrac.discard l0 (by word)) $$ [] as -
            · iframe Hsl; ipureintro; exact hl0
            wp_apply wp_EGetIndex.1 l0 DFrac.discard e0 $$ [$Hpb $He0] as -
            iframe
            ipureintro
            obtain ⟨e1, rest, hcons⟩ : ∃ e1 rest, es = e1 :: rest := by
              cases hh : es with
              | nil => rw [hh] at hpos; simp at hpos
              | cons a b => exact ⟨a, b, rfl⟩
            rw [hcons] at he0
            simp only [List.getElem?_cons_zero, Option.some.injEq] at he0
            subst he0
            have := (hesN e1 (by rw [hcons]; exact List.mem_cons_self)).2
            rw [hcons]; simp only [AntSim.firstOf]; word
          · iframe
            ipureintro
            have hes0 : es = [] := by
              have h1 := Heslen.1
              have h2 : sint.Z (W64 0) = 0 := by word
              rw [h2] at Hif
              rw [show sint.nat rd.Entries'.len = (sint.Z rd.Entries'.len).toNat from rfl] at h1
              apply List.eq_nil_of_length_eq_zero; omega
            rw [hes0]; simp only [AntSim.firstOf]; decide
        iintro %w ⟨%Hw, rd, %fw, first, %Hfw⟩
        subst Hw
        -- the `ready` report
        wp_take_receipt as Hr2
        wp_apply wp_Name ps.vote $$ [$Hpkg]
        wp_apply wp_entriesOf rd.Entries' DFrac.discard els es hesNorm $$ [$Hpkg $Hsl $Hbig]
          as %out ⟨-, #Hout, Hr3⟩
        obtain ⟨b, hb, hbt⟩ : ∃ b, reportedView v₀ = { v₀ with told := b } ∧
            (v₀.byE = go!"recv" → b = true) := by
          unfold reportedView
          split
          · exact ⟨true, rfl, fun _ => rfl⟩
          · rename_i hh
            refine ⟨v₀.told, rfl, fun hb => ?_⟩
            simp only [not_and, Bool.not_eq_false] at hh; exact hh hb
        rw [hb]
        have htc' : uint.Z ps.term < 2 ^ 61 := by omega
        have hT : sint.Z ps.term = uint.Z ps.term := by word
        have hC : sint.Z ps.commit = uint.Z ps.commit := by have := Hsn.2.2.2.1; word
        have hstep := readyStep GF hready j { v₀ with told := b } ps rdD net (reach_told b hR) hpure.1
          (hRepIff.1 hrep) hbt (by show uint.Z v₀.ps.term + 1 < 2 ^ 64; omega) (by rw [hrdD]; exact evReady_numsOk Hsn htc' hesMem) Hfits
        have hev : AntSim.evReady (AntSim.nodeId j) ({ v₀ with told := b } : AntSim.NodeView).byE
            rdD.role rdD.term rdD.vote rdD.commit rdD.ents =
            AntSim.evReady (AntSim.nodeId j) v₀.byE ps.role ps.term ps.vote ps.commit es := by
          rw [hrdD]; rfl
        rw [hev] at hstep
        ipersist «$a0»
        ihave #Hev : AntCheck.eventRO «$a0_ptr»
            (AntSim.evReady (AntSim.nodeId j) v₀.byE ps.role ps.term ps.vote ps.commit es) $$ []
        · iunfold AntCheck.eventRO
          iexists _
          iframe «$a0»
          simp only [AntSim.evReady, AntCheck.fieldRO]
          isplitr
          · ipureintro
            simp only [AntCheck.fieldRel, AntCheck.hasBit, AntCheck.fB, AntCheck.fA, AntCheck.fBy,
              AntCheck.fRole, AntCheck.fTerm, AntCheck.fVote, AntCheck.fCommit, AntCheck.fFirst,
              AntCheck.fLastIndex, AntCheck.fLastTerm, AntCheck.fApplied, AntCheck.fSnap, AntCheck.fW,
              AntCheck.fMore, AntCheck.fIndex, AntCheck.fCtx, hT, hC, Hfw, hr2, roleStr_roleGo]
            and_intros <;> first | rfl | decide
          simp only [AntCheck.hasBit, AntCheck.fEntries, AntCheck.fVoters, AntCheck.fOutgoing,
            AntCheck.fMsg, AntCheck.fCause]
          rw [← entOfE_logOf (fun e he => (hesN e he).1)]
          iframe Hout
          ipureintro
          and_intros <;> decide
        ihave HAU := report_au γ j { v₀ with told := b }
          (({ v₀ with told := b } : AntSim.NodeView).afterReady ps rdD)
          (AntSim.evReady (AntSim.nodeId j) v₀.byE ps.role ps.term ps.vote ps.commit es) net []
          (fun G => AntSim.ReadyFacts G (AntSim.nodeId j) ps) hstep $$ [Hv Hl]
        · iframe Hinv Hlb Hv Hl
          imodintro
          iexact Hext
        ihave Hrc : ⧗ (AntSim.evReady (AntSim.nodeId j) v₀.byE ps.role ps.term ps.vote ps.commit
            es).weight $$ [Hr1 Hr2 Hr3]
        · rw [evReady_weight]
          iapply (receipt_add (GF := GF) (es.length + 1) 1).2
          iframe Hr2
          iapply (receipt_add (GF := GF) es.length 1).2
          iframe Hr3 Hr1
        wp_apply wp_record γ.strm r «$a0_ptr»
            (AntSim.evReady (AntSim.nodeId j) v₀.byE ps.role ps.term ps.vote ps.commit es) _
          $$ [$Hpkg $Hrec $Hev $Hrc $HAU] as ⟨Hv, Hl, %net₁, #Hlb1, %Hpre1⟩
        -- the write
        wp_bind (If _ _ _)
        iapply (wp_wand (Φ := fun w => iprop(⌜w = executeVal⌝ ∗ rd_ptr ↦ rd ∗ n_ptr ↦ n ∗
            n.[github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node, go!"term"] ↦ ps.term ∗
            n.[github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node, go!"vote"] ↦ ps.vote ∗
            n.[github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node, go!"commit"] ↦ ps.commit ∗
            nodeStor si ms (HardStateM.mk ps.term ps.vote ps.commit) ∗
            appendReceipt rs.storage es []))) $$ [rd Hnp Hterm Hvote Hcommit Hbs Happ term vote commit
              hsNew]
        · by_cases hw : HsNew h ∨ es ≠ []
          · rw [decide_eq_true hw]
            wp_auto
            iunfold nodeStor at Hbs
            icases Hbs with ⟨Hbr, %γs, #Hlock, Hmeta, #Hbridge, %Hsz⟩
            ihave #Hbridge' : antStorBridge (GF := GF) rs.storage γs $$ []
            · rw [Hsto]; iexact Hbridge
            ihave ⟨%k, %old, %Hk, %Hkb, Hpre⟩ : ∃ (k : Nat) (old : List EntryM),
                ⌜∀ e0 ∈ es.head?, k = uint.nat e0.Index'⌝ ∗ ⌜k + es.length ≤ 2 ^ 61⌝ ∗
                (if es = [] then emp else memLog γs k (DFrac.own 1) old ∗ memEnd γs (k + old.length))
                $$ [Happ]
            · by_cases hes : es = []
              · iexists 0, []
                isplitr
                · ipureintro; intro e0 he0; rw [hes] at he0; cases he0
                isplitr
                · ipureintro; rw [hes]; simp
                rw [ite_eq_left hes]
                iempintro
              · ihave Happ : appendRight (GF := GF) rs.storage es $$ [Happ]
                · iunfold readyOut at Happ; iexact Happ
                icases append_pre rs.storage γs es $$ [$Hbridge' $Happ] with ⟨%k, %old, %Hk, Hpre⟩
                iexists k, old
                iframe Hpre
                ipureintro
                refine ⟨Hk, ?_⟩
                obtain ⟨e0, t, hcons⟩ : ∃ e0 t, es = e0 :: t := by
                  cases hh : es with
                  | nil => exact absurd hh hes
                  | cons a b => exact ⟨a, b, rfl⟩
                have hidxs := readyEnts_idx hidx hro.2.2.2.1 k Hk
                have hl : 0 < es.length := by rw [hcons]; exact Nat.succ_pos _
                have hlt : es.length - 1 < es.length := by omega
                have h1 := hidxs _ _ (List.getElem?_eq_getElem hlt)
                have h2 := (hesN _ (List.getElem_mem hlt)).2
                have : uint.nat (es[es.length - 1]).Index' = (uint.Z (es[es.length - 1]).Index').toNat := rfl
                omega
            ihave #HentsZ : entsPtsZ (GF := GF) γs.sz rd.Entries' DFrac.discard es $$ []
            · rw [Hsz, ← hmd]; iexact Hents
            wp_apply wp_Append ms γs k old es rd.Entries' DFrac.discard
              (readyEnts_idx hidx hro.2.2.2.1 k Hk) Hkb $$ [$Hrpkg $Hlock $Hpre $HentsZ]
              as ⟨-, Hpost⟩
            ihave Hrcpt := append_post rs.storage γs es k Hk $$ [$Hbridge' $Hpost]
            wp_bind (If _ _ _)
            iapply (wp_wand (Φ := fun w => iprop(⌜w = executeVal⌝ ∗ rd_ptr ↦ rd ∗ n_ptr ↦ n ∗
                memStorMeta ms γs (HardStateM.mk ps.term ps.vote ps.commit)))) $$ [rd Hnp Hmeta]
            · by_cases hn : HsNew h
              · rw [decide_eq_true hn]
                wp_auto
                ihave #Hho := hsOptC_hsOpt _ _ $$ Hhard
                wp_apply wp_SetHardState ms γs _ rd.HardState' h $$ [$Hrpkg $Hmeta $Hho] as Hmeta
                have hh : h = HardStateM.mk ps.term ps.vote ps.commit := by
                  have := hro.2.1; rw [phsNext_ne _ _ hn] at this; exact this
                rw [← hh]
                iframe
                ipureintro; rfl
              · rw [decide_eq_false hn]
                wp_auto
                obtain ⟨e1, e2, e3⟩ := hold hn
                rw [e1, e2, e3]
                iframe
                ipureintro; rfl
            iintro %w ⟨%Hw, rd, Hnp, Hmeta⟩
            subst Hw
            wp_auto
            iframe rd Hnp
            isplitr
            · ipureintro; rfl
            iframe Hterm Hvote Hcommit Hrcpt
            iunfold nodeStor
            iframe Hbr
            iexists γs
            iframe Hlock Hmeta Hbridge
            ipureintro; exact Hsz
          · rw [decide_eq_false hw]
            wp_auto
            simp only [not_or, Classical.not_not] at hw
            obtain ⟨hn, hes⟩ := hw
            obtain ⟨e1, e2, e3⟩ := hold hn
            iframe rd Hnp
            isplitr
            · ipureintro; rfl
            isplitl [Hterm]
            · rw [e1]; iexact Hterm
            isplitl [Hvote]
            · rw [e2]; iexact Hvote
            isplitl [Hcommit]
            · rw [e3]; iexact Hcommit
            isplitl [Hbs]
            · rw [e1, e2, e3]; iexact Hbs
            iunfold appendReceipt; ileft; ipureintro; exact hes
        iintro %w ⟨%Hw, rd, Hnp, Hterm, Hvote, Hcommit, Hbs, Hrcpt⟩
        subst Hw
        wp_auto
        iframe rd Hnp Hcp Hbp
        isplitr
        · ipureintro; rfl
        iexists b, net₁, null
        isplitl [Hrole]
        · rw [← hr2]; iexact Hrole
        iframe Hterm Hvote Hcommit Hcause Hbs Hrcpt Hv Hl Hlb1
        have hc : ¬ ((({ v₀ with told := b } : AntSim.NodeView).afterReady ps rdD).byE = go!"recv" ∧
            (({ v₀ with told := b } : AntSim.NodeView).afterReady ps rdD).told = false) := by
          rintro ⟨h1, h2⟩
          simp only [AntSim.NodeView.afterReady] at h1 h2
          rw [hbt h1] at h2; cases h2
        unfold causeOwn
        rw [ite_eq_right hc]
        ipureintro; rfl
      · rw [decide_eq_false hrep]
        have hnr : ¬ AntSim.Reported v₀ rdD := fun h' => hrep (hRepIff.2 h')
        simp only [not_or, Classical.not_not] at hrep
        obtain ⟨hn, hes, hrole⟩ := hrep
        obtain ⟨e1, e2, e3⟩ := hold hn
        have hlog : (v₀.afterReady ps rdD).ps.log = v₀.ps.log :=
          hpure.1.2.2.2.2.1 (by rw [hrdD, hes]; rfl)
        imod quiet_upd γ j v₀ (v₀.afterReady ps rdD) net (.silentReady v₀ ps rdD hR hpure.1 hnr) hlog
          $$ [$Hinv $Hlb $Hv $Hl] with ⟨Hv, Hl⟩
        wp_auto
        iframe rd Hnp Hcp Hbp
        isplitr
        · ipureintro; rfl
        iexists v₀.told, net, cl
        isplitl [Hrole]
        · rw [← hr2, hrole]; iexact Hrole
        isplitl [Hterm]
        · rw [e1]; iexact Hterm
        isplitl [Hvote]
        · rw [e2]; iexact Hvote
        isplitl [Hcommit]
        · rw [e3]; iexact Hcommit
        iframe Hcause
        isplitl [Hbs]
        · rw [e1, e2, e3]; iexact Hbs
        isplitr
        · iunfold appendReceipt; ileft; ipureintro; exact hes
        iframe Hlb
        isplitl [Hv]
        · iexact Hv
        isplitl [Hl]
        · iexact Hl
        rw [causeOwn_afterReady]
        iexact Hco
    iintro %w ⟨%Hw, rd, Hnp, Hcp, Hbp, %b, %net₁, %cl', Hrole, Hterm, Hvote, Hcommit, Hcause, Hbs,
      Hrcpt, Hv, Hl, #Hlb1, Hco⟩
    subst Hw
    -- the storage handshake: nothing unpersisted
    imod h_app γ.raft.raftNames rn (AntSim.nodeId j) _ (pAccepted ps) qs' ip' [] rfl
      (fun hh => absurd rfl hh) $$ Hraw Hrcpt with Hraw
    wp_pure
    wp_pure
    wp_pure
    rw [hmd]
    have hs := hsend c_ptr n_ptr by_ptr rd_ptr c n γ j
      ⟨rn, rs, v₀, ps, rd, h, es, ce, rms, ss, steps, W, qs', ip'⟩
      (AntSim.NodeView.afterReady { v₀ with told := b } ps rdD) net₁ q
    unfold github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster.drain.sendE at hs
    iapply hs
    clear hs
    iframe Hpkg Hc Hn Had Htok
    isplitl [Hcp Hnp Hbp rd Hraw Hrole Hterm Hvote Hcommit Hapl Hcause Hbs Hv Hl Hco Hlive Hfree
        Hdur Hdf]
    · unfold drainMid
      iframe Hcp Hnp Hbp rd Hrn Hdf Hce
      isplitl [Hraw]
      · unfold DrainIter.rs₂
        iexact Hraw
      isplitl
      · iunfold loopRest
        iexists ms, si, cl', applied
        simp only [AntSim.NodeView.afterReady]
        iframe Hms Hbs Hrole Hterm Hvote Hcommit Hapl Hcause Hv Hl Hlb1 Hco
        isplitr
        · ipureintro; exact Hsto
        isplitl
        · iunfold nodeRaft
          iexists x, g
          simp only [DrainIter.rs₂]
          iframe Hlive Hfree Hdur Htlb Hbud
          ipureintro; exact Hγ
        ipureintro
        refine ⟨hbyok, ?_⟩
        unfold ViewNormal
        exact ⟨hpure.2.1, HN.2⟩
      ipureintro
      refine ⟨rfl, by rw [hrdD]; rfl, by rw [hrdD]; rfl, rfl, rfl, ?_⟩
      unfold DrainIter.Ok
      exact ⟨hrv, reach_ce hR, hro, hqs', hip', hbyok, Hsn,
        qs_noPreVote hR hnet hnok hpre hqs'⟩
    isplitl [Hmsgs Hmsgs_cap Hmsgs_own]
    · unfold drainMsgs
      iframe Hmsgs Hmsgs_cap Hmsgs_own Hmok
      ipureintro
      simp only [AntSim.NodeView.afterReady, hrdD, readyDOf]
      exact hpure.2.2
    iintro %v₂ %net₂ ⟨Hmid, %Hpend, Had, Htok⟩
    wp_bind (App (App (Val exceptionSeq) (Lam BAnon (App (Val doExecute) _))) (If _ _ _))
    have ha := fun Φ' => hadv c_ptr n_ptr by_ptr rd_ptr c n γ j
      ⟨rn, rs, v₀, ps, rd, h, es, ce, rms, ss, steps, W, qs', ip'⟩ v₂ net₂ Φ' Hpend
    unfold github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster.drain.tailE at ha
    iapply ha
    clear ha
    iframe Hpkg Hc Hn Hmid
    iintro %v' %net' %ps' ⟨Hcp, Hnp, Hbp, Hown, %Hby'⟩
    iapply wp_for_post_do
    wp_auto
    iframe HΦ Hcp Hnp
    isplitl [Hbp]
    · iexact Hbp
    iexists v', net', ps'
    iframe Hown Had Htok
    ipureintro; exact Hby'
  · have hb : b = false := by cases b; rfl; exact absurd rfl Hif
    subst hb
    obtain ⟨hP, hip⟩ := Hb rfl
    wp_if_destruct
    · ihave Hx := drain_exit c γ j n v₀ net ps rn rs ip Hst.1 Hst.2.1 hP hip $$ [$Hinv $Hrn $Hraw $Hrest]
      imod Hx with Hown
      imodintro
      iapply HΦ
      iframe Hown Had Htok
      ipureintro; exact Hby
    · exact absurd rfl ‹¬(#false : val) = #false›
