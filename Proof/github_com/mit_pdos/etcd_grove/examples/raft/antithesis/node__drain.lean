/-
Lean-first (no Rocq counterpart). #33 parity B1, driver group E: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/node__drain.lean`: B1's mask is
synchronous (`DrainB1`: no `drainAsync`); a loop whose invariant is the loop head (`nodeOwn …
(.loop net₀ xnet₀ r₁ xs₁)`, the `by` kept); `HasReady` false ends it (`drain_exit`, `QuietIn.noReady`);
otherwise a `Ready` (S4's `Cluster.drain` over the parity vocabulary).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__drain
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB1Phases
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB1Report
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB1Bounds
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB1Store
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB1ReadNums
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.RangeRo
public import Proof.ReceiptTactics
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.roleOf
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__reportCause
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__announce
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__emit
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__stateEv
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.withByRole
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__parts
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__saveDisk
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__storeSave
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__sendEv
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__sendMsg
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__reads
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__applyCommitted
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__sent

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [AntStor GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

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

/-- (open: its source is still being designed, likely a raft-side invariant on a queued
`MsgTransferLeader`'s `From`) **A forwarded `MsgTransferLeader` that a `Ready` hands out has a server
as its source**: for any message raft certifies at node `j` (`isRaftMsg`, what `RawNode.Ready`'s
`Henter` gives for each of its messages), a transfer reading of type `transferLeader` comes from one
of the run's nodes. -/
def readyXferSrc.law : Prop :=
  ∀ (γ : AntNames) (j : Fin γ.R.N) (st : MsgSt),
    isRaftMsg (GF := GF) γ.raft.raftNames (AntSim.nodeId j) st ⊢
      ⌜∀ x, xmsgOf st = some x → x.ty = .transferLeader → ∃ i : Fin γ.R.N, x.src = AntSim.nodeId i⌝

instance hsOptRO_persistent (hp : Loc) (oh : Option HardStateM) :
    Persistent (hsOptRO (GF := GF) hp oh) := by
  unfold hsOptRO; infer_instance

theorem entsRO_open_d (s : GoSlice) (es : List EntryM) :
    entsRO (GF := GF) s es ⊢ ∃ ls : List Loc, s ↦*{DFrac.discard} ls ∗ [∗list] l;e ∈ ls;es, entRO l e := by
  unfold entsRO entsPts; exact .rfl

/-- (open: the advance-phase helper's Sim lemma, from `ReadOk`, `StateNums` and a
`MsgReadIndexResp`'s numbers) **The read states a `Ready` hands out have indices within the checker's
bound**: at a node state reached from a view under the mask (`readNums_reach`'s premises), every read
state of its protocol state. -/
def readyReadIdx.law : Prop :=
  ∀ {msk : AntSim.SimMask} (_ : msk ≤ AntSim.mskB1) {R : AntSim.RunCfg} {dec : CCDec}
    {Adm : List EntryM → CCState → Prop} {S : AntCheck.State} {net : List Msg} {xnet : List XMsg}
    {n : Fin R.N} {v : AntSim.NodeView} {r₁ : RState},
    AntSim.InMask msk R net xnet → AntSim.NetOk R S net → AntSim.NodeOk R dec S net n v →
    AntSim.ReachIn msk R dec Adm net xnet n v r₁ → AntSim.StateNums (2 ^ 61) r₁.p →
    ∀ st ∈ r₁.p.rd.states, uint.Z st.Index' < 2 ^ 61

theorem entails_of_eq {P Q : IProp GF} (h : P = Q) : P ⊢ Q := h ▸ .rfl

instance hsNew_dec (h : HardStateM) : Decidable (HsNew h) := by unfold HsNew; infer_instance

/-- `lcpLen` is at most its left list's length. -/
theorem lcpLen_le_left_d : ∀ (l l' : List EntryM), lcpLen l l' ≤ l.length
  | [], _ => by simp [lcpLen]
  | _ :: _, [] => by simp [lcpLen]
  | a :: l, b :: l' => by
    unfold lcpLen
    split
    · have := lcpLen_le_left_d l l'; simp only [List.length_cons]; omega
    · simp

/-- A `Ready`'s entries, the suffix of a log with consecutive indices from the first's. -/
theorem readyEnts_idx_d {l es : List EntryM} (hl : AntSim.LogIdx l)
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

/-- **The disk a reported `Ready`'s write leaves** (`saveW`): the `Ready`'s hard state `H` (the
write's, or the disk's when it writes none) and the log `l` the `Ready`'s entries make of the disk's. -/
theorem saveW_ready (w : AntSim.DurW) (oh : Option HardStateM) (es : List EntryM) (H : HardStateM)
    (l : List EntryM) (hoh : oh.getD (HardStateM.mk w.term w.vote w.commit) = H)
    (hnil : es = [] → l = w.log)
    (hcons : ∀ e0 ∈ es.head?, l = w.log.take (uint.nat e0.Index' - 1) ++ es) :
    saveW w oh es = ⟨H.Term', H.Vote', H.Commit', l⟩ := by
  cases oh with
  | none =>
    simp only [Option.getD_none] at hoh
    subst hoh
    cases es with
    | nil => rw [hnil rfl]; rfl
    | cons e0 t => rw [hcons e0 rfl]; rfl
  | some h0 =>
    simp only [Option.getD_some] at hoh
    subst hoh
    cases es with
    | nil => rw [hnil rfl]; rfl
    | cons e0 t => rw [hcons e0 rfl]; rfl

attribute [-instance] pure_wp_slice_for_range in
theorem node.drain.wp_proof
    (wp_HasReady : RawNode.HasReady.apiSpec (GF := GF) (hG := hG))
    (wp_Ready : RawNode.Ready.apiSpec (GF := GF) (hG := hG))
    (h_wf : rawNode_wf.law (GF := GF) (hG := hG))
    (h_ns : rawNode_noSnap.law (GF := GF) (hG := hG))
    (h_ttc : rawNode_term_tc.law (GF := GF) (hG := hG))
    (h_bp : rnBudget_persistent.law (GF := GF) (hG := hG))
    (h_tlp : rnTermLB_persistent.law (GF := GF) (hG := hG))
    (wp_roleOf : roleOf.spec (GF := GF) (hG := hG))
    (wp_IsEmptyHardState : IsEmptyHardState.spec (GF := GF) (hG := hG))
    (wp_IsEmptySnap : IsEmptySnap.spec (GF := GF) (hG := hG))
    (h_vu : view_update.law (GF := GF) (hG := hG))
    (h_lo : nodeLive_over.law (GF := GF) (hG := hG))
    (h_quiet : antSim_quiet_in.law AntSim.mskB1) (h_mask : runInMask.law AntSim.mskB1)
    (h_recs : rawNode_logRecs.law (GF := GF) (hG := hG))
    (h_lt : rawNode_logTerms.law (GF := GF) (hG := hG))
    (h_rb : rnTermLB_rb.law (GF := GF) (hG := hG))
    (h_app : rawNode_appended.law (GF := GF) (hG := hG))
    (h_pt : rawNode_phsTerm.law (GF := GF) (hG := hG))
    (h_ld : rawNode_leader.law (GF := GF) (hG := hG))
    (h_vote : rawNode_vote.law (GF := GF) (hG := hG))
    (h_cm : rawNode_commit.law (GF := GF) (hG := hG))
    (h_cmd : rawNode_committed.law (GF := GF) (hG := hG))
    (h_inv : rawNode_commitInv.law (GF := GF) (hG := hG))
    (h_ready : antSim_readyA.law)
    (wp_reportCause : node.reportCause.spec (GF := GF) (hG := hG))
    (wp_parts : node.parts.spec (GF := GF) (hG := hG))
    (wp_announce : node.announce.spec (GF := GF) (hG := hG))
    (wp_emit : node.emit.spec (GF := GF) (hG := hG))
    (wp_stateEv : node.stateEv.spec (GF := GF) (hG := hG))
    (wp_withByRole : withByRole.spec (GF := GF) (hG := hG))
    (wp_saveDisk : node.saveDisk.spec (GF := GF) (hG := hG))
    (wp_storeSave : node.storeSave.spec (GF := GF) (hG := hG))
    (h_send : drainSendB1.stmt (GF := GF) (hG := hG))
    (h_xsrc : readyXferSrc.law (GF := GF))
    (h_rsidx : readyReadIdx.law)
    (h_adv : drainAdvanceB1.stmt (GF := GF) (hG := hG)) :
    node.drain.spec (GF := GF) (hG := hG) := by
  intro _ c γ n j v net₀ xnet₀ r₁ xs₁ q
  wp_start as ⟨#Hc, #Hn, Hown, Had, Htok, %Hb1⟩
  iapply wp_fupd
  ihave #Hrpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  ihave #Hc' := Hc
  iunfold antCluster at Hc'
  icases Hc' with ⟨%cfg, %r, %ns, %stop, #Hcfg, %Hcok, %Hmode, #Hr, #Hrec, #Hro, #Hnodes, #Hstop, #Hbc,
    #Hnj, #Hmu, #Hinv, %Hfits, #Hpm, #Hrdm, #Hasi, %Hnames⟩
  iunfold clusterRO at Hro
  icases Hro with ⟨%nsl, %ivl, #Hns, #Hnsl, %HN, #Hmd, #Hiv, #Hivs⟩
  ihave Hmd' := Hmd
  iStructNamed Hmd'
  ihave #Hn' := Hn
  iunfold nodeRO at Hn'
  icases Hn' with ⟨%ch, %d, #Hnc, #Hid, #Hname, #Hin, #Hbag, #Hd, #Hlog⟩
  obtain ⟨hs, hcc, hfw, has⟩ := rMd_flags_d Hmode.2 Hb1
  wp_auto
  rw [Hb1.2.1]
  wp_auto
  irename «by» => Hbp
  irename n => Hnp
  ihave IH : iprop(∃ (v₀ : AntSim.NodeView) (n₀ : List Msg) (x₀ : List XMsg) (r : RState)
      (xs : List XMsg), nodeOwn c γ j n v₀ (.loop n₀ x₀ r xs) ∗ ⌜v₀.byE = v.byE⌝ ∗
      netAdder c γ q ∗ threadTok) $$ [Hown Had Htok]
  · iexists v, net₀, xnet₀, r₁, xs₁; iframe Hown Had Htok; ipureintro; rfl
  wp_for_core
  icases IH with ⟨%v₀, %n₀, %x₀, %r, %xs, Hown, %Hby, Had, Htok⟩
  icases nodeOwn_loop_open c γ j n v₀ n₀ x₀ r xs $$ Hown with ⟨%rn, %rs, %ip, Hrn, Hraw, %Hst, Hrest⟩
  obtain ⟨hrv, hR, hip, hbyok, hN, hk⟩ := Hst
  wp_auto
  wp_apply wp_HasReady γ.R.md hs hcc hfw has γ.raft.raftNames rn (AntSim.nodeId j) rs r [] ip
    $$ [$Hrpkg $Hraw] as %b ⟨Hraw, %Hb⟩
  cases b with
  | false =>
    obtain ⟨hP, hip', hrd⟩ := Hb rfl
    wp_if_destruct
    · exact absurd Hif false_neq_true
    ihave Hx := drain_exit h_vu h_lo h_quiet h_mask c γ j n v₀ n₀ x₀ r rn rs ip Hmode Hb1 hcc hrv hR hbyok hN hk
      hP hip' hrd $$ [$Hinv $Hrn $Hraw $Hrest]
    imod Hx with Hown
    iapply HΦ
    iframe Hown Had Htok
    ipureintro; exact Hby
  | true =>
    wp_if_destruct
    rotate_left
    · exact absurd rfl Hif
    iunfold loopRest at Hrest
    icases Hrest with ⟨%d, %ms, %hsl, %cl, %csl, %role, %applied, %si, #Hd0, Hmem, Hms, Hrole, Hhs,
      Hcause, Hapl, Hconf, Hv, Hl, Hdisk, Hstor, %Hsto, Hnr, %Hpv, #Hhsro, #Hcs, #Hrq, %Hc0, #Hlb, #Hxlb, Hco⟩
    iunfold nodeRaft at Hnr
    icases Hnr with ⟨%x, %g, Hgv, Hfree, Hdur, Htlb, Hbud, %Hγ⟩
    icases h_wf γ.R.md hs hcc hfw has _ _ _ _ _ _ _ $$ Hraw with ⟨%Hwf, Hraw⟩
    icases h_ns γ.R.md hs hcc hfw has _ _ _ _ _ _ _ $$ Hraw with ⟨%Hns, Hraw⟩
    icases h_ttc γ.R.md hs hcc hfw has _ _ _ _ _ _ _ $$ Hraw with ⟨%Httc, Hraw⟩
    icases h_recs γ.R.md hs hcc hfw has _ _ _ _ _ _ _ $$ Hraw with ⟨#Hrrec, Hraw⟩
    icases h_pt γ.R.md hs hcc hfw has _ _ _ _ _ _ _ $$ Hraw with ⟨%Hpt, Hraw⟩
    imod rawNode_stateNums_b1 h_wf h_ns h_recs h_lt h_ttc h_rb h_bp h_tlp γ.R.md hs hcc hfw has γ.raft rn
      (AntSim.nodeId j) rs r [] ip (by rw [Hγ.2.2.2.1]; exact bootLog_length_le _) Hfits
      $$ Hbud Htlb Hraw with ⟨%Hsn, Hbud, Htlb, Hraw⟩
    imod drain_peekRecsB1 h_vu h_lo h_mask γ j v₀ n₀ x₀ Hmode Hb1 $$ [$Hinv $Hlb $Hxlb $Hv $Hl]
      with ⟨%Hpk, #Hvrec, %Hvidx, Hv, Hl⟩
    ihave %Hag := recs_pair γ.raft.raftNames v₀.r.full r.p.log $$ [Hvrec Hrrec]
    · iframe Hvrec Hrrec; ipureintro; exact logIdx_of_wf Hwf.1
    wp_apply wp_Ready γ.R.md hs hcc hfw has γ.raft.raftNames rn (AntSim.nodeId j) x rs r [] ip 1 g
      hrv.2.2.2.1 hrv.2.2.2.2.1 Hγ.1 $$ [$Hrpkg $Hraw $Hgv $Hfree]
      as %rd %ce %es %rms %sts %h %steps %L %ss %W %r' %qs' %ip' Hpost
    icases Hpost with ⟨Hraw, Hlive, Henter, #Hlead, #Hsnapto, #Hsrcs, #Hss, #Hce, #Hcommitted,
      #Hents, Hmsgs, Hmsgs_cap, Hmsgs_own, Hmsgs_cred, %Hmsgs_term, Hsnapz, %Hpsn, #Hrs, #Hrs_ok,
      #Hhard, #Hhsw, Happ, #Hfrz, #Hdk, %Hout⟩
    obtain ⟨hr', hqs', hro, hfirst, hip', hhne, habs, hxok, htr, hxz, hpk, hsts⟩ := Hout γ.R.md rfl
    have hL : L = none := hro.2.2.2.2.2.2.2.2
    subst hL
    -- the role (`rd.SoftState`, else `n.role`)
    have hrole0 : role = roleStr rs.role := by rw [Hpv.2.1, hrv.2.2.2.2.2.2.1]
    wp_bind (If _ _ _)
    iapply (wp_wand (Φ := fun w => iprop(⌜w = executeVal⌝ ∗
        role_ptr ↦ roleStr (roleAfter rs.role ss) ∗ rd_ptr ↦ rd))) $$ [role rd]
    · icases softStateIs_cases _ _ $$ Hss with (%Hsn0 | ⟨%ld, %st, %Hsn1, #Hst⟩)
      · rw [Hsn0.2]
        wp_auto
        rw [Hsn0.1, hrole0]
        iframe
        ipureintro; rfl
      · have hnn : decide (rd.SoftState' = null) = false := decide_eq_false Hsn1.2
        rw [hnn]
        wp_auto
        wp_apply wp_roleOf st $$ [$Hpkg]
        rw [Hsn1.1]
        iframe
        ipureintro; rfl
    iintro %w ⟨%Hw, role, rd⟩
    subst Hw
    wp_auto
    -- the hard state (`rd.HardState` unless empty, else `n.hs`)
    wp_bind (If _ _ _)
    iapply (wp_wand (Φ := fun w => iprop(⌜w = executeVal⌝ ∗
        hs_ptr ↦ (if (h.Term' = W64 0 ∧ h.Vote' = W64 0 ∧ h.Commit' = W64 0) then hsl else rd.HardState') ∗ rd_ptr ↦ rd))) $$ [hs rd]
    · ihave #Hhard' := Hhard
      iunfold hsOptC at Hhard'
      icases Hhard' with (%Hh0 | #Hhro)
      · rw [Hh0.1]
        ihave #Hho : hsOpt (GF := GF) null h $$ []
        · iunfold hsOpt; ileft; ipureintro; exact ⟨rfl, Hh0.2⟩
        wp_apply wp_IsEmptyHardState null h $$ [$Hrpkg $Hho]
        have hn : (h.Term' = W64 0 ∧ h.Vote' = W64 0 ∧ h.Commit' = W64 0) := by rw [Hh0.2]; simp
        rw [if_pos hn]
        have hd : decide (h.Term' = W64 0 ∧ h.Vote' = W64 0 ∧ h.Commit' = W64 0) = true := by
          rw [Hh0.2]; simp
        rw [hd]
        try wp_auto
        iframe
        ipureintro; rfl
      · ihave #Hho := hsOptC_hsOpt _ _ $$ Hhard
        wp_apply wp_IsEmptyHardState rd.HardState' h $$ [$Hrpkg $Hho]
        by_cases hn : HsNew h
        · rw [if_neg hn]
          have hd : decide (h.Term' = W64 0 ∧ h.Vote' = W64 0 ∧ h.Commit' = W64 0) = false :=
            decide_eq_false hn
          rw [hd]
          try wp_auto
          iframe
          ipureintro; rfl
        · rw [if_pos (Classical.not_not.mp hn)]
          have hd : decide (h.Term' = W64 0 ∧ h.Vote' = W64 0 ∧ h.Commit' = W64 0) = true :=
            decide_eq_true (Classical.not_not.mp hn)
          rw [hd]
          try wp_auto
          iframe
          ipureintro; rfl
    iintro %w ⟨%Hw, hs, rd⟩
    subst Hw
    -- `write`: the hard state taken is not `n.hs` (a new one is not the disk's), or entries
    ihave #Hents' := entsROz_entsRO _ _ _ $$ Hents
    ihave %Heslen := entsPts_len _ _ _ $$ Hents'
    ihave %Hhsne : ⌜¬ (h.Term' = W64 0 ∧ h.Vote' = W64 0 ∧ h.Commit' = W64 0) → rd.HardState' ≠ hsl⌝ $$ []
    · iintro %hE %Heq
      ihave #Hhard' := Hhard
      iunfold hsOptC at Hhard'
      icases Hhard' with (%Hh0 | #Hhro)
      · exfalso; apply hE; rw [Hh0.2]; simp
      · ihave #Hhr : hsRO (GF := GF) hsl h $$ []
        · rw [← Heq]; iapply hsROC_hsRO _ _ $$ Hhro
        ihave %Hag := hsRO_agree hsl (HardStateM.mk v₀.dur.term v₀.dur.vote v₀.dur.commit) h $$ [$Hhsro $Hhr]
        exfalso
        apply hhne hE
        rw [hrv.1, Hag]
    -- `write := hs != n.hs || len(rd.Entries) > 0`
    wp_pures
    wp_bind (If _ _ _)
    iapply (wp_wand (Φ := fun w => iprop(⌜w = #(decide (HsNew h ∨ es ≠ []))⌝ ∗
        hs_ptr ↦ (if (h.Term' = W64 0 ∧ h.Vote' = W64 0 ∧ h.Commit' = W64 0) then hsl else rd.HardState') ∗
        rd_ptr ↦ rd ∗ n_ptr ↦ n ∗
        n.[github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node, go!"hs"] ↦ hsl))) $$ [hs rd Hnp Hhs]
    · have hl : es ≠ [] ↔ 0 < es.length := by cases es <;> simp
      have h0 : sint.Z (W64 0) = 0 := by word
      have h2 : sint.nat rd.Entries'.len = (sint.Z rd.Entries'.len).toNat := rfl
      by_cases hE : (h.Term' = W64 0 ∧ h.Vote' = W64 0 ∧ h.Commit' = W64 0)
      · rw [if_pos hE]
        wp_auto
        iframe
        ipureintro
        have hn : ¬ HsNew h := fun hn => hn hE
        have : (0 < sint.Z rd.Entries'.len) ↔ (HsNew h ∨ es ≠ []) := by
          rw [hl]; constructor
          · intro hh; right; omega
          · rintro (hh | hh)
            · exact absurd hh hn
            · omega
        rw [h0]
        simp only [this]
      · rw [if_neg hE]
        have hne := Hhsne hE
        wp_auto
        have hd : decide (rd.HardState' = hsl) = false := decide_eq_false hne
        rw [hd]
        wp_auto
        iframe
        ipureintro
        have hn : HsNew h := hE
        simp [hn]
    iintro %w ⟨%Hw, hs, rd, Hnp, Hhs⟩
    subst Hw
    wp_auto
    -- `early := n.c.mode.Parallel && …`: false (`DrainB1`)
    rw [Hb1.2.2.1]
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
    -- `write || role != n.role`
    wp_bind (If (Val _) _ _)
    iapply (wp_wand (Φ := fun w => iprop(⌜w = #(decide (HsNew h ∨ ¬ es = [] ∨
        roleStr (roleAfter rs.role ss) ≠ role))⌝ ∗
        role_ptr ↦ roleStr (roleAfter rs.role ss) ∗ n_ptr ↦ n ∗
        n.[github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node, go!"role"] ↦ role))) $$ [role Hnp Hrole]
    · by_cases hw : HsNew h ∨ ¬ es = []
      · rw [decide_eq_true hw]
        wp_auto
        iframe
        ipureintro
        have : HsNew h ∨ ¬ es = [] ∨ roleStr (roleAfter rs.role ss) ≠ role := by
          rcases hw with hw | hw
          · exact Or.inl hw
          · exact Or.inr (Or.inl hw)
        rw [decide_eq_true this]
      · rw [decide_eq_false hw]
        wp_auto
        iframe
        ipureintro
        simp only [not_or, Classical.not_not] at hw
        by_cases hc : roleStr (roleAfter rs.role ss) = role
        · simp [hc, hw]
        · simp [hc, hw]
    iintro %w ⟨%Hw, role, Hnp, Hrole⟩
    subst Hw
    -- raft's certificates of the messages, the durable ghost at the `Ready`'s state (`Henter`)
    iapply (wp_ncfupd _ _ (by rfl))
    unfold ncfupd
    iintro Hnc
    imod Henter $$ %⊤ %(1 : Qp) %CoPset.subseteq_top Hnc [$Hdur $Hlive] with
      ⟨Hnc, Hdur, Hlive, Hfree, Hdf, #Hmok⟩
    imodintro
    iframe Hnc
    subst hr'
    -- the report, or a silent `Ready`: the iteration's state after it (`drainMidB1`)
    let I : DrainIterB1 := ⟨rn, rs, v₀, r, rd, ce, es, rms, sts, h, steps, ss, W, qs', ip'⟩
    obtain ⟨S₀, net₀', xnet₀', hn0, hx0, hin0, hnet0, hok0⟩ := Hpk
    ihave %Hxp := xPend_of_msgs (R := γ.R) γ.raft.raftNames γ.R.md (AntSim.nodeId j) r.p rms hxok
      Hnames.1 Hnames.2 $$ Hmok
    have hRO := readyOutP_b1 hin0 hnet0 hok0 (reachIn_b1 hcc hbyok hR hn0 hx0) hrv hip hro hfirst hqs'
      (fun h' => hk ▸ hpk h') Hxp hsts ⟨Hns.1, Hns.2.2⟩ Hwf.1 Hvidx Hag.1
    obtain ⟨rdD, hrdD⟩ : ∃ x, x = readyDOf r (roleAfter rs.role ss) es ce rms qs' sts := ⟨_, rfl⟩
    rw [← hrdD] at hRO
    have hRepIff : (HsNew h ∨ ¬ es = [] ∨ roleStr (roleAfter rs.role ss) ≠ role) ↔
        AntSim.Reported v₀ rdD := by
      rw [hrdD, Hpv.2.1]
      exact reported_iff hrv hro.2.1 hhne hro.1.1 rfl
    have hinm : ∀ S V net xnet, AntSim.AntSim γ.R γ.dec S V net xnet →
        AntSim.InMask AntSim.mskB1 γ.R net xnet := by
      intro S V net xnet hA
      obtain ⟨-, -, -, -, hmd', hdrv⟩ := Hmode.2
      obtain ⟨hb', -, hp', hs', -, hr', hsn', hcc', hfw', has'⟩ := Hb1
      refine inMask_b1_of ?_ ?_ ?_ ?_ ?_ hA
      · rw [hmd']; exact rnLe_scopeMd_b1 _ hfw' has' hsn' hcc'
      · rw [hdrv]; exact hb'
      · rw [hdrv]; exact hp'
      · rw [hdrv]; simp [modeDrv, hs']
      · rw [hdrv]; exact hr'
    have hce := reach_ce hR
    have hri0 := reachIn_b1 hcc hbyok hR hn0 hx0
    have hnorm : AllNormal r.full :=
      (AntSim.shape_reach mskB1_le hin0 hnet0 hok0 hri0 hN.1 (fun m hm => (hN.2 m hm).1)).1
    have hfp : (rAccepted r).fp = [] :=
      (AntSim.reach_fp mskB1_le hin0 hok0 hri0).trans (hok0.facts.snap0 hs).2.1
    imod readyExt_b1 h_wf h_recs h_ld h_vote h_cm h_cmd h_inv γ j γ.R.md hs hcc hfw has rn _ (rAccepted r)
      qs' ip' _ hfp
      ⟨by simp only [readyDurable, RaftState.next, rAccepted, pAccepted, hro.2.1],
       by simp only [readyDurable, RaftState.next, rAccepted, pAccepted, hro.2.1]⟩
      Hγ.2.2.2.1 Hγ.2.2.2.2 $$ [$Hraw $Hdur] with ⟨#Hext, Hraw, Hdur⟩
    wp_bind (If _ _ _)
    iapply (wp_wand (Φ := fun w => iprop(⌜w = executeVal⌝ ∗ rd_ptr ↦ rd ∗ n_ptr ↦ n ∗ by_ptr ↦ v.byE ∗
        nodeMemB1 n ∗ n.[github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node, go!"store"] ↦ ms ∗
        ∃ (v₁ : AntSim.NodeView) (net₁ : List Msg) (xnet₁ : List XMsg) (hsl' cl' : Loc),
          ⌜((AntSim.Reported v₀ rdD ∧ ∃ b : Bool, (v₀.byE = go!"recv" → b = true) ∧
              v₁ = ({ v₀ with told := b } : AntSim.NodeView).afterReady r rdD) ∨
            (¬ AntSim.Reported v₀ rdD ∧ v₁ = v₀.drainOf r rdD)) ∧ n₀ <+: net₁ ∧ x₀ <+: xnet₁⌝ ∗
          n.[github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node, go!"role"] ↦ AntSim.roleS v₁ ∗
          n.[github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node, go!"hs"] ↦ hsl' ∗
          hsRO hsl' (HardStateM.mk v₁.dur.term v₁.dur.vote v₁.dur.commit) ∗
          n.[github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node, go!"cause"] ↦ cl' ∗ causeOwn γ j v₁ cl' ∗ diskOwn d v₁.dur ∗
          nodeStor si ms (votersW γ) (HardStateM.mk v₁.dur.term v₁.dur.vote v₁.dur.commit) ∗
          appendReceipt rs.storage es [] ∗ viewFrag γ j v₁ ∗ nodeLive γ j ∗
          sentLb γ net₁ ∗ xsentLb γ xnet₁))) $$ [rd Hnp Hbp Hmem Hrole Hhs Hcause Hco Hdisk Hstor Happ Hv Hl
        hs write role Hms]
    · by_cases hrep : HsNew h ∨ ¬ es = [] ∨ roleStr (roleAfter rs.role ss) ≠ role
      · rw [decide_eq_true hrep]
        have hrepS := hRepIff.1 hrep
        iunfold nodeMemB1 at Hmem
        icases Hmem with ⟨%mhs, %rhs, Hm1, Hm2, Hm3, Hm4, Hm5, Hm6, Hm7, Hm8, Hm9, Hm10, Hm11, Hm12, Hok⟩
        ihave Hrc := causeOwn_report h_vu h_lo c γ j v₀ n₀ x₀ cl
          (iprop(∃ (b : Bool) (net : List Msg) (xnet : List XMsg),
            ⌜(v₀.byE = go!"recv" → b = true) ∧ n₀ <+: net ∧ x₀ <+: xnet⌝ ∗ sentLb γ net ∗
              xsentLb γ xnet ∗ viewFrag γ j { v₀ with told := b } ∗ nodeLive γ j)) hinm $$ [Hco Hv Hl]
        · iframe Hc Hlb Hxlb Hco Hv Hl
          iintro %b %net %xnet %Hp #Hlb' #Hxlb' Hv Hl
          iexists b, net, xnet
          iframe Hlb' Hxlb' Hv Hl
          ipureintro; exact Hp
        icases Hrc with ⟨%o, Hpc, Hreps⟩
        wp_auto
        wp_apply wp_reportCause c γ n j cl o _ $$ [$Hpkg $Hc $Hn $Hok $Hcause $Hpc $Hreps]
          as ⟨Hok, Hcause, Hq⟩
        icases Hq with ⟨%b, %net₁, %xnet₁, %Hb, #Hlb1, #Hxlb1, Hv, Hl⟩
        -- the `ready` report's facts
        obtain ⟨hmd0, hbt0, hpar0, hspl0, -, -⟩ := hin0.b1 mskB1_le
        have hsd0 := (hok0.sync (by rw [hmd0]) hbt0 hspl0 hpar0).2.1
        have hvt : v₀.ps.term = v₀.dur.term := by rw [hsd0]; rfl
        have hpht : rs.phs.Term' = v₀.dur.term := by rw [hrv.1]
        have htc' : uint.Z r.p.term < 2 ^ 61 := by have := Hsn.2; omega
        have hterm : AntSim.TermRoom ({ v₀ with told := b } : AntSim.NodeView) := by
          show uint.Z v₀.ps.term + 1 < 2 ^ 64
          rw [hvt, ← hpht]; omega
        have hesMem : ∀ e ∈ es, e ∈ r.p.log := by
          intro e he
          obtain ⟨e0, he0⟩ : ∃ e0, es.head? = some e0 := by
            cases es with
            | nil => cases he
            | cons a _ => exact ⟨a, rfl⟩
          have h1 := hro.2.2.2.1 e0 he0
          rw [← h1] at he; exact List.mem_of_mem_drop he
        have hesN : ∀ e ∈ es, uint.Z e.Term' < 2 ^ 61 ∧ uint.Z e.Index' < 2 ^ 61 :=
          fun e he => Hsn.1.2.2.2.2 e (hesMem e he)
        have hstep := readyHstep h_ready j ({ v₀ with told := b } : AntSim.NodeView) r rdD n₀ x₀ hinm has hcc
          hbyok (reach_told_b1 b hR) hRO.1 hrepS Hb.1 hterm
        have hrs : AntSim.roleStr rdD.pre rdD.role = roleStr (roleAfter rs.role ss) := by
          rw [hrdD]; exact readyDOf_roleStr hro.1.1
        have hev : AntSim.evReady (AntSim.nodeId j) ({ v₀ with told := b } : AntSim.NodeView).byE
            (AntSim.roleStr rdD.pre rdD.role) rdD.term rdD.vote rdD.commit rdD.ents rdD.snap =
            AntSim.evReady (AntSim.nodeId j) v.byE (roleStr (roleAfter rs.role ss)) r.p.term r.p.vote
              r.p.commit es := by
          rw [hrs, hrdD]; simp only [readyDOf]; rw [← Hby]
        rw [hev] at hstep
        -- the report (`announce` or `emit`), once its receipts are in hand
        ihave Hmk : ⧗ (es.length + 2) -∗ reports γ.strm [atNode (AntSim.nameOf (AntSim.nodeId j))
            (withByRoleM (stateEvM go!"ready" (HardStateM.mk r.p.term r.p.vote r.p.commit) es) v.byE
              (roleStr (roleAfter rs.role ss)))]
            (iprop(viewFrag γ j (({ v₀ with told := b } : AntSim.NodeView).afterReady r rdD) ∗ nodeLive γ j ∗
              ∃ (net : List Msg) (xnet : List XMsg), sentLb γ net ∗ xsentLb γ xnet ∗
                ⌜net₁ <+: net ∧ (∀ m ∈ ([] : List Msg), m ∈ net) ∧ xnet₁ <+: xnet ∧
                  ∀ x ∈ ([] : List XMsg), x ∈ xnet⌝)) $$ [Hv Hl]
        · iintro Hr
          have hsev := stateEv_ready (AntSim.nodeId j) v.byE (roleStr (roleAfter rs.role ss))
            (HardStateM.mk r.p.term r.p.vote r.p.commit) es (by simpa using htc')
            (by simpa using Hsn.1.2.2.2.1) hesN
          rw [hsev]
          iapply report_upd h_vu h_lo c γ j ({ v₀ with told := b } : AntSim.NodeView)
            (({ v₀ with told := b } : AntSim.NodeView).afterReady r rdD)
            (AntSim.evReady (AntSim.nodeId j) v.byE (roleStr (roleAfter rs.role ss)) r.p.term r.p.vote
              r.p.commit es) net₁ [] xnet₁ []
            (fun G0 G => FactsLe γ.R G0 G ∧ AntSim.RaftLaws G ∧
              AntSim.ReadyFacts G (AntSim.nodeId j) (rAccepted r)) _
            (evReady_numsOk_b1 Hsn.1 htc' hesMem) (evReady_chgOk_b1 _ _ _ _ _ _ _)
            (fun evs S V net xnet G0 G h1 h2 h3 h4 h5 h6 =>
              hstep evs S V net xnet G0 G h1 h2 h3 h4 (Hb.2.1.trans h5) (Hb.2.2.trans h6))
          iframe Hc Hlb1 Hxlb1 Hext Hv Hl
          rw [evReady_weight_b1]
          iframe Hr
          iintro H
          iexact H
        wp_bind (If _ _ _)
        iapply (wp_wand (Φ := fun w => iprop(⌜w = executeVal⌝ ∗ rd_ptr ↦ rd ∗ n_ptr ↦ n ∗ emitOk n ∗
            by_ptr ↦ v.byE ∗ role_ptr ↦ roleStr (roleAfter rs.role ss) ∗
            n.[github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node, go!"store"] ↦ ms ∗
            ∃ (hsl' : Loc) (net : List Msg) (xnet : List XMsg),
              n.[github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node, go!"hs"] ↦ hsl' ∗
              hsRO hsl' (HardStateM.mk r.p.term r.p.vote r.p.commit) ∗
              diskOwn d (AntSim.durOf (AntSim.accepted r)) ∗
              nodeStor si ms (votersW γ) (HardStateM.mk r.p.term r.p.vote r.p.commit) ∗
              appendReceipt rs.storage es [] ∗
              viewFrag γ j (({ v₀ with told := b } : AntSim.NodeView).afterReady r rdD) ∗ nodeLive γ j ∗
              sentLb γ net ∗ xsentLb γ xnet ∗ ⌜net₁ <+: net ∧ xnet₁ <+: xnet⌝)))
          $$ [rd Hnp Hok Hbp Hhs Hdisk Hstor Happ Hmk hs role Hms]
        · -- the hard state the branch writes (`hs`, the part's `after`) is the `Ready`'s, `H`
          have hH : phsNext rs.phs h = HardStateM.mk r.p.term r.p.vote r.p.commit := hro.2.1
          have hmd' : γ.raft.raftNames.maxData.isSome = false := by rw [Hγ.2.2.1]; rfl
          have hesNorm : AllNormal es := fun e he => hnorm e (by rw [hRO.2.1]; exact hesMem e he)
          ihave #HhsH : hsRO (GF := GF) (if (h.Term' = W64 0 ∧ h.Vote' = W64 0 ∧ h.Commit' = W64 0) then hsl
              else rd.HardState') (HardStateM.mk r.p.term r.p.vote r.p.commit) $$ []
          · by_cases hE : (h.Term' = W64 0 ∧ h.Vote' = W64 0 ∧ h.Commit' = W64 0)
            · rw [if_pos hE, ← hH, phsNext_empty _ _ hE, hrv.1]; iexact Hhsro
            · rw [if_neg hE, ← hH, phsNext_ne _ _ hE]
              ihave #Hhard' := Hhard
              iunfold hsOptC at Hhard'
              icases Hhard' with (%Hh0 | #Hhro)
              · exfalso; apply hE; rw [Hh0.2]; simp
              · iapply hsROC_hsRO _ _ $$ Hhro
          by_cases hw : HsNew h ∨ ¬ es = []
          · rw [decide_eq_true hw]
            -- the write: one part (`Split = 0`), its `hs` `nil` unless the hard state is new
            ihave ⟨%oh, %Hoh1, %Hoh2, #Hoh⟩ : ∃ oh : Option HardStateM,
                ⌜oh.getD (HardStateM.mk v₀.dur.term v₀.dur.vote v₀.dur.commit) =
                  HardStateM.mk r.p.term r.p.vote r.p.commit⌝ ∗
                ⌜saveW v₀.dur oh es = AntSim.durOf (AntSim.accepted r)⌝ ∗
                hsOptRO (GF := GF) (if (if (h.Term' = W64 0 ∧ h.Vote' = W64 0 ∧ h.Commit' = W64 0) then hsl
                  else rd.HardState') = hsl then null else
                  (if (h.Term' = W64 0 ∧ h.Vote' = W64 0 ∧ h.Commit' = W64 0) then hsl else rd.HardState')) oh
                $$ []
            · have hsv : ∀ oh : Option HardStateM, oh.getD (HardStateM.mk v₀.dur.term v₀.dur.vote v₀.dur.commit) =
                  HardStateM.mk r.p.term r.p.vote r.p.commit →
                  saveW v₀.dur oh es = AntSim.durOf (AntSim.accepted r) := fun oh hoh =>
                saveW_ready v₀.dur oh es _ r.full hoh
                  (fun hes => hRO.1.2.2.2.2.2.1 (by rw [hrdD]; rfl) (by rw [hrdD]; exact hes))
                  (fun e0 he => by
                    have h := (hRO.1.2.2.2.2.2.2.1 e0 (by rw [hrdD]; exact he)).1
                    rw [hrdD] at h; exact h)
              by_cases hE : (h.Term' = W64 0 ∧ h.Vote' = W64 0 ∧ h.Commit' = W64 0)
              · have h1 : (none : Option HardStateM).getD (HardStateM.mk v₀.dur.term v₀.dur.vote v₀.dur.commit) =
                    HardStateM.mk r.p.term r.p.vote r.p.commit := by
                  rw [Option.getD_none, ← hH, phsNext_empty _ _ hE, hrv.1]
                iexists none
                rw [if_pos hE, if_pos rfl]
                isplitr
                · ipureintro; exact h1
                isplitr
                · ipureintro; exact hsv none h1
                iunfold hsOptRO; ileft; ipureintro; exact ⟨rfl, rfl⟩
              · iexists some (HardStateM.mk r.p.term r.p.vote r.p.commit)
                rw [if_neg hE, if_neg (Hhsne hE)]
                ihave %Hnn : ⌜rd.HardState' ≠ null⌝ $$ [HhsH]
                · iunfold hsRO at HhsH
                  icases HhsH with ⟨%pt, %pv, %pc, %uf, %Hnn, -⟩
                  ipureintro; exact Hnn
                isplitr
                · ipureintro; rfl
                isplitr
                · ipureintro; exact hsv _ rfl
                iunfold hsOptRO; iright; iexists _; iframe HhsH; ipureintro; exact ⟨Hnn, rfl⟩
            have hsaveOk : SaveOk v₀.dur es := by
              intro e he
              have h1 := hfirst e he
              have h2 : ip ≤ v₀.dur.log.length := by
                rw [hip, hRO.2.2.2, hRO.2.2.1]; exact lcpLen_le_left_d _ _
              omega
            obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hLI, -⟩ := hRO.1
            rw [hRO.2.1] at hLI
            iunfold nodeStor at Hstor
            icases Hstor with ⟨Hbr, %γs, #Hlock, Hmeta, #Hbridge, %Hsz⟩
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
                icases append_preB1 rs.storage γs es $$ [$Hbridge' $Happ] with ⟨%k, %old, %Hk, Hpre⟩
                iexists k, old
                iframe Hpre
                ipureintro
                refine ⟨Hk, ?_⟩
                have hlt : es.length - 1 < es.length := by
                  cases es with
                  | nil => exact absurd rfl hes
                  | cons a b => simp
                have h1 := readyEnts_idx_d hLI hro.2.2.2.1 k Hk _ _ (List.getElem?_eq_getElem hlt)
                have h2 := (hesN _ (List.getElem_mem hlt)).2
                have : uint.nat (es[es.length - 1]).Index' = (uint.Z (es[es.length - 1]).Index').toNat := rfl
                omega
            ihave #HentsZ : entsPtsZ (GF := GF) γs.sz rd.Entries' DFrac.discard es $$ []
            · rw [Hsz, ← hmd']; iexact Hents
            ihave ⟨%els, #Hsl, #Hbig⟩ : ∃ ls : List Loc, rd.Entries' ↦*{DFrac.discard} ls ∗
                [∗list] l;e ∈ ls;es, entRO (GF := GF) l e $$ [Hents']
            · iapply entsRO_open_d; iexact Hents'
            wp_auto
            wp_apply wp_parts c γ n j _ hsl rd.Entries' $$ [$Hpkg $Hc $Hn $Hhs] as %out ⟨Hhs, Hout⟩
            · ipureintro; exact Hb1.2.2.2.1
            wp_apply (wp_slice_range_ro (V := H.part) _ out _ (DFrac.own 1) _
              (fun i => iprop(∃ x : H.part, p_ptr ↦ x ∗ n_ptr ↦ n ∗ by_ptr ↦ v.byE ∗
                role_ptr ↦ roleStr (roleAfter rs.role ss) ∗ emitOk n ∗
                n.[github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node, go!"store"] ↦ ms ∗
                if i = 0 then
                  n.[github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node, go!"hs"] ↦ hsl ∗
                  diskOwn d v₀.dur ∗ memStorMeta ms γs (HardStateM.mk v₀.dur.term v₀.dur.vote v₀.dur.commit) ∗
                  (if es = [] then emp else memLog γs k (DFrac.own 1) old ∗ memEnd γs (k + old.length)) ∗
                  (⧗ (es.length + 2) -∗ reports γ.strm [atNode (AntSim.nameOf (AntSim.nodeId j))
                    (withByRoleM (stateEvM go!"ready" (HardStateM.mk r.p.term r.p.vote r.p.commit) es) v.byE
                      (roleStr (roleAfter rs.role ss)))]
                    (iprop(viewFrag γ j (({ v₀ with told := b } : AntSim.NodeView).afterReady r rdD) ∗ nodeLive γ j ∗
                      ∃ (net : List Msg) (xnet : List XMsg), sentLb γ net ∗ xsentLb γ xnet ∗
                        ⌜net₁ <+: net ∧ (∀ m ∈ ([] : List Msg), m ∈ net) ∧ xnet₁ <+: xnet ∧
                          ∀ x ∈ ([] : List XMsg), x ∈ xnet⌝)))
                else
                  n.[github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node, go!"hs"] ↦
                    (if (h.Term' = W64 0 ∧ h.Vote' = W64 0 ∧ h.Commit' = W64 0) then hsl else rd.HardState') ∗
                  diskOwn d (AntSim.durOf (AntSim.accepted r)) ∗
                  memStorMeta ms γs (HardStateM.mk r.p.term r.p.vote r.p.commit) ∗
                  (if es = [] then emp else memLog γs k (DFrac.own 1) es ∗ memEnd γs (k + es.length)) ∗
                  viewFrag γ j (({ v₀ with told := b } : AntSim.NodeView).afterReady r rdD) ∗ nodeLive γ j ∗
                  ∃ (net : List Msg) (xnet : List XMsg), sentLb γ net ∗ xsentLb γ xnet ∗
                    ⌜net₁ <+: net ∧ (∀ m ∈ ([] : List Msg), m ∈ net) ∧ xnet₁ <+: xnet ∧
                      ∀ x ∈ ([] : List XMsg), x ∈ xnet⌝)))
              $$ Hout [p Hnp Hbp role Hok Hms Hhs Hdisk Hmeta Hpre Hmk]
            · iexists _
              simp only [eq_self_iff_true, ↓reduceIte]
              iframe
            · imodintro
              iintro %i %x %hx HP Hs
              have hi0 : i = 0 := by
                have := (List.getElem?_eq_some_iff.1 hx).1; simp at this; omega
              subst hi0
              simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
              subst hx
              simp only [Nat.zero_add, Nat.one_ne_zero, eq_self_iff_true, ↓reduceIte]
              icases HP with ⟨%x0, p, Hnp, Hbp, role, Hok, Hms, Hhs, Hdisk, Hmeta, Hpre, Hmk⟩
              wp_take_receipt as Hr1
              wp_apply +noauto wp_stateEv c γ n j go!"ready" _ (HardStateM.mk r.p.term r.p.vote r.p.commit) rd.Entries'
                DFrac.discard els es hesNorm $$ [$Hpkg $Hc $Hn $HhsH $Hsl $Hbig] as %pe ⟨-, -, Hev, Hr3⟩
              wp_take_receipt as Hr2
              wp_apply wp_withByRole pe _ v.byE (roleStr (roleAfter rs.role ss)) $$ [$Hpkg $Hev] as Hev
              ihave Hrep := Hmk $$ [Hr1 Hr2 Hr3]
              · iapply (receipt_add (GF := GF) (es.length + 1) 1).2
                iframe Hr2
                iapply (receipt_add (GF := GF) es.length 1).2
                iframe Hr3 Hr1
              wp_apply wp_announce c γ n j pe _ _ $$ [$Hpkg $Hc $Hn $Hok $Hev $Hrep] as ⟨Hok, Hrep⟩
              wp_apply wp_saveDisk c γ n j d v₀.dur _ oh rd.Entries' els es hsaveOk
                $$ [$Hpkg $Hc $Hn $Hd0 $Hok $Hdisk $Hoh $Hsl $Hbig] as ⟨Hok, Hdisk⟩
              wp_apply wp_storeSave n ms γs (HardStateM.mk v₀.dur.term v₀.dur.vote v₀.dur.commit) _ oh k old es
                rd.Entries' DFrac.discard (readyEnts_idx_d hLI hro.2.2.2.1 k Hk) Hkb
                $$ [$Hpkg $Hms $Hlock $Hmeta $Hoh $Hpre $HentsZ] as ⟨Hms, Hmeta, -, Hpost⟩
              iframe
              isplitr
              · ipureintro; rfl
              rw [Hoh1, Hoh2]
              iframe
            · iintro HP Hs
              simp only [List.length_singleton, Nat.one_ne_zero, ↓reduceIte]
              icases HP with ⟨%x0, p, Hnp, Hbp, role, Hok, Hms, Hhs, Hdisk, Hmeta, Hpost, Hv, Hl, %net₂, %xnet₂,
                #Hlb2, #Hxlb2, %Hp2⟩
              ihave Hrcpt := append_postB1 rs.storage γs es k Hk $$ [$Hbridge' $Hpost]
              iframe
              iexists net₂, xnet₂
              iframe
              iframe HhsH
              isplitl [Hbr Hmeta]
              · iunfold nodeStor
                iframe Hbr
                iexists γs
                iframe Hlock Hmeta Hbridge
                ipureintro; exact Hsz
              iframe Hlb2 Hxlb2
              ipureintro; exact ⟨Hp2.1, Hp2.2.2.1⟩
          · rw [decide_eq_false hw]
            simp only [not_or, Classical.not_not] at hw
            obtain ⟨hn, hes⟩ := hw
            have hE : (h.Term' = W64 0 ∧ h.Vote' = W64 0 ∧ h.Commit' = W64 0) := by
              exact Classical.byContradiction fun hc => hn hc
            have h1 : HardStateM.mk r.p.term r.p.vote r.p.commit =
                HardStateM.mk v₀.dur.term v₀.dur.vote v₀.dur.commit := by
              rw [← hH, phsNext_empty _ _ hE, hrv.1]
            have hdur0 : AntSim.durOf (AntSim.accepted r) = v₀.dur := by
              have h2 : r.full = v₀.dur.log :=
                hRO.1.2.2.2.2.2.1 (by rw [hrdD]; rfl) (by rw [hrdD]; exact hes)
              injection h1 with e1 e2 e3
              show (⟨r.p.term, r.p.vote, r.p.commit, r.full⟩ : AntSim.DurW) =
                ⟨v₀.dur.term, v₀.dur.vote, v₀.dur.commit, v₀.dur.log⟩
              rw [e1, e2, e3, h2]
            rw [if_pos hE]
            subst hes
            ihave Hnil : (slice.nil ↦*{DFrac.own 1} ([] : List Loc) : IProp GF) $$ []
            · iapply ownSlice_nil
            ihave Hbnil : ([∗list] p;e ∈ ([] : List Loc);([] : List EntryM), entRO (GF := GF) p e) $$ []
            · iapply BigSepL2.bigSepL2_nil.2; iempintro
            wp_take_receipt as Hr1
            wp_apply +noauto wp_stateEv c γ n j go!"ready" hsl (HardStateM.mk r.p.term r.p.vote r.p.commit) slice.nil
              (DFrac.own 1) [] [] (fun e he => nomatch he) $$ [$Hpkg $Hc $Hn $HhsH $Hnil $Hbnil]
              as %pe ⟨-, -, Hev, -⟩
            wp_take_receipt as Hr2
            wp_apply wp_withByRole pe _ v.byE (roleStr (roleAfter rs.role ss)) $$ [$Hpkg $Hev] as Hev
            ihave Hrep := Hmk $$ [Hr1 Hr2]
            · iapply (receipt_add (GF := GF) 1 1).2
              iframe Hr1 Hr2
            wp_apply wp_emit c γ n j pe _ _ $$ [$Hpkg $Hc $Hn $Hok $Hev $Hrep] as ⟨Hok, Hrep⟩
            icases Hrep with ⟨Hv, Hl, %net₂, %xnet₂, #Hlb2, #Hxlb2, %Hp2⟩
            iframe
            isplitr
            · ipureintro; rfl
            iexists net₂, xnet₂
            rw [hdur0, h1]
            iframe
            iframe Hhsro
            isplitr
            · iunfold appendReceipt; ileft; ipureintro; rfl
            iframe Hlb2 Hxlb2
            ipureintro; exact ⟨Hp2.1, Hp2.2.2.1⟩
        iintro %w ⟨%Hw, rd, Hnp, Hok, Hbp, role, Hms, %hsl', %net₂, %xnet₂, Hhs, #HhsR, Hdisk, Hstor, Hrcpt, Hv, Hl, #Hlb2,
          #Hxlb2, %Hp2⟩
        subst Hw
        wp_auto
        iframe rd Hnp Hbp Hms
        isplitr
        · ipureintro; rfl
        isplitl [Hm1 Hm2 Hm3 Hm4 Hm5 Hm6 Hm7 Hm8 Hm9 Hm10 Hm11 Hm12 Hok]
        · iunfold nodeMemB1
          iexists mhs, rhs
          iframe
        iexists (({ v₀ with told := b } : AntSim.NodeView).afterReady r rdD), net₂, xnet₂, hsl', null
        isplitr
        · ipureintro
          exact ⟨Or.inl ⟨hrepS, b, Hb.1, rfl⟩, Hb.2.1.trans Hp2.1, Hb.2.2.trans Hp2.2⟩
        isplitl [Hrole]
        · have hro2 : AntSim.roleS (({ v₀ with told := b } : AntSim.NodeView).afterReady r rdD) =
              roleStr (roleAfter rs.role ss) := by
            rw [hrdD]; exact roleS_drainOf (v := { v₀ with told := b }) (qs := qs') (sts := sts) hro
          rw [hro2]; iexact Hrole
        rw [show (({ v₀ with told := b } : AntSim.NodeView).afterReady r rdD).dur =
          AntSim.durOf (AntSim.accepted r) from rfl]
        rw [show HardStateM.mk (AntSim.durOf (AntSim.accepted r)).term (AntSim.durOf (AntSim.accepted r)).vote
          (AntSim.durOf (AntSim.accepted r)).commit = HardStateM.mk r.p.term r.p.vote r.p.commit from rfl]
        iframe Hhs HhsR Hcause Hdisk Hstor Hrcpt Hv Hl Hlb2 Hxlb2
        iunfold causeOwn
        have hnc : ¬ ((({ v₀ with told := b } : AntSim.NodeView).afterReady r rdD).byE = go!"recv" ∧
            (({ v₀ with told := b } : AntSim.NodeView).afterReady r rdD).told = false) := by
          rintro ⟨h1, h2⟩
          have := Hb.1 h1
          simp only [AntSim.NodeView.afterReady, AntSim.NodeView.drainOf] at h2
          rw [this] at h2; cases h2
        rw [if_neg hnc]
        iunfold pendingCause
        ileft
        ipureintro; exact ⟨rfl, rfl⟩
      · rw [decide_eq_false hrep]
        have hnr : ¬ AntSim.Reported v₀ rdD := fun h' => hrep (hRepIff.2 h')
        simp only [not_or, Classical.not_not] at hrep
        obtain ⟨hn, hes, hrl⟩ := hrep
        have hfe : (v₀.drainOf r rdD).r.full = v₀.r.full := by
          show (AntSim.accepted r).full = v₀.r.full
          rw [show (AntSim.accepted r).full = r.full from rfl,
            hRO.1.2.2.2.2.2.1 (by rw [hrdD]; rfl) (by rw [hrdD]; exact hes), hRO.2.2.2]
        imod view_quiet h_vu h_lo AntSim.mskB1 h_quiet h_mask γ j v₀ (v₀.drainOf r rdD) n₀ x₀ Hmode Hb1
          (Adm := AdmFold γ.dec γ.R.c0) (P := True)
          (fun S V net xnet hn' hx' _ _ _ =>
            ⟨.silentReady v₀ r rdD (reachIn_b1 hcc hbyok hR hn' hx') hRO.1 hnr, hfe, trivial⟩)
          $$ [$Hinv $Hlb $Hxlb $Hv $Hl] with ⟨Hv, Hl, -⟩
        wp_auto
        iframe rd Hnp Hbp Hmem Hms
        isplitr
        · ipureintro; rfl
        iexists v₀.drainOf r rdD, n₀, x₀, hsl, cl
        isplitr
        · ipureintro; exact ⟨Or.inr ⟨hnr, rfl⟩, List.prefix_refl _, List.prefix_refl _⟩
        isplitl [Hrole]
        · rw [hrdD, roleS_drainOf hro, hrl]; iexact Hrole
        rw [show (v₀.drainOf r rdD).dur = v₀.dur from rfl,
          show causeOwn (GF := GF) γ j (v₀.drainOf r rdD) cl = causeOwn γ j v₀ cl from rfl]
        iframe Hhs Hhsro Hcause Hco Hdisk Hstor Hv Hl Hlb Hxlb
        iunfold appendReceipt; ileft; ipureintro; exact hes
    iintro %w ⟨%Hw, rd, Hnp, Hbp, Hmem, Hms, %v₁, %net₁, %xnet₁, %hsl', %cl', %Hv1, Hrole, Hhs, #Hhsro', Hcause,
      Hco, Hdisk, Hstor, Hrcpt, Hv, Hl, #Hlb1, #Hxlb1⟩
    subst Hw
    imod h_app γ.R.md hs hcc hfw has γ.raft.raftNames rn (AntSim.nodeId j) _ (rAccepted r) qs' ip' [] rfl
      (fun hh => absurd rfl hh) $$ Hraw Hrcpt with Hraw
    have hview : RsView { I.rs₂ with steps := [] } v₁ ∧ ViewNormal v₁ ∧ v₁.r = AntSim.accepted r ∧
        v₁.qs = qs' ∧ v₁.ce = ce ∧ v₁.rpend = sts ∧ v₁.byE = v₀.byE ∧
        v₁.pend = rms.filterMap (fun m => absMsgOf m.st) ∧ v₁.xpend = rms.filterMap (fun m => xmsgOf m.st) ∧
        v₁.delivered = v₀.delivered ∧ v₁.alive = v₀.alive ∧ v₁.conf = v₀.conf ∧ v₁.reads = v₀.reads := by
      rcases Hv1.1 with ⟨-, b, -, rfl⟩ | ⟨hnr, rfl⟩
      · subst hrdD
        exact ⟨(drainView_rep (I := I) b hrv hce hro hRO.2.1 hN hnorm).1,
          (drainView_rep (I := I) b hrv hce hro hRO.2.1 hN hnorm).2,
          rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · have hnr' : ¬ (HsNew h ∨ ¬ es = [] ∨ roleStr (roleAfter rs.role ss) ≠ role) :=
          fun h' => hnr (hRepIff.1 h')
        simp only [not_or, Classical.not_not] at hnr'
        obtain ⟨hn, hes, -⟩ := hnr'
        have hfv : r.full = v₀.r.full := by
          rw [hRO.1.2.2.2.2.2.1 (by rw [hrdD]; rfl) (by rw [hrdD]; exact hes), hRO.2.2.2]
        subst hrdD
        exact ⟨(drainView_silent (I := I) hrv hce hro hfv hN hn hes).1,
          (drainView_silent (I := I) hrv hce hro hfv hN hn hes).2,
          rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    obtain ⟨hv1, hvn1, hvr1, hvq1, hvce1, hvrp1, hvby1, hvp1, hvx1, hvd1, hval1, hvc1, hvrd1⟩ := hview
    have hIok : I.Ok γ j :=
      ⟨hrv, hk, hbyok, hqs', hro, hip', habs, fun q hq x hx => ⟨hxok q hq x hx, hxz q hq x hx⟩, htr, hsts,
        Hsn.2, Hsn.1, by
          show ∀ st ∈ sts, _
          rw [hsts]
          exact h_rsidx (R := γ.R) (dec := γ.dec) mskB1_le hin0 hnet0 hok0 hri0 Hsn.1⟩
    have hmd : γ.raft.raftNames.maxData.isSome = false := by rw [Hγ.2.2.1]; rfl
    ihave Hmsgs_own := entails_of_eq (Q := iprop([∗list] q ∈ rms, msgOwnZ (GF := GF) false q.loc
      (readyDq q.st) q.st)) (by rw [hmd]) $$ Hmsgs_own
    ihave %Hxs := ((BigSepL.bigSepL_mono (l := rms) (Φ := fun _ (q : QMsg) => isRaftMsg (GF := GF) γ.raft.raftNames
      (AntSim.nodeId j) q.st) (Ψ := fun _ (q : QMsg) => iprop(⌜∀ x, xmsgOf q.st = some x →
        x.ty = .transferLeader → ∃ i : Fin γ.R.N, x.src = AntSim.nodeId i⌝)) fun _ => h_xsrc γ j _).trans BigSepL.bigSepL_pure_intro) $$ Hmok
    ihave Hmsgs : drainMsgsB1 (GF := GF) γ j I $$ [Hmsgs Hmsgs_cap Hmsgs_own]
    · iunfold drainMsgsB1
      iframe Hmsgs Hmsgs_cap Hmsgs_own Hmok
      ipureintro
      intro q hq
      refine ⟨Hmsgs_term q hq, fun m hm => ?_, fun x hx ht => ?_⟩
      · have hall := AntSim.readyMsgNums mskB1_le hin0 hnet0 hok0 hri0 hRO.1 Hsn.1
          (causeNums_reach hnet0 hok0 hN) (AntSim.readNums_reach mskB1_le hin0 hnet0 hok0 hri0 Hsn.1)
        refine hall m (List.mem_append_left _ ?_)
        rw [hrdD]; exact List.mem_filterMap.2 ⟨q, hq, hm⟩
      · obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hq
        exact Hxs k q hk x hx ht
    ihave Hmid : drainMidB1 n_ptr by_ptr rd_ptr n γ j I v₁ net₁ xnet₁ $$ [Hnp Hbp rd Hrn Hraw Hmem Hms
        Hrole Hhs Hcause Hapl Hconf Hv Hl Hdisk Hstor Hco Hlive Hfree Hdur Htlb Hbud Hdf]
    · iunfold drainMidB1
      iframe Hnp rd Hrn Hdf Hce Hrs Hrs_ok
      isplitl [Hbp]
      · first | rw [Hby] | rw [show I.v.byE = v.byE from Hby]
        iexact Hbp
      isplitl [Hraw]
      · unfold DrainIterB1.rs₂
        iexact Hraw
      isplitl
      · iunfold loopRest
        iexists d, ms, hsl', cl', csl, AntSim.roleS v₁, applied, si
        iframe Hd0 Hmem Hms Hrole Hhs Hcause Hapl Hconf Hv Hl Hdisk Hstor Hhsro' Hcs Hlb1 Hxlb1 Hco
        isplitr
        · ipureintro; exact Hsto
        isplitl [Hlive Hfree Hdur Htlb Hbud]
        · iunfold nodeRaft
          unfold DrainIterB1.rs₂
          iexists x, g
          iframe Hlive Hfree Hdur Htlb Hbud
          ipureintro; exact Hγ
        isplitr
        · ipureintro; exact ⟨by rw [hval1]; exact Hpv.1, rfl, by rw [hvd1]; exact Hpv.2.2⟩
        isplitr
        · rw [show readsOwn (GF := GF) γ v₁ = readsOwn γ v₀ by unfold readsOwn; rw [hvrd1]]
          iexact Hrq
        ipureintro; rw [hvc1]; exact Hc0
      ipureintro
      exact ⟨hvr1, hvq1, hvce1, hvrp1, hvby1, hv1, hvn1, hIok⟩
    have Hpx : v₁.pend = rms.filterMap (fun m => absMsgOf m.st) ∧
        v₁.xpend = rms.filterMap (fun m => xmsgOf m.st) := ⟨hvp1, hvx1⟩
    wp_pure
    wp_pure
    wp_pure
    have hsd := h_send n_ptr by_ptr rd_ptr early_ptr c n γ j I v₁ net₁ xnet₁ q
    unfold github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.drain.sendE at hsd
    iapply hsd _ _ Hpx.1 Hpx.2
    clear hsd
    iframe Hpkg Hc Hn Hmid Hmsgs early Had Htok
    isplitr
    · ipureintro; exact Hb1
    iintro %v₂ %net₂ %xnet₂ ⟨Hmid, %Hpend, Hsent, early, Had, Htok⟩
    have ha := fun Φ' => h_adv n_ptr by_ptr rd_ptr c n γ j I v₂ net₂ xnet₂ Φ' Hpend.1 Hpend.2
    unfold github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.drain.tailE at ha
    iapply ha
    clear ha
    iframe Hpkg Hc Hn Hmid Hsent
    isplitr
    · ipureintro; exact Hb1
    iintro %v' %net' %xnet' %r'' ⟨Hnp, Hbp, Hown, %Hby'⟩
    iapply wp_for_post_do
    wp_auto
    iframe HΦ Hnp
    isplitl [Hbp]
    · rw [Hby]; iexact Hbp
    iexists v', net', xnet', r'', []
    iframe Hown Had Htok
    ipureintro; rw [Hby', Hby]

end proof

end AntHarness
end EtcdGrove
end Perennial
