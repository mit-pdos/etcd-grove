-- The copy for the part `RaftNoAx/` of `Proof/go_etcd_io/raft/v3/BootFixFacts.lean` (etc/copy-part.py; rerun it, do not edit).
/- keepfix (c), 2026-11-27: the facts raft's boot law (`raftBootFix.law`) draws from its premises
(L1 of the decomposition in `~/coordinator-notes/plans/raft-boot-law-brief.md`). -/
module
public import RaftNoAx.Proof.go_etcd_io.raft.v3.InvNodeRule
public import RaftNoAx.Proof.go_etcd_io.raft.v3.Protocol.BootFix
public import RaftNoAx.Spec.go_etcd_io.raft.v3.RaftBootFix
import RaftNoAx.Proof.go_etcd_io.raft.v3.Protocol.Enter
import RaftNoAx.Proof.go_etcd_io.raft.v3.InvNodeChan
import all RaftNoAx.Proof.go_etcd_io.raft.v3.InvNodeRule
import all RaftNoAx.Proof.go_etcd_io.raft.v3.InvNode
import RaftNoAx.Proof.go_etcd_io.raft.v3.InvApi
import RaftNoAx.Proof.go_etcd_io.raft.v3.InvApiDec

@[expose] public section
noncomputable section
namespace Perennial
namespace EtcdGrove
open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics] [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- (L1) **What the boot law's premises give**: the log `F` raft committed through `c ≥ ci` at
the saved raft term `rt` (`committedAtTerm`), its records, certificate and committed prefix, the
term budget at `rt` (N1), and, from the committed log `l` with `l[ci-1] = e`: `F`'s entry at `ci`
is `e`'s term, which is at most `rt` (`commitIn_termLe`; `rt ≠ 0` covers the bootstrap log's
term `1`). -/
private theorem bootCommit_facts (γ : Cluster) (N : Namespace) (Em : CoPset) (hEm : ↑N ⊆ Em)
    (l : List LogEntry) (ci : Nat) (e : LogEntry) (rt c : w64) :
    0 < ci → l[ci - 1]? = some e → ci ≤ uint.nat c → rt ≠ W64 0 →
    isCluster (GF := GF) γ N ∗ isCommittedLogLb γ l ∗ committedAtTerm γ N rt c ⊢ |={Em}=>
      ∃ F : List EntryM,
        ⌜PlogWf base0 F ∧ plogTermAt base0 F (W64 (ci : Int)) = some e.term ∧
          uint.Z e.term ≤ uint.Z rt ∧ uint.Z c ≤ plogLastIndexZ base0 F⌝ ∗
        logRecs (ApiImpl.Cluster.raft γ) base0 F ∗ commitIn (ApiImpl.Cluster.raft γ) F c rt ∗
        isCommitted (ApiImpl.Cluster.raft γ) (F.take (uint.Z c).toNat) ∗
        termLB (ApiImpl.Cluster.bud γ) rt := by
  intro Hci0 Hle Hcic Hrt
  iintro ⟨#Hcluster, #Hlb, #Hcat⟩
  iunfold isCluster at Hcluster
  iunfold ApiImpl.isClusterU at Hcluster
  icases Hcluster with ⟨-, #Hcinv, -⟩
  iunfold committedAtTerm at Hcat
  iunfold ApiImpl.committedAtTerm at Hcat
  icases Hcat with ⟨#Hw, #Htlb, -⟩
  iunfold commitWit at Hw
  icases Hw with ⟨%F, %Hwf, #Hr, #Hc, #Hknown⟩
  iunfold isCommittedLogLb at Hlb
  imod ApiImpl.api_committed_cert γ N Em hEm l $$ Hcinv Hlb with (%Hl | ⟨%P, %HP, #HPc, -⟩)
  · subst Hl; simp at Hle
  obtain ⟨Hpre, -⟩ := HP
  icases commitIn_has _ F c rt $$ Hc with %Hhas
  have Hcr := (word.unsigned_range c)
  have HFlen : uint.Z c ≤ plogLastIndexZ base0 F := by
    obtain ⟨x, Hx⟩ := Option.isSome_iff_exists.mp Hhas
    exact (plogTermAt_some_range _ _ _ _ Hx).2
  have HFl : uint.nat c ≤ F.length := by
    unfold plogLastIndexZ at HFlen; rw [base0_index] at HFlen; word
  icases isCommitted_agree _ P (F.take (uint.Z c).toNat) $$ HPc Hknown with %Hpp
  icases commitIn_termLe _ F c rt Hwf (by intro h; apply Hrt; word) $$ Hr Hc with %Hterm
  imodintro
  -- the entry at `ci`
  have Hlt : ci - 1 < l.length := (List.getElem?_eq_some_iff.mp Hle).1
  obtain ⟨r, hr⟩ := Hpre
  have HlP : l.length ≤ P.length := by
    have := congrArg List.length hr; simp [strip] at this; omega
  have HPe : (strip P)[ci - 1]? = some e := by rw [← hr, List.getElem?_append_left Hlt]; exact Hle
  have HtakeL : (F.take (uint.Z c).toNat).length = uint.nat c := by
    rw [List.length_take]; word
  have HPF : P[ci - 1]? = (F.take (uint.Z c).toNat)[ci - 1]? := by
    rcases Hpp with H | H
    · obtain ⟨s, hs⟩ := H
      rw [← hs, List.getElem?_append_left (by omega)]
    · obtain ⟨s, hs⟩ := H
      rw [← hs, List.getElem?_append_left (by rw [HtakeL]; omega)]
  have HFe : ∃ x : EntryM, F[ci - 1]? = some x ∧ x.Term' = e.term := by
    have HPe' : ∃ x, P[ci - 1]? = some x ∧ LogEntry.ofEntryM x = e := by
      simp only [strip, List.getElem?_map, Option.map_eq_some_iff] at HPe; exact HPe
    obtain ⟨x, hx, hxe⟩ := HPe'
    rw [HPF, List.getElem?_take] at hx
    split at hx
    · exact ⟨x, hx, by rw [← hxe]; rfl⟩
    · cases hx
  obtain ⟨x, hx, hxe⟩ := HFe
  have Hci64 : uint.Z (W64 (ci : Int)) = ci := by word
  have HtAt : plogTermAt base0 F (W64 (ci : Int)) = some e.term := by
    unfold plogTermAt; rw [base0_index, Hci64]
    simp only [show ¬ ((ci : Int) < 0) by omega, show ¬ ((ci : Int) = 0) by omega, ↓reduceIte]
    rw [show ((ci : Int) - 0 - 1).toNat = ci - 1 by omega, hx]
    simp [hxe]
  iexists F
  iframe Hr Hc Hknown Htlb
  ipureintro
  refine ⟨Hwf, HtAt, ?_, HFlen⟩
  exact Hterm _ _ (by rw [Hci64]; word) HtAt

section law
variable [CrashGS GF]

/-- The durable invariants' facts the boot law reads (L7's opening). -/
private theorem durPers_bootPure (γ : RaftNames) (id : w64) (S : RaftState) (E : DurMaps) :
    durPers (GF := GF) γ id S E ⊢ ∃ (kd : Option w64) (fp : List EntryM),
      ⌜VoteHistOkD E.voted S ∧ (∀ k, (E.acks !! k).isSome → uint.Z k.1 ≤ uint.Z S.term) ∧
        (∀ T, (E.camps !! T).isSome → uint.Z T ≤ uint.Z S.term) ∧
        FullOk S.base fp ∧ PlogWf S.base S.ents ∧ uint.Z S.base.index' ≤ uint.Z S.commit⌝ ∗
      logRecs γ S.base S.ents ∗ logRecs γ base0 fp ∗
      ([∗map] k ↦ _u ∈ E.acks, hist γ (fp ++ S.ents) k.1 k.2 (bndD S kd)) ∗
      isCommitted γ ((fp ++ S.ents).take (uint.Z S.commit).toNat) ∗ raftCommitInv γ ∗
      □ (durFrags γ id E -∗ [∗map] k ↦ _u ∈ E.acks, ackInF γ k.1 k.2) := by
  iintro #Hd
  iunfold durPers at Hd
  icases Hd with ⟨%kd, %fp, %Hp, #HrS, -, #Hfp, -, #Hhs, -, -, -, #Hcm, #Hinv, #Hai, -, -⟩
  obtain ⟨Hvh, Hak, Hcp, -, Hfull, Hwf, -, Hbc, -⟩ := Hp
  iexists kd, fp
  iframe HrS Hfp Hhs Hcm Hinv Hai
  ipureintro; exact ⟨Hvh, Hak, Hcp, Hfull, Hwf, Hbc⟩

/-- The boot step's raised term in branch B, `max(rt, S.term + 1)`, within the term budget: `rt`'s
bound (N1), or one tick credit past the member's term (`budget_spend`). -/
private theorem bootTermLB (bud : BudgetNames) (St rt : w64) (E : CoPset) (HE : ↑budgetN ⊆ E) :
    ⊢ inv budgetN (budgetInv (GF := GF) bud) -∗ ⧗ 1 -∗ termLB bud St -∗ termLB bud rt ={E}=∗
      ∃ Tn : w64, ⌜uint.Z St < uint.Z Tn ∧ uint.Z rt ≤ uint.Z Tn ∧
        Tn = (if uint.Z St < uint.Z rt then rt else St + W64 1)⌝ ∗ termLB bud Tn := by
  iintro #Hbud Hrc #HS #Hr
  by_cases HR : uint.Z St < uint.Z rt
  · imodintro; iexists rt; iframe Hr; ipureintro; exact ⟨HR, Int.le_refl _, by rw [if_pos HR]⟩
  · imod budget_spend bud St E HE $$ Hbud [Hrc] HS with ⟨%Hov, #Hl1⟩
    · unfold tickCred; iexact Hrc
    imodintro
    iexists St + W64 1
    iframe Hl1
    ipureintro
    refine ⟨by word, by word, by rw [if_neg HR]⟩

/-- (keepfix (c)) **Raft's boot law, proved** (L7: `bootCommit_facts`, `durPers_raise`,
`durPers_commitRaise`, `durPers_snapBase` with `bootB_hists`, `raft_vacant_close`). -/
theorem raftBootFix_law : raftBootFix.law (GF := GF) := by
  intro γ N id x S l ci e rt c E hN hB hci hl hSc hcc hrt
  iintro Hnc Hrc #Hcl Hvac #Hlb #Hcat Hrs
  imod (entails_wand (bootCommit_facts γ N E hN l ci e rt c hci hl hcc hrt)) $$ [] with
    ⟨%F, %HF, #HrF, #HcF, #HkF, #Htlb⟩
  · iframe Hcl Hlb Hcat
  obtain ⟨HwF, HtF, Hle, HFlen⟩ := HF
  ihave #Hcl2 := Hcl
  iunfold isCluster at Hcl2
  iunfold ApiImpl.isClusterU at Hcl2
  icases Hcl2 with ⟨-, #Hci, -⟩
  iunfold ApiImpl.clusterInv at Hci
  icases Hci with ⟨%HNs, -, -⟩
  have HrN : ↑(raftN (ApiImpl.Cluster.raft γ)) ⊆ E := by
    unfold raftN; rw [HNs]; exact ApiImpl.raftN_sub N hN
  have HsE : (↑(slotN (ApiImpl.Cluster.raft γ) id) : CoPset) ⊆ E :=
    fun p hp => HrN p (slotN_raftN _ id p hp)
  have HbE : (↑budgetN : CoPset) ⊆ E := by unfold raftBudgetN at hB; exact hB
  iunfold raftState at Hrs
  iunfold ApiImpl.raftStateU at Hrs
  icases Hrs with ⟨Hdur, #HtlbS, #Hbud⟩
  iunfold ownDurGhost at Hdur
  icases Hdur with ⟨%Ed, Hsh, #Hdp, #Hslot, #HI1⟩
  iunfold nodeVacantA at Hvac
  iunfold ApiImpl.nodeVacantAU at Hvac
  icases (entails_wand (durPers_bootPure _ id S Ed)) $$ Hdp with
    ⟨%kd, %fp, %Hp, #HrS, #Hfp, #Hhs, #Hcm, #Hinv, #Hai⟩
  obtain ⟨Hvh, Hak, Hcp, Hfull, Hwf, Hbc⟩ := Hp
  have Hci64 : uint.Z (W64 (ci : Int)) = ci := by word
  have hSc' : uint.Z S.commit < (ci : Int) := by have := uint_nat_eq S.commit; omega
  have hcc' : (ci : Int) ≤ uint.Z c := by have := uint_nat_eq c; omega
  have Hfresh : ∀ T, uint.Z S.term < uint.Z T → Ed.camps !! T = none := fun T hT => by
    cases h : Ed.camps !! T with
    | none => rfl
    | some y => exfalso; have := Hcp T (by rw [h]; rfl); omega
  icases commitIn_termLe _ F c rt HwF (by intro h; apply hrt; word) $$ HrF HcF with %HtermF
  have HtF' : plogTermAt base0 F (W64 (ci : Int)) = some e.term := HtF
  -- the durable state after the step
  simp only [raftBootFix, if_pos Hle]
  by_cases HA : plogTermAt S.base S.ents (W64 (ci : Int)) = some e.term
  · -- branch A: the log holds the committed entry at `ci`
    simp only [if_pos HA]
    have HsomeA : (plogTermAt S.base S.ents (W64 (ci : Int))).isSome := by rw [HA]; rfl
    have HagA : plogTermAt base0 F (W64 (ci : Int)) = plogTermAt S.base S.ents (W64 (ci : Int)) := by
      rw [HtF', HA]
    by_cases HR : uint.Z S.term < uint.Z rt
    · simp only [if_pos HR]
      imod raft_vacant_close E _ id x Ed rt HrN (Hfresh rt HR) $$ Hnc Hvac Hsh with
        ⟨Hnc, Hvac, Hsh, #Hcn⟩
      ihave #Hd1 := durPers_raise _ id S Ed rt HR $$ Hdp
      ihave #Hd2 := (entails_wand (durPers_commitRaise _ id { S with term := rt, vote := W64 0 }
        (Ed.add (.close rt)) F (W64 (ci : Int)) c rt (by simp only; rw [Hci64]; omega) HsomeA HwF
        (by rw [Hci64]; omega) (by simp only; omega) HagA)) $$ [Hd1 HrF HcF HkF]
      · iframe Hd1 HrF HcF HkF
      imodintro
      iframe Hnc
      isplitl [Hvac]
      · iunfold nodeVacantA; iunfold ApiImpl.nodeVacantAU; iexact Hvac
      iunfold raftState
      iunfold ApiImpl.raftStateU
      isplitl [Hsh]
      · iunfold ownDurGhost
        iexists Ed.add (.close rt)
        iframe Hsh Hslot
        isplitr; · iExactEq Hd2; rfl
        iExactEq HI1; unfold durI1; rfl
      iframe Htlb Hbud
    · simp only [if_neg HR]
      ihave #Hd2 := (entails_wand (durPers_commitRaise _ id S Ed F (W64 (ci : Int)) c rt
        (by rw [Hci64]; omega) HsomeA HwF (by rw [Hci64]; omega) (by omega) HagA)) $$ [HrF HcF HkF]
      · iframe Hdp HrF HcF HkF
      imodintro
      iframe Hnc
      isplitl [Hvac]
      · iunfold nodeVacantA; iunfold ApiImpl.nodeVacantAU; iexact Hvac
      iunfold raftState
      iunfold ApiImpl.raftStateU
      isplitl [Hsh]
      · iunfold ownDurGhost
        iexists Ed
        iframe Hsh Hslot
        isplitr; · iExactEq Hd2; rfl
        iExactEq HI1; unfold durI1; rfl
      iframe HtlbS Hbud
  · -- branch B: the log replaced by the committed prefix, the term raised past `S.term`
    simp only [if_neg HA]
    -- the raised term and its budget
    imod bootTermLB _ S.term rt E HbE $$ Hbud Hrc HtlbS Htlb with ⟨%Tn, %HTn, #HtlbN⟩
    obtain ⟨HTn1, HTn2, HTn3⟩ := HTn
    rw [← HTn3]
    -- the old maps' fragments (by statement: `durShares_frags`), and the histories (L6b)
    imod durShares_frags E _ id Ed HsE $$ Hsh Hslot with ⟨Hsh, #Hfr⟩
    imod bootB_hists E _ id S Ed kd fp F (W64 (ci : Int)) c rt Tn e.term HrN Hfull Hwf HwF
        (by rw [Hci64]; omega) (by rw [Hci64]; omega) HtF' HA HTn1 HTn2 Hak Hvh
        $$ Hinv HrF HcF HkF Hfp HrS Hcm Hfr Hai Hhs Hsh with ⟨Hsh, %kd', #Hkl', #Hhs'⟩
    imod raft_vacant_close E _ id x Ed Tn HrN (Hfresh Tn HTn1) $$ Hnc Hvac Hsh with
      ⟨Hnc, Hvac, Hsh, #Hcn⟩
    ihave #Hd' := (entails_wand (durPers_snapBase _ id S Ed F (W64 (ci : Int)) c rt Tn e.term kd'
      HTn1 HTn2 (by rw [Hci64]; omega) (by rw [Hci64]; omega) HwF HtF' HtermF)) $$ []
    · iframe Hdp HrF HcF HkF Hkl' Hhs'
    imodintro
    iframe Hnc
    isplitl [Hvac]
    · iunfold nodeVacantA; iunfold ApiImpl.nodeVacantAU; iexact Hvac
    iunfold raftState
    iunfold ApiImpl.raftStateU
    isplitl [Hsh]
    · iunfold ownDurGhost
      iexists Ed.add (.close Tn)
      iframe Hsh Hslot
      isplitr; · iExactEq Hd'; rfl
      unfold durI1
      iintro !> %fp' %Hfp' -
      ipureintro
      intro _ k1 k2 e1 e2 hk _ h2 _ _
      have hl := (List.getElem?_eq_some_iff.mp h2).1
      have hlen : (fp'.length : Int) = uint.Z (W64 (ci : Int)) := Hfp'.1
      simp only [List.append_nil] at hl
      dsimp only
      rw [Hci64] at hlen
      word
    iframe HtlbN Hbud

end law

end EtcdGrove
end Perennial
