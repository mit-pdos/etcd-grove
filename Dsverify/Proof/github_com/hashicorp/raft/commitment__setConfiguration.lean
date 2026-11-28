/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/commitment__setConfiguration.lean (241f27e).
-/
/-
The proof of `raft.commitment.setConfiguration` (stage 4 interface: a new spec, to be proved).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.commitment__setConfiguration
public import Dsverify.Spec.github_com.hashicorp.raft.commitment__recalculate
public import Dsverify.Proof.github_com.hashicorp.raft.leader.DurView

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]

open github_com.hashicorp.raft github_com.hashicorp.raft.gprot github_com.hashicorp.raft.proto

theorem github_com.hashicorp.raft.commitment.setConfiguration.wp_proof
    (wp_recalculate : github_com.hashicorp.raft.commitment.recalculate.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.commitment.setConfiguration.spec (GF := GF) (hG := hG) := by
  intro γ rc i s cm c p
  wp_start as ⟨#Hcm, #HInv, #Hdur, Hsrv, #Hldr, Hcc, #Hcfg, %Hpre⟩
  obtain ⟨hL1, hcv⟩ := Hpre
  iunfold cfgAtIs at Hcfg
  icases Hcfg with (⟨%h0, -⟩ | ⟨%ss, %eN, Hcv0, %HeN⟩)
  · exfalso; omega
  iunfold cfgVal at Hcv0
  icases Hcv0 with ⟨#Hss, %Hssok⟩
  obtain ⟨-, HeNent, HeNk, HeNd⟩ := HeN
  have hdomN : γ.cv eN.data = srvVoters ss := by rw [hcv, HeNd]; exact cfgDec_encode _ _ Hssok
  ihave Hf := durFact γ rc i (E := ⊤) (by solve_ndisj) s iprop(Inv γ ∗ leaderIs γ s.term i)
    iprop(llogPre γ s.term s.log)
    (by iintro ⟨⟨#HI, #Hl⟩, Hs⟩; iapply llogPre_leader γ (⊤ \ ↑durN) dvN_gprot_dur i s; iframe; iframe #)
    $$ [Hsrv]
  · iframe; iframe #
  iapply (wp_ncfupd _ _ rfl)
  iintro Hnc
  imod Hf $$ Hnc with ⟨Hnc, Hsrv, #Hpre⟩
  imodintro
  iframe Hnc
  ihave #HidxN := llogPre_idx γ s.term s.log _ eN HeNent $$ Hpre
  wp_apply wp_with_defer as %defer Hdefer
  unfold isCommitment
  icases Hcm with ⟨-, #Hmu⟩
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
  unfold commitInv
  icases Hinv with ⟨%ch, %mi, %mm, %ci, %si, %n0, %p', %e, Hch, #Hchn, Hmi, Hmm, Hcc', #He, %Hdom, #Hacks, Hci, #Hcio, #Hsip, #Hn0, %Hsi, #Hl, -⟩
  ihave %Hpp := ccfgOwn_agree γ i s.term p p' $$ [Hcc Hcc']
  · iframe
  subst Hpp
  ihave Hf := durFact γ rc i (E := ⊤) (by solve_ndisj) s
    iprop(Inv γ ∗ leaderIs γ s.term i ∗ ccfgOwn γ i s.term p ∗ ccfgOwn γ i s.term p)
    iprop(ccfgOwn γ i s.term (lastCfgIdx s.log) ∗ ccfgOwn γ i s.term (lastCfgIdx s.log))
    (by iintro ⟨⟨#HI, #Hl, H1, H2⟩, Hs⟩
        iapply installCfg_upd γ (⊤ \ ↑durN) dvN_gprot_dur i s p; iframe; iframe #)
    $$ [Hsrv Hcc Hcc']
  · iframe; iframe #
  wp_auto
  iapply (wp_ncfupd _ _ rfl)
  iintro Hnc
  imod Hf $$ Hnc with ⟨Hnc, Hsrv, Hcc, Hcc'⟩
  imodintro
  iframe Hnc
  wp_apply (wp_map_make1 (K := SID) (V := w64) ServerID.ty go.uint64) as %mi2 Hmm2
  ihave %Hsllen := ownSlice_len $$ Hss
  ihave HI : (∃ (k : Nat) (mm2 : GMap SID w64), "Hctr" ∷ i_ptr ↦ W64 k ∗
      "Hmm2" ∷ mi2 ↦$ mm2 ∗ "server" ∷ (∃ v : Server, server_ptr ↦ v) ∗
      "%Hk" ∷ ⌜k ≤ ss.length ∧ (∀ j, (mm2 !! j).isSome ↔ j ∈ srvVoters (ss.take k)) ∧
        ∀ j m, mm2 !! j = some m → m = W64 0 ∨ mm !! j = some m⌝ : IProp GF) $$ [i Hmm2 server]
  · iexists 0, ∅; iframe
    isplitl [server]
    · iexists _; iexact server
    ipureintro
    refine ⟨by omega, fun j => by simp [srvVoters], fun j m h => by simp at h⟩
  wp_for HI
  split
  · rename_i Hc
    icases server with ⟨%sv0, server⟩
    obtain ⟨hk, hdom2, hval2⟩ := Hk
    have hkl : k < ss.length := by simp only [decide_eq_true_eq] at Hc; word
    list_elem ss k as sv
    wp_auto
    rw [ite_eq_left_iff.mpr (by intro h; exfalso; apply h; constructor <;> word)]
    wp_apply (wp_load_slice_index c.Servers' (sint.Z (W64 k)) ss DFrac.discard sv (by word))
      $$ [Hss] as -
    · iframe #
      ipureintro
      have : (sint.Z (W64 (k : Int))).toNat = k := by word
      rw [this]; exact Hsv_lookup
    have hctr : W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) := by word
    have hsv : ss[k] = sv := (List.getElem?_eq_some_iff.mp Hsv_lookup).2
    have htake : ss.take (k + 1) = ss.take k ++ [sv] := by
      rw [List.take_succ, List.getElem?_eq_getElem hkl, hsv]; rfl
    wp_if_destruct
    · wp_apply (wp_map_lookup1 (K := SID) (V := w64) ServerID.ty go.uint64 mi mm sv.ID' (DFrac.own 1))
        $$ [$Hmm] as Hmm
      wp_apply (wp_mapInsert (K := SID) (V := w64) ServerID.ty mi2 mm2 sv.ID'
        ((mm !! sv.ID').getD (Perennial.zero_val w64))) $$ [$Hmm2] as Hmm2
      wp_for_post
      iframe
      iexists (k + 1), (<[sv.ID' := (mm !! sv.ID').getD (Perennial.zero_val w64)]> mm2)
      rw [hctr]
      iframe
      isplitl [server]
      · iexists _; iframe
      ipureintro
      refine ⟨by omega, ?_, ?_⟩
      · intro j
        rw [htake]
        simp only [srvVoters, List.filter_append, List.map_append, List.mem_append]
        simp only [List.filter_cons, Hif, decide_true, List.filter_nil, ↓reduceIte, List.map_cons,
          List.map_nil, List.mem_singleton]
        have := hdom2 j
        simp only [srvVoters] at this
        rw [← this]
        by_cases hj : sv.ID' = j
        · subst hj; simp
        · rw [GMap.lookup_insert_ne _ _ hj]
          constructor
          · intro h; exact Or.inl h
          · intro h; rcases h with h | h
            · exact h
            · exact absurd h.symm hj
      · intro j m hm
        by_cases hj : sv.ID' = j
        · subst hj; rw [GMap.lookup_insert] at hm; cases hm
          cases h : mm !! sv.ID' with
          | none => left; rfl
          | some m' => right; rfl
        · rw [GMap.lookup_insert_ne _ _ hj] at hm; exact hval2 j m hm
    · wp_for_post
      iframe
      iexists (k + 1), mm2
      rw [hctr]
      iframe
      isplitl [server]
      · iexists _; iframe
      ipureintro
      refine ⟨by omega, ?_, hval2⟩
      intro j
      rw [htake, hdom2 j]
      simp [srvVoters, List.filter_append]
      intro h; exact absurd h Hif
  rename_i Hc
  obtain ⟨hk, hdom2, hval2⟩ := Hk
  have hkn : k = ss.length := by simp only [decide_eq_true_eq] at Hc; word
  subst hkn
  rw [List.take_length, ← hdomN] at hdom2
  have hbound : (γ.cv eN.data).length < 2 ^ 32 := by
    rw [hdomN]
    have h1 : (srvVoters ss).length ≤ ss.length := by
      unfold srvVoters; rw [List.length_map]; exact List.length_filter_le _ _
    have h2 := Hssok.2.2.2.2
    omega
  wp_auto
  wp_apply (wp_recalculate γ i s.term cm) $$ [Hch Hmi Hmm2 Hci Hcc'] as Hinv
  · unfold commitInv
    iexists ch, mi2, mm2, ci, si, n0, lastCfgIdx s.log, eN
    iframe; iframe #
    isplitr; · ipureintro; exact ⟨HeNk, hdom2, hbound⟩
    isplitr
    · iapply BigSepM.bigSepM_forall_elim
      iintro %j %m %hjm
      rcases hval2 j m hjm with h0 | hold
      · ileft; ipureintro; exact h0
      · iapply (BigSepM.bigSepM_lookup hold) $$ Hacks
    ipureintro; exact Hsi
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hinv]
  · inext; unfold commitInv; iexact Hinv
  iapply HΦ; iframe

end proof

end Perennial
