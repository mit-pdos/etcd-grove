/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/newCommitment.lean (241f27e).
-/
/-
The proof of `newCommitment` (replication subsystem).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.newCommitment
public import Dsverify.Proof.github_com.hashicorp.raft.ReplBase

@[expose] public section

set_option linter.unusedVariables false
set_option linter.deprecated false

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

open github_com.hashicorp.raft github_com.hashicorp.raft.gprot proto

theorem github_com.hashicorp.raft.newCommitment.wp_proof :
    github_com.hashicorp.raft.newCommitment.spec (GF := GF) (hG := hG) := by
  intro γ i T n0 p ch c ss e si
  wp_start as ⟨#HInv, #Hch, #Hcfg, #He, %Hecfg, Hcc, #Hl, #Hn0, %Hsi⟩
  iapply wp_fupd
  unfold cfgVal
  icases Hcfg with ⟨#Hss, %Hssok⟩
  obtain ⟨hek, hed, hcv⟩ := Hecfg
  have hdom0 : γ.cv e.data = srvVoters ss := by rw [hcv, hed]; exact cfgDec_encode _ _ Hssok
  wp_auto
  wp_apply (wp_map_make1 (K := SID) (V := w64) ServerID.ty go.uint64) as %mi Hmm
  ihave %Hsl := ownSlice_len $$ Hss
  ihave HI : iprop(∃ (iv : w64) (mm : GMap SID w64) (sv : Server),
      "i" ∷ i_ptr ↦ iv ∗ "Hmm" ∷ mi ↦$ mm ∗ "server" ∷ server_ptr ↦ sv ∗
      "%Hiv" ∷ ⌜0 ≤ sint.Z iv ∧ sint.Z iv ≤ ss.length ∧
        (∀ j, (mm !! j).isSome ↔ j ∈ srvVoters (ss.take (sint.nat iv))) ∧
        ∀ j m, mm !! j = some m → m = W64 0⌝) $$ [i Hmm server]
  · iexists (W64 0), ∅, _
    iframe
    ipureintro
    refine ⟨by word, by word, ?_, ?_⟩
    · intro j
      rw [show sint.nat (W64 0) = 0 from rfl]
      simp [srvVoters]
    · intro j m h; simp at h
  wp_for HI
  have hlenZ : sint.Z c.Servers'.len = (ss.length : Int) := by
    obtain ⟨h1, h2⟩ := Hsl; word
  wp_if_destruct
  · obtain ⟨hiv0, hivl, hdomk, hzero⟩ := Hiv
    have hlt : sint.nat iv < ss.length := by
      have : sint.Z iv < sint.Z c.Servers'.len := Hif
      word
    rw [if_pos (show 0 ≤ sint.Z iv ∧ sint.Z iv < sint.Z c.Servers'.len by omega)]
    list_elem ss (sint.nat iv) as sv'
    wp_apply (wp_load_slice_index c.Servers' (sint.Z iv) ss DFrac.discard sv' hiv0) $$ [Hss] as -
    · iframe #; ipureintro; exact Hsv'_lookup
    have hn1 : sint.nat (iv + W64 1) = sint.nat iv + 1 := by word
    have hsv : ss[sint.nat iv] = sv' := (List.getElem?_eq_some_iff.mp Hsv'_lookup).2
    have htake : ss.take (sint.nat iv + 1) = ss.take (sint.nat iv) ++ [sv'] := by
      rw [List.take_succ, List.getElem?_eq_getElem hlt, hsv]; rfl
    by_cases hvoter : sv'.Suffrage' = W64 0
    · rw [decide_eq_true hvoter]
      wp_auto
      wp_apply (wp_mapInsert (K := SID) (V := w64) ServerID.ty mi mm sv'.ID' (W64 0)) $$ [$Hmm] as Hmm
      wp_for_post
      iframe
      iexists (iv + W64 1), (<[sv'.ID' := W64 0]> mm), sv'
      iframe
      ipureintro
      refine ⟨by word, by word, ?_, ?_⟩
      · intro j
        rw [hn1, htake]
        simp only [srvVoters, List.filter_append, List.map_append, List.mem_append]
        simp only [List.filter_cons, hvoter, decide_true, List.filter_nil, ↓reduceIte, List.map_cons,
          List.map_nil, List.mem_singleton]
        have := hdomk j
        simp only [srvVoters] at this
        rw [← this]
        by_cases hj : sv'.ID' = j
        · subst hj; simp
        · rw [GMap.lookup_insert_ne _ _ hj]
          constructor
          · intro h; exact Or.inl h
          · intro h; rcases h with h | h
            · exact h
            · exact absurd h.symm hj
      · intro j m hm
        by_cases hj : sv'.ID' = j
        · subst hj; rw [GMap.lookup_insert] at hm; cases hm; rfl
        · rw [GMap.lookup_insert_ne _ _ hj] at hm; exact hzero j m hm
    · rw [decide_eq_false hvoter]
      wp_auto
      wp_for_post
      iframe
      iexists (iv + W64 1), mm, sv'
      iframe
      ipureintro
      refine ⟨by word, by word, ?_, hzero⟩
      intro j
      rw [hn1, htake, hdomk j]
      simp [srvVoters, List.filter_append]
      intro h; exact absurd h hvoter
  -- the loop is done: the map has a zero match index for each voter
  obtain ⟨hiv0, hivl, hdomk, hzero⟩ := Hiv
  have hend : sint.nat iv = ss.length := by
    have : ¬ sint.Z iv < sint.Z c.Servers'.len := Hif
    word
  rw [hend, List.take_length, ← hdom0] at hdomk
  have hbound : (γ.cv e.data).length < 2 ^ 32 := by
    rw [hdom0]
    have h1 : (srvVoters ss).length ≤ ss.length := by
      unfold srvVoters; rw [List.length_map]; exact List.length_filter_le _ _
    have h2 := Hssok.2.2.2.2
    omega
  iStructNamed «$r0»
  ipersist startIndex
  imod sync.init_Mutex (commitInv γ i T «$r0_ptr») ⊤ _ $$ Mutex [commitCh matchIndexes commitIndex Hmm Hcc]
    with #Hmu
  · inext
    unfold commitInv
    iexists ch, mi, mm, (W64 0), si, n0, p, e
    iframe; iframe #
    isplitr; · ipureintro; exact ⟨hek, hdomk, hbound⟩
    isplitr
    · iapply BigSepM.bigSepM_forall_elim
      iintro %k %v %hkv
      ileft; ipureintro; exact hzero k v hkv
    isplitr
    · ileft; ipureintro; rfl
    ipureintro; exact Hsi
  imodintro
  iapply HΦ
  unfold isCommitment
  isplitr; · iexists si, n0; iframe #; ipureintro; exact Hsi
  iexact Hmu

end proof

end Perennial
