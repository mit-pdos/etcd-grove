/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/replica/QuorumSet.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`newQuorumSetAdvance`, `NewQuorumSet`, `QuorumSet.AQ`: proofs.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.QuorumLemmas
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.QuorumArith

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF]
variable [sem : go.Semantics] [replica.Assumptions] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]

set_option goose.wp.extras true

open replica.quorum

theorem replica.newQuorumSetAdvance.wp_proof (wp_NewQuorum : replica.NewQuorum.spec)
    (wp_NewQuorumsOfLeader : replica.NewQuorumsOfLeader.spec)
    (wp_subsets : replica.subsets.spec) : replica.newQuorumSetAdvance.spec := by
  intro N treat
  wp_start as ⟨#Htreat, %HN⟩
  wp_auto
  wp_apply (wp_slice_make2 (V := w32) (W64 (N : Int))) as %ids ⟨Hids, -⟩
  · ipureintro; word
  wp_apply wp_NewQuorum as %q Hq
  wp_apply (wp_map_make2 (K := w32) (V := Loc)) as %qs Hqs
  have hNn : sint.nat (W64 (N : Int)) = N := by
    word
  rw [hNn]
  ihave %Hlen := ownSlice_len _ _ _ $$ Hids
  have hidsl : sint.Z ids.len = N := by
    have h1 := Hlen.1
    simp only [List.length_replicate] at h1
    unfold sint.nat at h1
    have h2 : (0 : Int) ≤ BitVec.toInt ids.len := Hlen.2
    show BitVec.toInt ids.len = N
    omega
  ihave HI : (∃ (c : Nat) (d : w64) (M : GMap w32 Loc), i_ptr ↦ W64 (c : Int) ∗ id_ptr ↦ d ∗
      ⌜c ≤ N ∧ ∀ k : w32, (M !! k).isSome ↔ ∃ l < c, k = w32n l⌝ ∗
      ids ↦* (idsList c ++ List.replicate (N - c) (zero_val w32)) ∗ qs ↦$ M ∗
      [∗list] l ∈ List.range c, ∃ p, ⌜M !! w32n l = some p⌝ ∗ lqsOwn p (DFrac.own 1) [] : IProp netDistGF)
    $$ [i id Hids Hqs]
  · iexists 0, _, ∅
    iframe i id Hqs
    isplitr
    · ipureintro; refine ⟨by omega, fun k => ?_⟩; simp
    rw [show idsList 0 = [] from rfl, Nat.sub_zero, List.nil_append]
    iframe Hids
    rw [List.range_zero]
    iapply BI.BigSepL.bigSepL_nil.2
    itrivial
  wp_for HI
  icases HI with ⟨i, id, %Hc, Hids, Hqs, Hbig⟩
  wp_auto
  have hcond : sint.Z (W64 (c : Int)) < sint.Z ids.len ↔ c < N := by
    rw [sint_W64 _ (by omega) (by omega), hidsl]; omega
  rw [show decide (sint.Z (W64 (c : Int)) < sint.Z ids.len) = decide (c < N) from
    decide_eq_decide.mpr hcond]
  cleanup_bool_decide
  by_cases hcN : c < N
  · simp only [hcN, decide_true, ite_true]
    wp_auto
    have hc64 : sint.Z (W64 (c : Int)) = c := sint_W64 _ (by omega) (by omega)
    have hlenL : (idsList c ++ List.replicate (N - c) (zero_val w32)).length = N := by
      simp [idsList]; omega
    rw [if_pos (by rw [hc64, hidsl]; omega)]
    wp_apply (wp_load_slice_index ids _ _ _ (zero_val w32) (by omega)) $$ [$Hids] as Hids
    · ipureintro
      rw [hc64]
      simp [idsList, List.getElem?_append_right, hcN, List.getElem?_replicate]; omega
    rw [if_pos (by rw [hc64, hidsl]; omega)]
    wp_apply (wp_store_slice_index ids _ _ (W32 (sint.Z (W64 (c : Int))))) $$ [$Hids] as Hids
    · ipureintro; rw [hc64, hlenL]; omega
    wp_apply wp_NewQuorumsOfLeader as %p Hp
    wp_apply (wp_mapInsert (K := w32) (V := Loc)) $$ [$Hqs] as Hqs
    wp_for_post
    iframe
    rw [show W64 (c : Int) + W64 1 = W64 ((c + 1 : Nat) : Int) by word]
    rw [hc64, show W32 (c : Int) = w32n c from rfl]
    iexists (c + 1), _, (<[w32n c := p]> M)
    iframe i id
    isplitr
    · ipureintro
      refine ⟨by omega, fun k => ?_⟩
      by_cases hk : w32n c = k
      · subst hk; simp only [GMap.lookup_insert, Option.isSome_some, true_iff]; exact ⟨c, by omega, rfl⟩
      · rw [GMap.lookup_insert_ne _ _ hk, Hc.2 k]
        constructor
        · rintro ⟨l, hl, rfl⟩; exact ⟨l, by omega, rfl⟩
        · rintro ⟨l, hl, rfl⟩
          refine ⟨l, ?_, rfl⟩
          rcases Nat.lt_or_ge l c with h | h
          · exact h
          · exfalso; apply hk; congr 1; omega
    isplitl [Hids]
    · have : (idsList c ++ List.replicate (N - c) (zero_val w32)).set c (w32n c) =
          idsList (c + 1) ++ List.replicate (N - (c + 1)) (zero_val w32) := by
        have hl : (idsList c).length = c := by simp [idsList]
        rw [List.set_append_right _ _ (by omega), hl, Nat.sub_self,
          show N - c = (N - (c + 1)) + 1 by omega, List.replicate_succ, List.set_cons_zero]
        have h2 : idsList (c + 1) = idsList c ++ [w32n c] := by
          simp only [idsList, List.range_succ, List.map_append, List.map_cons, List.map_nil]
        rw [h2, List.append_assoc]
        rfl
      rw [show (Int.toNat (c : Int)) = c by omega, this]
      iexact Hids
    iframe Hqs
    rw [List.range_succ]
    iapply BI.BigSepL.bigSepL_snoc.2
    isplitl [Hbig]
    · have hmono : ([∗list] l ∈ List.range c, ∃ p, ⌜M !! w32n l = some p⌝ ∗
            lqsOwn p (DFrac.own 1) []) ⊢
          ([∗list] l ∈ List.range c, ∃ p', ⌜(<[w32n c := p]> M) !! w32n l = some p'⌝ ∗
            lqsOwn p' (DFrac.own 1) [] : IProp netDistGF) := by
        apply BI.BigSepL.bigSepL_mono
        intro k x hk
        have hx : x < c := by have := List.getElem?_eq_some_iff.mp hk; simp at this; omega
        iintro ⟨%p', %Hp', H⟩
        iexists p'
        iframe H
        ipureintro
        rw [GMap.lookup_insert_ne]
        · exact Hp'
        · intro h; have := w32n_inj _ _ (by omega) (by omega) h; omega
      iapply hmono $$ Hbig
    · iexists p
      iframe Hp
      ipureintro; simp
  · simp only [hcN, decide_false, Bool.false_eq_true, ite_false]
    have hcN' : N = c := by omega
    subst hcN'
    wp_auto
    rw [Nat.sub_self, List.replicate_zero, List.append_nil]
    imod (ownSlice_persist ids _ _) $$ Hids with #Hids
    imod (ownMap_persist (K := w32) (V := Loc)) $$ Hqs with #Hqs
    ihave Hqso : qsOwn qs N (fun _ => []) (DFrac.own 1) $$ [Hbig]
    · iunfold qsOwn; iexists M; iframe Hqs Hbig; ipureintro; exact Hc.2
    have hk : sint.Z (W64 ((N : Int) / 2 + 1)) = ((N / 2 + 1 : Nat) : Int) := by
      rw [sint_W64 _ (by omega) (by omega)]; omega
    rw [show (W64 0 : w64) = W64 ((0 : Nat) : Int) from rfl]
    wp_apply +noauto (wp_subsets ids N (W64 ((N : Int) / 2 + 1)) 0 q [] qs (fun _ => []) treat)
      $$ [Hq Hqso] as ⟨Hq, Hqso⟩
    · iframe Hq Hqso Hids Htreat
      ipureintro
      refine ⟨HN.2, by omega, by simp, List.nodup_nil, by rw [hk]; omega, by rw [hk]; omega, ?_⟩
      intro l
      rw [hk, quorums_emitL]
      have h1 := quorums_length N HN.2
      have h2 := List.length_filter_le (fun s => decide (l ∈ s)) (quorums N)
      simp only [List.length_nil, Nat.zero_add]
      omega
    imod qsOwn_persist $$ Hqso with Hqso
    wp_auto
    iapply HΦ
    iunfold qsIs
    isplitr; · ipureintro; exact HN
    iapply qsOwn_congr $$ Hqso
    intro l _
    rw [hk, quorums_emitL]
    simp [addL, lqs]

theorem replica.NewQuorumSet.wp_proof (wp_adv : replica.newQuorumSetAdvance.spec) :
    replica.NewQuorumSet.spec := by
  intro N
  wp_start as %HN
  wp_auto
  wp_apply wp_adv as %qs Hqs
  · iframe
    isplitl
    · iunfold treatOk
      imodintro
      iintro %l %qid %q %Φ' HΦ'
      wp_auto
      iexact HΦ'
    · ipureintro; exact HN
  iapply HΦ $$ Hqs

theorem replica.QuorumSet.AQ.wp_proof (wp_Leader : replica.Leader.spec) :
    replica.QuorumSet.AQ.spec := by
  intro qs N b
  wp_start as ⟨#Hqs, %Hb⟩
  iunfold qsIs at Hqs
  icases Hqs with ⟨%HN, #Hqs⟩
  wp_auto
  generalize hbn : (sint.Z b).toNat = bn
  have hl : bn % N < N := Nat.mod_lt _ (by omega)
  ihave Hacc := qsOwn_acc qs N (lqs N) DFrac.discard _ hl $$ Hqs
  icases Hacc with ⟨%m, %p, #Hm, %Hp, %Hdom, #Hl, -⟩
  wp_apply (wp_map_len (K := w32) (V := Loc) (t := replica.QuorumSet.ty)) $$ [$Hm] as -
  rw [lqs_size m N (by omega) Hdom]
  have hN64 : sint.Z (W64 (N : Int)) = N := sint_W64 _ (by omega) (by omega)
  wp_apply wp_Leader
  · ipureintro; rw [hN64]; omega
  rw [hN64, srem_nat b N (by omega) Hb, hbn]
  wp_apply (wp_map_lookup1 (K := w32) (V := Loc)) $$ [$Hm] as -
  rw [Hp]
  simp only [Option.getD_some]
  iunfold lqsOwn at Hl
  icases Hl with ⟨%mi, #Hmi, %Hdomi, #Hbig⟩
  wp_apply (wp_map_len (K := w32) (V := Loc) (t := replica.QuorumSet.ty)) $$ [$Hm] as -
  rw [lqs_size m N (by omega) Hdom, hN64]
  have hN32 : sint.Z (W32 (N : Int)) = N := sint_W32 _ (by omega) (by omega)
  rw [if_neg (by omega)]
  wp_auto
  wp_apply (wp_map_len (K := w32) (V := Loc) (t := replica.QuorumsOfLeader.ty)) $$ [$Hmi] as -
  rw [lqs_size mi _ Hdomi.1 Hdomi.2]
  obtain ⟨hpos, h35⟩ := numAQ_pos N (bn % N) HN hl
  unfold numAQ at hpos h35
  have hL64 : sint.Z (W64 ((lqs N (bn % N)).length : Int)) = (lqs N (bn % N)).length :=
    sint_W64 _ (by omega) (by omega)
  rw [hL64]
  have hd := sdiv_nat b N (by omega) Hb
  have hd0 : 0 ≤ sint.Z (BitVec.sdiv b (W32 (N : Int))) := by
    rw [hd]; exact Int.ediv_nonneg Hb (by omega)
  have hL32 : sint.Z (W32 ((lqs N (bn % N)).length : Int)) = (lqs N (bn % N)).length :=
    sint_W32 _ (by omega) (by omega)
  rw [if_neg (by omega)]
  rw [srem_nat _ _ (by omega) hd0]
  have hqid : (sint.Z (BitVec.sdiv b (W32 (N : Int)))).toNat % (lqs N (bn % N)).length =
      (bn / N) % numAQ N (bn % N) := by
    rw [hd, toNat_ediv _ _ Hb, hbn]; rfl
  rw [hqid]
  generalize hqid' : (bn / N) % numAQ N (bn % N) = qid
  have hqlt : qid < (lqs N (bn % N)).length := by rw [← hqid']; exact Nat.mod_lt _ hpos
  have hget : (lqs N (bn % N))[qid]? = some (aqOf N bn) := by
    unfold aqOf; rw [hqid', List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hqlt]; rfl
  icases (BI.BigSepL.bigSepL_lookup hget) $$ Hbig with ⟨%ql, %Hql, #Hq⟩
  wp_auto
  wp_apply (wp_map_lookup1 (K := w32) (V := Loc)) $$ [$Hmi] as -
  rw [Hql]
  simp only [Option.getD_some]
  iapply HΦ $$ Hq

end proofs

end Perennial.github_com.imdea_software.swiftpaxos

end
