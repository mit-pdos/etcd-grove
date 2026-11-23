/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/replica/QuorumSubsets.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`subsets`: the recursive enumeration of the quorums (strong induction on `N - i`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.QuorumLemmas
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps

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

/-- What the `quorumSize == 0` branch emits. -/
def emit0 (k : w64) (cur : List Nat) : List (List Nat) := if k = W64 0 then [cur] else []

theorem flatMap_range'_split {α : Type} (f : Nat → List α) (i j N : Nat) (hij : i ≤ j)
    (hjN : j < N) :
    (List.range' i (N - i)).flatMap f =
      (List.range' i (j - i)).flatMap f ++ f j ++ (List.range' (j + 1) (N - (j + 1))).flatMap f := by
  have h1 : List.range' i (N - i) = List.range' i (j - i) ++ List.range' j (N - j) := by
    have h : List.range' i (j - i) ++ List.range' (i + 1 * (j - i)) (N - j) =
        List.range' i (j - i + (N - j)) := List.range'_append
    rw [show i + 1 * (j - i) = j by omega, show j - i + (N - j) = N - i by omega] at h
    exact h.symm
  have h2 : List.range' j (N - j) = j :: List.range' (j + 1) (N - (j + 1)) := by
    rw [show N - j = (N - (j + 1)) + 1 by omega, List.range'_succ]
  rw [h1, h2]; simp

theorem flatMap_range'_succ {α : Type} (f : Nat → List α) (i j : Nat) (hij : i ≤ j) :
    (List.range' i (j + 1 - i)).flatMap f = (List.range' i (j - i)).flatMap f ++ f j := by
  rw [show j + 1 - i = (j - i) + 1 by omega, List.range'_concat]
  simp [show i + (j - i) = j by omega]

theorem replica.subsets.wp_proof (wp_copy : replica.Quorum.copy.spec) :
    replica.subsets.spec := by
  intro ids N k i q cur qs L treat
  suffices H : ∀ (n : Nat) (k : w64) (i : Nat) (cur : List Nat) (L : Nat → List (List Nat)),
      N - i = n →
      {{ ids ↦*□ idsList N ∗ qOwn q (DFrac.own 1) cur ∗ qsOwn qs N L (DFrac.own 1) ∗
          treatOk treat ∗
          ⌜N ≤ 7 ∧ i ≤ N ∧ (∀ x ∈ cur, x < i) ∧ cur.Nodup ∧ -(i : Int) ≤ sint.Z k ∧
            sint.Z k ≤ N ∧ ∀ l, (L l).length +
              ((emitL N (sint.Z k) i cur).filter (fun s => decide (l ∈ s))).length < 2 ^ 31⌝ }}
        (App (App (App (App (App (App (App (Val (@! replica.subsets)) (Val #ids))
          (Val #(W64 N))) (Val #k)) (Val #(W64 i))) (Val #q)) (Val #qs)) (Val #treat))
      {{ RET #(); qOwn q (DFrac.own 1) cur ∗
          qsOwn qs N (addL L (emitL N (sint.Z k) i cur)) (DFrac.own 1) }} from
    H _ k i cur L rfl
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro k i cur L hn
  wp_start as ⟨#Hids, Hq, Hqs, #Htreat, %Hpre⟩
  obtain ⟨hN7, hiN, hcur, hnd, hk1, hk2, hlen⟩ := Hpre
  wp_auto
  wp_join iprop(qOwn q (DFrac.own 1) cur ∗ qsOwn qs N (addL L (emit0 k cur)) (DFrac.own 1) ∗
      qs_ptr ↦ qs ∗ q_ptr ↦ q ∗ repNum_ptr ↦ W64 (N : Int) ∗ treat_ptr ↦ treat)
    with [Hq Hqs qs q repNum treat] as ⟨Hq, Hqs, qs, q, repNum, treat⟩
  · -- `quorumSize == 0`: the emission loop over `repId`
    rw [show (W32 0 : w32) = w32n 0 from rfl]
    ihave HI : (∃ r : Nat, repId_ptr ↦ w32n r ∗ ⌜r ≤ N⌝ ∗ qOwn q (DFrac.own 1) cur ∗
        qsOwn qs N (fun l => if l < r then addL L [cur] l else L l) (DFrac.own 1) : IProp netDistGF)
      $$ [repId Hq Hqs]
    · iexists 0
      iframe Hq
      isplitl [repId]; · iexact repId
      isplitr; · ipureintro; omega
      iapply qsOwn_congr $$ Hqs
      intro l _; simp
    wp_for HI
    icases HI with ⟨repId, %hr, Hq, Hqs⟩
    wp_auto
    have hcond : sint.Z (w32n r) < sint.Z (W32 (sint.Z (W64 (N : Int)))) ↔ r < N := by
      have h1 : sint.Z (w32n r) = r := sint_W32 _ (by omega) (by omega)
      have h2 : sint.Z (W32 (sint.Z (W64 (N : Int)))) = N := by
        rw [sint_W64 _ (by omega) (by omega)]; exact sint_W32 _ (by omega) (by omega)
      omega
    rw [show decide (sint.Z (w32n r) < sint.Z (W32 (sint.Z (W64 (N : Int))))) = decide (r < N) from
      decide_eq_decide.mpr hcond]
    cleanup_bool_decide
    by_cases hrN : r < N
    · simp only [hrN, decide_true, ite_true]
      wp_auto
      icases (qsOwn_acc qs N _ _ r hrN) $$ Hqs with ⟨%m, %p, #Hm, %Hp, -, Hl, Hclose⟩
      wp_apply (wp_map_lookup1 (K := w32) (V := Loc)) $$ [$Hm] as -
      rw [Hp]
      simp only [Option.getD_some]
      iunfold lqsOwn at Hl
      icases Hl with ⟨%mi, Hmi, %Hdom, Hbig⟩
      wp_apply (wp_map_len (K := w32) (V := Loc) (t := replica.QuorumsOfLeader.ty)) $$ [$Hmi] as Hmi
      have e : (if r < r then addL L [cur] r else L r) = L r := by simp
      rw [e] at Hdom ⊢
      rw [lqs_size mi _ Hdom.1 Hdom.2]
      rw [show W32 (sint.Z (W64 ((L r).length : Int))) = w32n (L r).length by
        unfold w32n; rw [sint_W64 _ (by omega) (by omega)]]
      iunfold qOwn at Hq
      icases Hq with ⟨%mq, Hmq, %Hrq⟩
      wp_apply (wp_map_lookup2 (K := w32) (V := Unit)) $$ [$Hmq] as Hmq
      have hex : (mq !! w32n r).isSome = decide (r ∈ cur) := by
        rw [Hrq]
        have : w32n r ∈ cur.map w32n ↔ r ∈ cur := by
          constructor
          · intro h
            obtain ⟨x, hx, hxe⟩ := List.mem_map.mp h
            have := w32n_inj x r (by have := hcur x hx; omega) (by omega) hxe
            subst this; exact hx
          · intro h; exact List.mem_map_of_mem h
        by_cases h : r ∈ cur <;> simp [h, this]
      rw [hex]
      wp_if_destruct
      · -- `r ∈ cur`: append a copy of `q` to `qs[r]`
        have hrc : r ∈ cur := by simpa using Hif
        have hQ : (L r).length + 1 < 2 ^ 31 := by
          have h := hlen r
          have h0 : sint.Z (W64 0) = 0 := rfl
          rw [h0, emitL_unfold] at h
          simp only [ite_true, List.singleton_append, List.filter_cons, hrc, decide_true,
            List.length_cons] at h
          omega
        wp_method_call
        wp_auto
        ihave Hq : qOwn q (DFrac.own 1) cur $$ [Hmq]
        · iunfold qOwn; iexists mq; iframe Hmq; ipureintro; exact Hrq
        wp_apply (wp_copy q _ cur) $$ [$Hq] as %nq ⟨Hq, Hnq⟩
        iunfold qOwn at Hnq
        icases Hnq with ⟨%mn, Hmn, %Hrn⟩
        imod (ownMap_persist (K := w32) (V := Unit)) $$ Hmn with #Hmn
        wp_apply (wp_map_lookup1 (K := w32) (V := Loc)) $$ [$Hm] as -
        rw [Hp]
        simp only [Option.getD_some]
        wp_apply (wp_mapInsert (K := w32) (V := Loc)) $$ [$Hmi] as Hmi
        wp_bind (App (App (App (Val #treat) _) _) _)
        ihave #Ht := Htreat
        iunfold treatOk at Ht
        iapply Ht
        wp_auto
        wp_for_post
        iframe
        iexists (r + 1)
        rw [show w32n r + W32 1 = w32n (r + 1) by unfold w32n; word]
        iframe repId Hq
        isplitr; · ipureintro; omega
        ihave Hl := lqsOwn_snoc p mi (L r) nq cur hQ Hdom.2 $$ [Hmi Hbig]
        · iframe Hmi Hbig
          iunfold qOwn; iexists mn; iframe Hmn; ipureintro; exact Hrn
        iapply qsOwn_congr $$ (Hclose $$ Hl)
        intro l _
        unfold updL
        by_cases hl : l = r
        · subst hl; simp [addL, hrc]
        · by_cases hl2 : l < r
          · simp [hl, hl2, show l < r + 1 by omega]
          · simp [hl, hl2, show ¬ l < r + 1 by omega]
      · -- `r ∉ cur`: nothing
        have hrc : r ∉ cur := by simpa using Hif
        wp_for_post
        iframe
        iexists (r + 1)
        rw [show w32n r + W32 1 = w32n (r + 1) by unfold w32n; word]
        iframe repId
        isplitr; · ipureintro; omega
        isplitl [Hmq]
        · iunfold qOwn; iexists mq; iframe Hmq; ipureintro; exact Hrq
        ihave Hl : lqsOwn p (DFrac.own 1) (L r) $$ [Hmi Hbig]
        · iunfold lqsOwn; iexists mi; iframe Hmi Hbig; ipureintro; exact Hdom
        iapply qsOwn_congr $$ (Hclose $$ Hl)
        intro l _
        unfold updL
        by_cases hl : l = r
        · subst hl; simp [addL, hrc]
        · by_cases hl2 : l < r
          · simp [hl, hl2, show l < r + 1 by omega]
          · simp [hl, hl2, show ¬ l < r + 1 by omega]
    · simp only [hrN, decide_false, Bool.false_eq_true, ite_false]
      have hrN' : r = N := by omega
      subst hrN'
      iframe
      iapply qsOwn_congr $$ Hqs
      intro l hl
      simp [emit0, hl]
  · unfold emit0; rw [if_neg Hif, addL_nil]; iframe
  -- the `j` loop
  ihave HJ : (∃ j : Nat, j_ptr ↦ W64 (j : Int) ∗ ⌜i ≤ j ∧ j ≤ N⌝ ∗ qOwn q (DFrac.own 1) cur ∗
      qsOwn qs N (addL L (emit0 k cur ++ (List.range' i (j - i)).flatMap
        (fun j' => emitL N (sint.Z k - 1) (j' + 1) (cur ++ [j'])))) (DFrac.own 1) : IProp netDistGF)
    $$ [j Hq Hqs]
  · iexists i
    iframe j Hq
    isplitr; · ipureintro; omega
    simp only [Nat.sub_self, List.range'_zero, List.flatMap_nil, List.append_nil]
    iexact Hqs
  wp_for HJ
  icases HJ with ⟨j, %hj, Hq, Hqs⟩
  wp_auto
  have hcond : sint.Z (W64 (j : Int)) < sint.Z (W64 (N : Int)) ↔ j < N := by
    rw [sint_W64 _ (by omega) (by omega), sint_W64 _ (by omega) (by omega)]; omega
  rw [show decide (sint.Z (W64 (j : Int)) < sint.Z (W64 (N : Int))) = decide (j < N) from
    decide_eq_decide.mpr hcond]
  cleanup_bool_decide
  by_cases hjN : j < N
  · simp only [hjN, decide_true, ite_true]
    wp_auto
    ihave %Hlen := ownSlice_len _ _ _ $$ Hids
    have hidsj : (idsList N)[(sint.Z (W64 (j : Int))).toNat]? = some (w32n j) := by
      rw [sint_W64 _ (by omega) (by omega)]; simp [idsList, hjN]
    have hlenN : (idsList N).length = N := by simp [idsList]
    have hidsl : sint.Z ids.len = N := by
      have h1 : N = (sint.Z ids.len).toNat := by rw [← hlenN, Hlen.1]
      have h2 := Hlen.2
      omega
    have hidsl' : BitVec.toInt ids.len = N := hidsl
    rw [if_pos (by rw [sint_W64 _ (by omega) (by omega)]; omega)]
    wp_apply (wp_load_slice_index ids _ (idsList N) _ (w32n j) (by rw [sint_W64 _ (by omega) (by omega)]; omega))
      $$ [$Hids] as -
    · ipureintro; exact hidsj
    iunfold qOwn at Hq
    icases Hq with ⟨%mq, Hmq, %Hrq⟩
    wp_apply (wp_mapInsert (K := w32) (V := Unit)) $$ [$Hmq] as Hmq
    rw [show W64 (j : Int) + W64 1 = W64 ((j + 1 : Nat) : Int) by word]
    have hk' : sint.Z (k - W64 1) = sint.Z k - 1 := by
      have : sint.Z k < 2 ^ 63 := by word
      word
    -- the remaining emissions after `j`'s
    have hsplit := flatMap_range'_split (fun j' => emitL N (sint.Z k - 1) (j' + 1) (cur ++ [j']))
      i j N hj.1 hjN
    wp_apply (ih (N - (j + 1)) (by omega) (k - W64 1) (j + 1) (cur ++ [j])
        (addL L (emit0 k cur ++ (List.range' i (j - i)).flatMap
          (fun j' => emitL N (sint.Z k - 1) (j' + 1) (cur ++ [j'])))) rfl)
      $$ [Hmq Hqs] as ⟨Hq, Hqs⟩
    · iframe Hqs Hids Htreat
      isplitl [Hmq]
      · iunfold qOwn; iexists _; iframe Hmq; ipureintro
        exact qRepr_insert mq cur j Hrq
      ipureintro
      refine ⟨hN7, by omega, ?_, ?_, by omega, by omega, ?_⟩
      · intro x hx; simp at hx; rcases hx with hx | hx
        · have := hcur x hx; omega
        · omega
      · rw [List.nodup_append]
        refine ⟨hnd, by simp, ?_⟩
        intro a ha b hb; simp at hb; subst hb; have := hcur a ha; omega
      · intro l
        have h := hlen l
        rw [emitL_unfold, hsplit] at h
        rw [hk']
        simp only [addL, List.filter_append, List.length_append] at h ⊢
        unfold emit0
        have : (if k = W64 0 then [cur] else []) = (if sint.Z k = 0 then [cur] else []) := by
          by_cases h0 : k = W64 0
          · rw [if_pos h0, if_pos (by rw [h0]; rfl)]
          · rw [if_neg h0, if_neg (fun h => h0 (by word))]
        rw [this]
        omega
    rw [if_pos (by rw [sint_W64 _ (by omega) (by omega)]; omega)]
    wp_apply (wp_load_slice_index ids _ (idsList N) _ (w32n j) (by rw [sint_W64 _ (by omega) (by omega)]; omega))
      $$ [$Hids] as -
    · ipureintro; exact hidsj
    iunfold qOwn at Hq
    icases Hq with ⟨%mq', Hmq, %Hrq'⟩
    wp_apply (wp_mapDelete _ mq' (w32n j) go.int32 (go.StructType [])) $$ [$Hmq] as Hmq
    wp_for_post
    iframe
    iexists (j + 1)
    rw [show W64 (j : Int) + W64 1 = W64 ((j + 1 : Nat) : Int) by word]
    iframe j
    isplitr; · ipureintro; omega
    isplitl [Hmq]
    · iunfold qOwn; iexists _; iframe Hmq; ipureintro
      apply qRepr_delete mq' cur j Hrq'
      intro x hx h
      have := w32n_inj x j (by have := hcur x hx; omega) (by omega) h
      have := hcur x hx; omega
    rw [hk', addL_append, flatMap_range'_succ _ i j hj.1, List.append_assoc]
    iexact Hqs
  · simp only [hjN, decide_false, Bool.false_eq_true, ite_false]
    have hjN' : j = N := by omega
    rw [show j - i = N - i by omega]
    wp_auto
    iapply HΦ
    iframe Hq
    iapply qsOwn_congr $$ Hqs
    intro l _
    rw [emitL_unfold]
    congr 3
    unfold emit0
    have : k = W64 0 ↔ sint.Z k = 0 := by
      constructor
      · rintro rfl; rfl
      · intro h; word
    by_cases h0 : k = W64 0
    · rw [if_pos h0, if_pos (this.mp h0)]
    · rw [if_neg h0, if_neg (fun h => h0 (this.mpr h))]

end proofs

end Perennial.github_com.imdea_software.swiftpaxos

end
