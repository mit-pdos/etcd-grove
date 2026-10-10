module
public import Spec.go_etcd_io.bbolt.internal.common.Mergepgids
public import Proof.go_etcd_io.bbolt.internal.common.SliceLemmas
public import Perennial.Proof.sort_proof.search

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.common

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

/-- The invariant of `Mergepgids`' loop. `merged` is `dst[0:k]`, holding `ms`; `dst[k:N]`
(`N = len(a)+len(b)`) is not written yet. `lead` and `follow` are what is left of `a` and
`b` (in some order), read at fractions handed back by `Hback`; both are non-empty (the
loop leaves by its `break`). `ms` is sorted and below the rest, and with it a permutation
of `a ++ b`. -/
def mergeInv (dst a b : GoSlice) (xs ys : List w64) (qa qb : DFrac)
    (lead_ptr follow_ptr merged_ptr : Loc) : IProp GF :=
  iprop(∃ (L F : GoSlice) (k : w64) (ls fs ms junk : List w64) (qL qF : DFrac),
    "lead" ∷ lead_ptr ↦ L ∗ "follow" ∷ follow_ptr ↦ F ∗
    "merged" ∷ merged_ptr ↦ slice.slice dst w64 (W64 0) k ∗
    "HL" ∷ L ↦*{qL} ls ∗ "HF" ∷ F ↦*{qF} fs ∗
    "Hback" ∷ (L ↦*{qL} ls -∗ F ↦*{qF} fs -∗ a ↦*{qa} xs ∗ b ↦*{qb} ys) ∗
    "HM" ∷ slice.slice dst w64 (W64 0) k ↦* ms ∗
    "Hjunk" ∷ slice.slice dst w64 k (a.len + b.len) ↦* junk ∗
    "%Hpure" ∷ ⌜0 ≤ sint.Z k ∧ ls ≠ [] ∧ fs ≠ [] ∧
      PgidsSorted ms ∧ PgidsSorted ls ∧ PgidsSorted fs ∧
      (∀ x ∈ ms, ∀ y ∈ ls ++ fs, uint.Z x ≤ uint.Z y) ∧
      (ms ++ ls ++ fs).Perm (xs ++ ys)⌝)

set_option maxHeartbeats 1600000 in
theorem Mergepgids.wp_proof : Mergepgids.spec (GF := GF) (hG := hG) := by
  intro dst a b ds xs ys qa qb Hlen Hsa Hsb
  wp_start as ⟨Hdst, Ha, Hb⟩
  ihave %Hdl := ownSlice_len _ _ _ $$ Hdst
  ihave %Hal := ownSlice_len _ _ _ $$ Ha
  ihave %Hbl := ownSlice_len _ _ _ $$ Hb
  ihave %Hdwf := ownSlice_wf _ _ _ $$ Hdst
  wp_auto
  wp_if_destruct
  · exfalso; word
  have Hdn := Hif
  wp_if_destruct
  · wp_apply wp_slice_copy dst ds b ys qb $$ [Hdst Hb] with %n ⟨%Hn, Hdst, Hb⟩
    · iframe
    have hx : xs = [] := List.eq_nil_of_length_eq_zero (by word)
    subst hx
    ispecialize HΦ $$ %ys
    iapply HΦ
    rw [List.take_of_length_le (by omega)]
    simp only [List.length_nil, Nat.zero_add, List.nil_append]
    iframe
    ipureintro
    exact ⟨Hsb, List.Perm.refl _⟩
  have Ha0 := Hif
  wp_if_destruct
  · wp_apply wp_slice_copy dst ds a xs qa $$ [Hdst Ha] with %n ⟨%Hn, Hdst, Ha⟩
    · iframe
    have hy : ys = [] := List.eq_nil_of_length_eq_zero (by word)
    subst hy
    ispecialize HΦ $$ %xs
    iapply HΦ
    rw [List.take_of_length_le (by omega)]
    simp only [List.length_nil, Nat.add_zero, List.append_nil]
    iframe
    ipureintro
    exact ⟨Hsa, List.Perm.refl _⟩
  have Hb0 := Hif
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by decide, by word⟩)]
  wp_auto
  obtain ⟨x0, hx0⟩ : ∃ x0, xs[0]? = some x0 := by
    cases xs with
    | nil => exfalso; apply Ha0; simp at Hal; word
    | cons x0 _ => exact ⟨x0, rfl⟩
  obtain ⟨y0, hy0⟩ : ∃ y0, ys[0]? = some y0 := by
    cases ys with
    | nil => exfalso; apply Hb0; simp at Hbl; word
    | cons y0 _ => exact ⟨y0, rfl⟩
  have hxl : 0 < xs.length := by
    cases xs with
    | nil => simp at hx0
    | cons _ _ => simp
  have hyl : 0 < ys.length := by
    cases ys with
    | nil => simp at hy0
    | cons _ _ => simp
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by word⟩)]
  wp_apply wp_load_slice_index b (sint.Z (W64 0)) ys qb y0 (by decide) $$ [Hb] as Hb
  · iframe; ipureintro; exact hy0
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by word⟩)]
  wp_apply wp_load_slice_index a (sint.Z (W64 0)) xs qa x0 (by decide) $$ [Ha] as Ha
  · iframe; ipureintro; exact hx0
  have hN : sint.Z (a.len + b.len) = sint.Z a.len + sint.Z b.len := by word
  icases (ownSlice_split_all (a.len + b.len) dst _ ds ⟨by word, by word⟩).1 $$ Hdst
    with ⟨Hdst1, Hdst2⟩
  icases (ownSlice_split (W64 0) dst _ _ (W64 0) (a.len + b.len) ⟨by decide, by decide, by word⟩).1
    $$ Hdst1 with ⟨HM, Hjunk⟩
  have h00 : sint.nat (W64 0) - sint.nat (W64 0) = 0 := rfl
  rw [h00, List.take_zero, List.drop_zero]
  wp_if_destruct
  ihave HI : mergeInv dst a b xs ys qa qb lead_ptr follow_ptr merged_ptr $$
      [lead follow merged Ha Hb HM Hjunk]
  · unfold mergeInv
    iexists b, a, W64 0, ys, xs, [], _, qb, qa
    iframe
    isplitl []
    · iintro HL HF; iframe
    ipureintro
    refine ⟨by decide, ?_, ?_, List.Pairwise.nil, Hsb, Hsa, by simp, ?_⟩
    · intro h; simp [h] at hyl
    · intro h; simp [h] at hxl
    · simpa using List.perm_append_comm
  rotate_left
  ihave HI : mergeInv dst a b xs ys qa qb lead_ptr follow_ptr merged_ptr $$
      [lead follow merged Ha Hb HM Hjunk]
  · unfold mergeInv
    iexists a, b, W64 0, xs, ys, [], _, qa, qb
    iframe
    isplitl []
    · iintro HL HF; iframe
    ipureintro
    refine ⟨by decide, ?_, ?_, List.Pairwise.nil, Hsa, Hsb, by simp, by simp⟩
    · intro h; simp [h] at hxl
    · intro h; simp [h] at hyl
  rotate_left
  all_goals
    wp_for HI
    ihave %HLl := ownSlice_len _ _ _ $$ HL
    ihave %HFl := ownSlice_len _ _ _ $$ HF
    ihave %HMl := ownSlice_len _ _ _ $$ HM
    ihave %HJl := ownSlice_len _ _ _ $$ Hjunk
    ihave %HLwf := ownSlice_wf _ _ _ $$ HL
    obtain ⟨Hk, Hls0, Hfs0, Hms, Hls, Hfs, Hle, Hperm⟩ := Hpure
    have Hsum := Hperm.length_eq
    simp only [List.length_append] at Hsum
    rw [slice_prefix_len] at HMl
    simp only [slice.slice] at HJl
    obtain ⟨f0, hf0⟩ : ∃ f0, fs[0]? = some f0 := by
      cases fs with
      | nil => exact absurd rfl Hfs0
      | cons f0 _ => exact ⟨f0, rfl⟩
    have hh0 : fs.head? = some f0 := by rw [List.head?_eq_getElem?]; exact hf0
    have hLpos : 0 < sint.Z L.len := by
      cases ls with
      | nil => exact absurd rfl Hls0
      | cons _ _ => simp at HLl; word
    have hFpos : 0 < sint.Z F.len := by
      cases fs with
      | nil => exact absurd rfl Hfs0
      | cons _ _ => simp at HFl; word
    have hc : decide (sint.Z (W64 0) < sint.Z L.len) = true := by
      simp only [decide_eq_true_eq]; word
    simp only [hc, eq_self, ↓reduceIte]
    wp_auto
    wp_apply sort.wp_Search L.len _ (fun i => decide (uint.Z f0 < uint.Z (ls.getD i.toNat 0)))
      iprop(lead_ptr ↦ L ∗ follow_ptr ↦ F ∗ L ↦*{qL} ls ∗ F ↦*{qF} fs) $$ [lead follow HL HF]
    · iframe
      isplitl []
      · ipureintro; word
      isplitl []
      · unfold sort.predImplements
        iintro %i
        wp_start as ⟨⟨lead, follow, HL, HF⟩, %Hb⟩
        wp_auto
        have hil : (sint.Z i).toNat < ls.length := by rw [HLl.1]; word
        rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hb.1, Hb.2⟩)]
        wp_apply wp_load_slice_index L (sint.Z i) ls qL ls[(sint.Z i).toNat] Hb.1 $$ [HL] as HL
        · iframe; ipureintro; exact List.getElem?_eq_getElem hil
        rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, hFpos⟩)]
        wp_apply wp_load_slice_index F (sint.Z (W64 0)) fs qF f0 (by decide) $$ [HF] as HF
        · iframe; ipureintro; exact hf0
        iapply HΦ
        iframe
        ipureintro
        simp only [getD_of_lt _ hil]
      · ipureintro
        intro i j ⟨hi, hij, hj⟩ hfi
        simp only [decide_eq_true_eq] at hfi ⊢
        have hjl : j.toNat < ls.length := by rw [HLl.1]; word
        rw [getD_of_lt _ (by omega)] at hfi
        rw [getD_of_lt _ hjl]
        exact Int.lt_of_lt_of_le hfi
          (List.pairwise_iff_getElem.mp Hls _ _ (by omega) hjl (by omega))
    iintro %n ⟨⟨lead, follow, HL, HF⟩, %Hn0, %Hfound, %Hoob, %Hgt⟩
    have hnle : sint.Z n ≤ sint.Z L.len := by
      refine Classical.byContradiction fun hcn => ?_
      have := Hoob (fun j hj => Hgt j ⟨hj.1, by omega⟩)
      omega
    have hbelow : ∀ x ∈ ls.take (sint.nat n), uint.Z x ≤ uint.Z f0 := by
      intro x hx
      rw [List.mem_iff_getElem] at hx
      obtain ⟨j, hj, rfl⟩ := hx
      simp only [List.length_take] at hj
      have h1 := Hgt (j : Int) ⟨by omega, by word⟩
      simp only [decide_eq_false_iff_not, Int.not_lt, Int.toNat_natCast] at h1
      rw [getD_of_lt _ (by omega)] at h1
      simpa only [List.getElem_take] using h1
    wp_auto
    have hZ : sint.Z k + sint.Z L.len + sint.Z F.len = sint.Z a.len + sint.Z b.len := by
      have := Hsum; rw [HMl.1, HLl.1, HFl.1, Hal.1, Hbl.1] at this; word
    have hnlen : sint.nat n ≤ ls.length := by rw [HLl.1]; word
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, Hn0, by word⟩)]
    icases (ownSlice_split_all n L qL ls ⟨Hn0, hnle⟩).1 $$ HL with ⟨HL1, HL2⟩
    icases (ownSlice_split (k + n) dst _ junk k (a.len + b.len) ⟨Hk, by word, by word⟩).1 $$ Hjunk
      with ⟨Hj1, Hj2⟩
    wp_apply wp_slice_append_prefix dst k ms _ (slice.slice L w64 (W64 0) n) _ qL n
      (slice_prefix_len L n) Hk (by word) $$ [HM Hj1 HL1] as ⟨HM, HL1⟩
    · iframe
    have Hstep := merge_step (sint.nat n) Hms Hls Hfs Hle hh0 hbelow
    wp_if_destruct
    · -- `break`: all of `lead` went to `merged`; append `follow`
      have hnL : sint.nat n = ls.length := by rw [HLl.1]; word
      rw [hnL, List.take_length, List.drop_length] at Hstep
      rw [hnL, List.take_length, List.drop_length]
      wp_for_post
      have hNe : a.len + b.len = k + n + F.len := by word
      rw [hNe]
      wp_apply wp_slice_append_prefix dst (k + n) (ms ++ ls) _ F fs qF F.len rfl (by word)
        (by word) $$ [HM Hj2 HF] as ⟨HM, HF⟩
      · iframe
      ihave HL := (ownSlice_split_all n L qL ls ⟨Hn0, hnle⟩).2 $$ [HL1 HL2]
      · rw [hnL, List.take_length, List.drop_length]; iframe
      ihave Hab := Hback $$ HL HF
      ihave Hd := ownSlice_combine (k + n + F.len) dst _ (ms ++ ls ++ fs) _ (W64 0) dst.len
        ⟨by simp only [List.length_append]; word, by decide, by word, by word⟩ $$ HM Hdst2
      ihave Hd := ownSlice_trivial_slice_2 $$ Hd
      ispecialize HΦ $$ %(ms ++ ls ++ fs)
      have hd : sint.nat (k + n + F.len) = xs.length + ys.length := by
        rw [← hNe, Hal.1, Hbl.1]; word
      rw [hd]
      iapply HΦ
      iframe
      ipureintro
      exact ⟨merge_done Hms Hls Hfs Hle hh0 (by simpa [hnL] using hbelow), Hperm⟩
    · -- swap: `lead, follow = follow, lead[n:]`
      have hnL : sint.nat n < ls.length := by rw [HLl.1]; word
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hn0, by word, by word⟩)]
      wp_auto
      wp_for_post
      iframe
      unfold mergeInv
      iexists F, slice.slice L w64 n L.len, k + n, fs, ls.drop (sint.nat n),
        ms ++ ls.take (sint.nat n), _, qF, qL
      iframe
      isplitl [Hback HL1]
      · iintro HF HL2
        iapply Hback $$ [HL1 HL2] HF
        iapply (ownSlice_split_all n L qL ls ⟨Hn0, hnle⟩).2
        iframe
      ipureintro
      refine ⟨by word, Hfs0, ?_, Hstep.1, Hfs, (Hls.take_drop _).2.1, Hstep.2, ?_⟩
      · intro h
        have := congrArg List.length h
        simp only [List.length_drop, List.length_nil] at this
        omega
      · refine List.Perm.trans ?_ Hperm
        have e : ms ++ ls ++ fs = ms ++ (ls.take (sint.nat n) ++ ls.drop (sint.nat n)) ++ fs := by
          rw [List.take_append_drop]
        rw [e]
        simp only [List.append_assoc]
        exact List.Perm.append_left _ (List.Perm.append_left _ List.perm_append_comm)

end proof

end bbolt
end EtcdGrove
end Perennial
