/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvdurable/image__append.lean`. Lean-first
(no Rocq counterpart): no entries, or all at or below the log's start, change nothing; otherwise
the entries at or below the start are sliced off (the slice's ownership split around the kept part,
`ownSlice_slice`, and joined back after), and the log's entries before the first kept one are copied
into a new slice with the kept entries after them (two `append`s), frozen read-only.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.image__append
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetIndex
public import Proof.go_etcd_io.raft.v3.LemmasEnts

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

private theorem sint_nat_of_small (x : w64) (h : uint.nat x < 2 ^ 63) : sint.nat x = uint.nat x := by
  word

theorem image.append.wp_proof (wp_GetIndex : raftpb.Entry.GetIndex.spec (GF := GF) (hG := hG)) :
    image.append.spec (GF := GF) (hG := hG) := by
  intro p I s dq k es Hidx Hk Hb
  wp_start as ⟨Himg, Hs⟩
  iunfold ownImage at Himg
  icases Himg with ⟨%hsp, %sp, %ie, Himg⟩
  iNamed Himg
  ihave %Hilen := entsPts_len $$ HentsO
  iunfold entsPts at Hs
  icases Hs with ⟨%lsb, Hsb, #Hbigb⟩
  ihave %Hblen := entsBig_length $$ Hbigb
  ihave %Hslen := ownSlice_len $$ Hsb
  -- the image back unchanged, and the entries
  ihave Hsame : (p.[KImage, go!"hs"] ↦ hsp -∗ p.[KImage, go!"snap"] ↦ sp -∗
      p.[KImage, go!"prev"] ↦ I.prev -∗ p.[KImage, go!"prevTerm"] ↦ I.prevTerm -∗
      p.[KImage, go!"ents"] ↦ ie -∗ ownImage p I) $$ []
  · iintro Hhs Hsnap Hprev HprevTerm Hents
    iunfold ownImage
    iexists hsp, sp, ie
    iframe # ∗
    ipureintro; exact Hwf
  wp_auto
  wp_if_destruct
  · -- no entries
    have Hnil : es = [] := by
      apply List.length_eq_zero_iff.1; rw [← Hblen, Hslen.1, Hif]; rfl
    iapply HΦ
    rw [show imgAppend I k es = I by simp [imgAppend, Hnil]]
    isplitr [Hsb]
    · iapply Hsame $$ Hhs Hsnap Hprev HprevTerm Hents
    iunfold entsPts
    iexists lsb
    iframe Hsb Hbigb
  obtain ⟨e0, rest, rfl⟩ : ∃ e0 rest, es = e0 :: rest := by
    cases es with
    | nil => exfalso; apply Hif; simp only [List.length_nil] at Hblen; word
    | cons a b => exact ⟨a, b, rfl⟩
  have Hk0 : uint.nat e0.Index' = k := by simpa using Hidx 0 e0 rfl
  have Hk' := Hk (List.cons_ne_nil e0 rest)
  simp only [List.length_cons] at Hb Hblen
  icases entsBig_lookup lsb (e0 :: rest) 0 e0 rfl $$ Hbigb with ⟨%lb0, %Hlb0, #Heb0⟩
  have Hlenz : uint.Z s.len = (rest.length : Int) + 1 := by
    have := Hslen.1; rw [Hblen] at this; word
  rw [ite_eq_left ⟨by word, by word⟩]
  wp_apply wp_load_slice_index s (sint.Z (W64 0)) lsb dq lb0 (by word) $$ [Hsb] as Hsb
  · iframe Hsb; ipureintro; exact Hlb0
  wp_apply wp_GetIndex.1 lb0 DFrac.discard e0 $$ [Heb0] with -
  · iframe Heb0
  wp_if_destruct
  · -- all at or below the log's start
    iapply HΦ
    rw [show imgAppend I k (e0 :: rest) = I by
      simp only [imgAppend, List.length_cons]; rw [ite_eq_left (Or.inr (by word))]]
    isplitr [Hsb]
    · iapply Hsame $$ Hhs Hsnap Hprev HprevTerm Hents
    iunfold entsPts
    iexists lsb
    iframe Hsb Hbigb
  have Habove : uint.nat I.prev + 1 < k + (rest.length + 1) := by word
  ihave %Hwfs := ownSlice_wf $$ Hsb
  -- the number of entries at or below the log's start, sliced off (the two ways meet with `skip`
  -- at it)
  rw [ite_eq_left ⟨by word, by word⟩]
  wp_apply wp_load_slice_index s (sint.Z (W64 0)) lsb dq lb0 (by word) $$ [Hsb] as Hsb
  · iframe Hsb; ipureintro; exact Hlb0
  wp_apply wp_GetIndex.1 lb0 DFrac.discard e0 $$ [Heb0] with -
  · iframe Heb0
  have Hd : (uint.nat I.prev + 1 - k) ≤ rest.length := by omega
  ihave Hbig2 := entsBig_drop (uint.nat I.prev + 1 - k) lsb (e0 :: rest) $$ Hbigb
  -- (the two ways meet at the kept entries' slice, `s2`, from `skip`, at `lo`)
  wp_if_destruct
  -- some at or below the start
  rw [ite_eq_left ⟨by word, by word⟩]
  wp_apply wp_load_slice_index s (sint.Z (W64 0)) lsb dq lb0 (by word) $$ [Hsb] as Hsb
  · iframe Hsb; ipureintro; exact Hlb0
  wp_apply wp_GetIndex.1 lb0 DFrac.discard e0 $$ [Heb0] with -
  · iframe Heb0
  try wp_auto
  have Hlo : sint.nat (I.prev + W64 1 - e0.Index') = uint.nat I.prev + 1 - k := by word
  rw [ite_eq_left ⟨by word, by word, Hwfs.2⟩]
  icases (ownSlice_slice (I.prev + W64 1 - e0.Index') s.len s dq lsb
    ⟨by word, by word, by word⟩).1 $$ Hsb with ⟨HA, HB, HC⟩
  ihave Hback : (slice.slice s Loc (I.prev + W64 1 - e0.Index') s.len ↦*{dq}
      lsb.drop (uint.nat I.prev + 1 - k) -∗ s ↦*{dq} lsb) $$ [HA HC]
  · iintro HB
    iapply (ownSlice_slice (I.prev + W64 1 - e0.Index') s.len s dq lsb
      ⟨by word, by word, by word⟩).2
    iframe HA HC
    have HE : subslice (sint.nat (I.prev + W64 1 - e0.Index')) (sint.nat s.len) lsb =
        lsb.drop (uint.nat I.prev + 1 - k) := by
      simp only [subslice]
      rw [List.take_of_length_le (by word), Hlo]
    rw [HE]; iexact HB
  ihave HB : slice.slice s Loc (I.prev + W64 1 - e0.Index') s.len ↦*{dq}
      lsb.drop (uint.nat I.prev + 1 - k) $$ [HB]
  · have HE : subslice (sint.nat (I.prev + W64 1 - e0.Index')) (sint.nat s.len) lsb =
        lsb.drop (uint.nat I.prev + 1 - k) := by
      simp only [subslice]
      rw [List.take_of_length_le (by word), Hlo]
    rw [← HE]; iexact HB
  generalize slice.slice s Loc (I.prev + W64 1 - e0.Index') s.len = s2
  rotate_left
  -- none
  have Hlo : sint.nat (W64 0) = uint.nat I.prev + 1 - k := by word
  rw [ite_eq_left ⟨by word, by word, Hwfs.2⟩]
  icases (ownSlice_slice (W64 0) s.len s dq lsb ⟨by word, by word, by word⟩).1 $$ Hsb
    with ⟨HA, HB, HC⟩
  ihave Hback : (slice.slice s Loc (W64 0) s.len ↦*{dq}
      lsb.drop (uint.nat I.prev + 1 - k) -∗ s ↦*{dq} lsb) $$ [HA HC]
  · iintro HB
    iapply (ownSlice_slice (W64 0) s.len s dq lsb ⟨by word, by word, by word⟩).2
    iframe HA HC
    have HE : subslice (sint.nat (W64 0)) (sint.nat s.len) lsb =
        lsb.drop (uint.nat I.prev + 1 - k) := by
      simp only [subslice]
      rw [List.take_of_length_le (by word), Hlo]
    rw [HE]; iexact HB
  ihave HB : slice.slice s Loc (W64 0) s.len ↦*{dq} lsb.drop (uint.nat I.prev + 1 - k) $$ [HB]
  · have HE : subslice (sint.nat (W64 0)) (sint.nat s.len) lsb =
        lsb.drop (uint.nat I.prev + 1 - k) := by
      simp only [subslice]
      rw [List.take_of_length_le (by word), Hlo]
    rw [← HE]; iexact HB
  generalize slice.slice s Loc (W64 0) s.len = s2
  all_goals
    -- the first kept entry, at `max k (prev + 1)`
    ihave %Hs2len := ownSlice_len $$ HB
    obtain ⟨e1, He1⟩ : ∃ e1, (e0 :: rest)[uint.nat I.prev + 1 - k]? = some e1 :=
      ⟨_, List.getElem?_eq_getElem (by simp only [List.length_cons]; omega)⟩
    have He1i : uint.nat e1.Index' = k + (uint.nat I.prev + 1 - k) := Hidx _ _ He1
    have He1' : ((e0 :: rest).drop (uint.nat I.prev + 1 - k))[0]? = some e1 := by
      rw [List.getElem?_drop]; simpa using He1
    icases entsBig_lookup _ _ 0 e1 He1' $$ Hbig2 with ⟨%lb1, %Hlb1, #Heb1⟩
    have Hs2z : 0 < sint.Z s2.len := by
      have := Hs2len.1; simp only [List.length_drop] at this; word
    wp_auto
    rw [ite_eq_left ⟨by word, by word⟩]
    wp_apply wp_load_slice_index s2 (sint.Z (W64 0)) _ dq lb1 (by word) $$ [HB] as HB
    · iframe HB; ipureintro; exact Hlb1
    wp_apply wp_GetIndex.1 lb1 DFrac.discard e1 $$ [Heb1] with -
    · iframe Heb1
    have Hoff : uint.nat (e1.Index' - (I.prev + W64 1)) = k - (uint.nat I.prev + 1) := by word
    wp_if_destruct
    · exfalso; word
    -- the log's entries before the first kept one, copied, then the kept ones
    ihave #HentsO' := HentsO
    iunfold entsRO at HentsO'
    iunfold entsPts at HentsO'
    icases HentsO' with ⟨%lsI, #HlsI, #HbigI⟩
    ihave %HbI := entsBig_length $$ HbigI
    ihave %HwfI := ownSlice_wf $$ HlsI
    rw [ite_eq_left ⟨by word, by word, by word⟩]
    icases (ownSlice_slice (W64 0) (e1.Index' - (I.prev + W64 1)) ie DFrac.discard lsI
      ⟨by word, by word, by word⟩).1 $$ HlsI with ⟨-, #Hpre, -⟩
    ihave Hnil : (slice.nil ↦* ([] : List Loc) : IProp GF) $$ []
    · iapply ownSlice_nil
    ihave Hnilc := ownSliceCap_nil (GF := GF) (V := Loc)
    wp_apply wp_slice_append (V := Loc) slice.nil [] _ _ DFrac.discard $$ [$Hnil $Hnilc $Hpre]
      as %s3 ⟨Hs3, Hs3c, -⟩
    wp_apply +noauto wp_slice_append (V := Loc) s3 _ s2 _ dq $$ [$Hs3 $Hs3c $HB]
      as %s4 ⟨Hs4, -, HB⟩
    imod ownSlice_persist $$ Hs4 with #Hs4
    wp_auto
    iapply HΦ
    have Hne : ¬ (e0 :: rest = [] ∨ k + (e0 :: rest).length ≤ uint.nat I.prev + 1) := by
      rintro (h | h)
      · exact List.cons_ne_nil _ _ h
      · simp only [List.length_cons] at h; omega
    have Hsubeq : subslice 0 (sint.nat (e1.Index' - (I.prev + W64 1))) lsI =
        lsI.take (k - (uint.nat I.prev + 1)) := by
      simp only [subslice, List.drop_zero]
      rw [sint_nat_of_small _ (by rw [Hoff]; omega), Hoff]
    simp only [imgAppend]
    rw [ite_eq_right Hne]
    isplitr [HB Hback]
    · iunfold ownImage
      iexists hsp, sp, s4
      iframe # ∗
      isplitr
      · iunfold entsRO; iunfold entsPts
        iexists _
        isplitr
        · iexact Hs4
        rw [List.nil_append, Hsubeq]
        ihave #Ht := entsBig_take (k - (uint.nat I.prev + 1)) lsI I.ents $$ HbigI
        iapply entsBig_app $$ [Ht Hbig2]
        iframe Ht Hbig2
      ipureintro
      have h1 := List.length_take_le (k - (uint.nat I.prev + 1)) I.ents
      simp only [List.length_append, List.length_drop, List.length_cons]
      omega
    iunfold entsPts
    iexists lsb
    iframe Hbigb
    iapply Hback $$ HB

end proof

end kvdurable
end EtcdGrove
end Perennial
