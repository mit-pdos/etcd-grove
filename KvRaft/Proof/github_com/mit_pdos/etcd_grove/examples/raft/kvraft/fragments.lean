/-
The proof of `KvRaft/Spec/.../kvraft/fragments.lean` (kvraft-udp, phase 2: `notes/kvraft-udp-proof-plan.md`).
-/
module

public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.fragments
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.putFragment
public import Perennial.Proof.bytes.BufferBasics

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI Iris.ProofMode Net Udp go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]

/-- The chunk `fragments` slices out is `chunkAt`'s. -/
private theorem chunk_sub (bs : List w8) (i e : Nat) (he : e = min ((i + 1) * chunkSizeN) bs.length) :
    subslice (i * chunkSizeN) e bs = chunkAt bs i := by
  subst he
  unfold subslice chunkAt chunkSizeN
  rw [List.drop_take]
  by_cases h : (i + 1) * 479 ≤ bs.length
  · rw [Nat.min_eq_left h, show (i + 1) * 479 - i * 479 = 479 by omega]
  · rw [Nat.min_eq_right (by omega), List.take_of_length_le (by simp only [List.length_drop]; omega),
      List.take_of_length_le (by simp only [List.length_drop]; omega)]

/-- The `k`-th fragment of a body cut into `n` chunks. -/
private theorem fragsOf_get (src dst boot seq : w64) (bs : List w8) (k : Nat)
    (hn : ¬(nChunks bs = 0 ∨ maxFragmentsN < nChunks bs)) (hk : k < nChunks bs) :
    (fragsOf src dst boot seq bs)[k]? = some (fragBytes src dst boot seq (W32 (k : Int))
      (W32 ((nChunks bs : Nat) : Int)) (chunkAt bs k)) := by
  unfold fragsOf
  rw [if_neg hn, List.getElem?_map, List.getElem?_range hk]
  rfl

private theorem fragsOf_len (src dst boot seq : w64) (bs : List w8)
    (hn : ¬(nChunks bs = 0 ∨ maxFragmentsN < nChunks bs)) :
    (fragsOf src dst boot seq bs).length = nChunks bs := by
  unfold fragsOf
  rw [if_neg hn, List.length_map, List.length_range]

set_option hygiene false in
/-- `fragments`' loop body after `end` is set to `ev` (`hev`: `min((i+1)*chunkSize, len(body))`):
the chunk sliced, its fragment appended to `ds`. -/
local macro "frag_step " ev:term : tactic => `(tactic| (
  have hlo : sint.Z (iw * W64 479) = ((uint.nat iw * 479 : Nat) : Int) := by word
  have hlon : sint.nat (iw * W64 479) = uint.nat iw * chunkSizeN := by unfold chunkSizeN; word
  have Hcap : sint.Z body.len ≤ sint.Z body.cap := Hwf.2
  have Hrng : 0 ≤ sint.Z (iw * W64 479) ∧ sint.Z (iw * W64 479) ≤ sint.Z $ev ∧ sint.Z $ev ≤ sint.Z body.len := by
    rw [hlo, hevZ]; refine ⟨by omega, by omega, by omega⟩
  rw [if_pos ⟨Hrng.1, Hrng.2.1, Int.le_trans Hrng.2.2 Hcap⟩]
  icases (ownSlice_slice (GF := GF) (V := w8) (iw * W64 479) $ev body q bs Hrng).1 $$ Hb with ⟨Hb1, Hb2, Hb3⟩
  wp_apply wp_putFragment src dst boot seq (W32 (uint.Z iw)) (W32 (uint.Z nw)) _ q _ $$ [Hb2]
    as %f ⟨Hf, -, Hb2⟩
  · iframe
  ihave Hb := (ownSlice_slice (GF := GF) (V := w8) (iw * W64 479) $ev body q bs Hrng).2 $$ [Hb1 Hb2 Hb3]
  · iframe
  wp_apply wp_slice_literal (V := GoSlice) (t := go.GoType.SliceType go.byte) [f]
  isplitr
  · ipureintro; rfl
  iintro %lsl ⟨Hl, -⟩
  try wp_auto
  wp_apply wp_slice_append dsv dsl _ [f] (DFrac.own 1) $$ [Hds Hdc Hl] as %dsv' ⟨Hds, Hdc, -⟩
  · iframe
  try wp_auto
  ihave %Hdl' := ownSlice_len _ _ _ $$ Hds
  wp_for_post
  iframe
  iexists iw + W64 1, dsv', dsl ++ [f]
  iframe i ds Hb Hds Hdc
  have hW1 : W32 (uint.Z iw) = W32 ((uint.nat iw : Nat) : Int) := by
    rw [show ((uint.nat iw : Nat) : Int) = uint.Z iw by word]
  have hW2 : W32 (uint.Z nw) = W32 ((nChunks bs : Nat) : Int) := by
    rw [← hnw, show ((uint.nat nw : Nat) : Int) = uint.Z nw by word]
  have hch : subslice (sint.nat (iw * W64 479)) (sint.nat $ev) bs = chunkAt bs (uint.nat iw) := by
    rw [hlon]; exact chunk_sub bs _ _ hev
  have hiw1 : uint.nat (iw + W64 1) = uint.nat iw + 1 := by word
  isplitl [Hfr Hf]
  · iapply BigSepL.bigSepL_snoc.2
    iframe Hfr
    iexists _
    iframe Hf
    ipureintro
    rw [Hdl, fragsOf_get src dst boot seq bs (uint.nat iw) hn hi, hW1, hW2, hch]
  · ipureintro
    refine ⟨by rw [List.length_append, List.length_singleton, Hdl, hiw1], by omega, ?_⟩
    intro _ h
    rw [h] at Hdl'
    have h0 : sint.nat (slice.nil : GoSlice).len = 0 := rfl
    simp only [List.length_append, List.length_singleton] at Hdl'
    omega))

theorem fragments.wp_proof
    (wp_putFragment : putFragment.spec (GF := GF) (hG := hG)) :
    fragments.spec (GF := GF) (hG := hG) := by
  intro src dst boot seq body q bs Hbl
  wp_start as Hb
  ihave %Hlen := ownSlice_len _ _ _ $$ Hb
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hb
  ihave %Hmax := bytes.ownSlice_bytes_len_le _ _ _ $$ Hb
  unfold maxAddr at Hmax
  have HL : bs.length ≤ 2 ^ 47 := by have := Hlen.1; word
  have HLz : uint.Z body.len = bs.length := by have := Hlen.1; word
  have HLs : sint.Z body.len = (bs.length : Int) := by have := Hlen.1; word
  try wp_auto
  have h1 : uint.nat (body.len + W64 479 - W64 1) = bs.length + 478 := by word
  have hnw : uint.nat ((body.len + W64 479 - W64 1) / W64 479) = nChunks bs := by
    unfold nChunks chunkSizeN
    first | word | (rw [BitVec.toNat_udiv, h1]; rfl)
  generalize (body.len + W64 479 - W64 1) / W64 479 = nw at *
  wp_if_destruct
  · have hz : nChunks bs = 0 := by rw [← hnw]; rfl
    have hF : fragsOf src dst boot seq bs = [] := by unfold fragsOf; rw [if_pos (Or.inl hz)]
    iapply HΦ
    iframe Hb
    isplitr
    · ipureintro; exact ⟨fun _ => hF, fun _ => rfl⟩
    iexists []
    rw [hF]
    isplitl []
    · iapply ownSlice_nil
    isplitr
    · ipureintro; rfl
    iapply BigSepL.bigSepL_nil.2; iempintro
  have hN1 : 1 ≤ nChunks bs := by
    have : uint.nat nw ≠ 0 := fun h => Hif (by word)
    omega
  wp_if_destruct
  · have hbig : maxFragmentsN < nChunks bs := by unfold maxFragmentsN; rw [← hnw]; word
    have hF : fragsOf src dst boot seq bs = [] := by unfold fragsOf; rw [if_pos (Or.inr hbig)]
    try wp_auto
    iapply HΦ
    iframe Hb
    isplitr
    · ipureintro; exact ⟨fun _ => hF, fun _ => rfl⟩
    iexists []
    rw [hF]
    isplitl []
    · iapply ownSlice_nil
    isplitr
    · ipureintro; rfl
    iapply BigSepL.bigSepL_nil.2; iempintro
  have hNm : nChunks bs ≤ 16384 := by rw [← hnw]; word
  have hn : ¬(nChunks bs = 0 ∨ maxFragmentsN < nChunks bs) := by unfold maxFragmentsN; omega
  try wp_auto
  ihave HI : (∃ (iw : w64) (dsv : GoSlice) (dsl : List GoSlice),
      "i" ∷ i_ptr ↦ iw ∗ "ds" ∷ ds_ptr ↦ dsv ∗ "Hb" ∷ body ↦*{q} bs ∗
      "Hds" ∷ dsv ↦* dsl ∗ "Hdc" ∷ ownSliceCap GoSlice dsv (DFrac.own 1) ∗
      "Hfr" ∷ ([∗list] k ↦ d ∈ dsl, ∃ x, ⌜(fragsOf src dst boot seq bs)[k]? = some x⌝ ∗ d ↦* x) ∗
      "%Hinv" ∷ ⌜dsl.length = uint.nat iw ∧ uint.nat iw ≤ nChunks bs ∧
        (1 ≤ uint.nat iw → dsv ≠ slice.nil)⌝ : IProp GF) $$ [i ds Hb]
  · iexists W64 0, _, []
    iframe
    isplitl []
    · iapply ownSlice_nil
    isplitl []
    · iapply ownSliceCap_nil
    isplitl []
    · iapply BigSepL.bigSepL_nil.2; iempintro
    ipureintro
    exact ⟨rfl, Nat.zero_le _, fun h => absurd h (by decide)⟩
  irename «from» => Hfromv
  wp_for HI
  wp_if_destruct
  · obtain ⟨Hdl, Hile, Hnn⟩ := Hinv
    have hi : uint.nat iw < nChunks bs := by rw [← hnw]; word
    try wp_auto
    have hi' : (uint.nat iw + 1) * 479 ≤ nChunks bs * 479 := by
      have := Nat.mul_le_mul_right 479 (show uint.nat iw + 1 ≤ nChunks bs by omega); omega
    have hNL : nChunks bs * 479 < bs.length + 479 := by
      have h := Nat.div_mul_le_self (bs.length + chunkSizeN - 1) chunkSizeN
      have e : nChunks bs = (bs.length + chunkSizeN - 1) / chunkSizeN := rfl
      rw [e]
      rw [show chunkSizeN = 479 from rfl] at h ⊢
      omega
    have hNL' : uint.nat iw * 479 < bs.length := by
      have h2 : (uint.nat iw + 1) * 479 < bs.length + 479 := Nat.lt_of_le_of_lt hi' hNL
      rw [Nat.succ_mul] at h2
      exact Nat.lt_of_add_lt_add_right h2
    wp_if_destruct
    · have hgt : bs.length < (uint.nat iw + 1) * 479 := by word
      have hev : sint.nat body.len = min ((uint.nat iw + 1) * chunkSizeN) bs.length := by
        unfold chunkSizeN; rw [Nat.min_eq_right (by omega)]; word
      have hevZ : sint.Z body.len = ((min ((uint.nat iw + 1) * 479) bs.length : Nat) : Int) := by
        rw [Nat.min_eq_right (by omega)]; word
      try wp_auto
      frag_step body.len
    · have hle : (uint.nat iw + 1) * 479 ≤ bs.length := by word
      have hev : sint.nat ((iw + W64 1) * W64 479) = min ((uint.nat iw + 1) * chunkSizeN) bs.length := by
        unfold chunkSizeN; rw [Nat.min_eq_left hle]; word
      have hevZ : sint.Z ((iw + W64 1) * W64 479) = ((min ((uint.nat iw + 1) * 479) bs.length : Nat) : Int) := by
        rw [Nat.min_eq_left hle]; word
      try wp_auto
      frag_step ((iw + W64 1) * W64 479)
  · obtain ⟨Hdl, Hile, Hnn⟩ := Hinv
    have hiw : uint.nat iw = nChunks bs := by rw [← hnw] at Hile ⊢; word
    try wp_auto
    iapply HΦ
    iframe Hb
    have hFne : fragsOf src dst boot seq bs ≠ [] := by
      intro h
      rcases (fragsOf_nil src dst boot seq bs).1 h with h | h
      · subst h; exact absurd hN1 (by decide)
      · unfold maxFragmentsN at h; omega
    isplitr
    · ipureintro; exact ⟨fun h => absurd h (Hnn (by omega)), fun h => absurd h hFne⟩
    iexists dsl
    iframe Hds Hfr
    ipureintro
    rw [fragsOf_len src dst boot seq bs hn]; omega

end proof

end kvraft
end EtcdGrove
end Perennial
