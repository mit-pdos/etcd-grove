/-
The proof of `KvNet/Spec/.../kvnet/getDatagram.lean` (kvudp, phase 2: `notes/kvudp-proof-plan.md`).
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.getDatagram
public import Perennial.Proof.bytes.BufferBasics

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Iris.ProofMode Net Udp go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [HasExt udpExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [net_sem : net.Assumptions] [net_udp_sem : net.UdpFieldAssumptions]

/-- `b[off:]`, `k` bytes at its front, with the way back. -/
private theorem slice_at (b : GoSlice) (q : DFrac) (bs : List w8) (off : w64) (o k : Nat)
    (ho : sint.nat off = o) (h0 : 0 ≤ sint.Z off) (hlen : bs.length = sint.nat b.len)
    (hb : 0 ≤ sint.Z b.len) (hoff : o + k ≤ bs.length) :
    (b ↦*{q} bs : IProp GF) ⊢
      slice.slice b w8 off b.len ↦*{q} ((bs.drop o).take k ++ bs.drop (o + k)) ∗
      (slice.slice b w8 off b.len ↦*{q} ((bs.drop o).take k ++ bs.drop (o + k)) -∗ b ↦*{q} bs) := by
  subst ho
  have Hrng : 0 ≤ sint.Z off ∧ sint.Z off ≤ sint.Z b.len ∧ sint.Z b.len ≤ sint.Z b.len := by
    refine ⟨h0, ?_, Int.le_refl _⟩; word
  have E := ownSlice_slice (GF := GF) (V := w8) off b.len b q bs Hrng
  have Hsub : subslice (sint.nat off) (sint.nat b.len) bs =
      (bs.drop (sint.nat off)).take k ++ bs.drop (sint.nat off + k) := by
    have hd : (bs.drop (sint.nat off)).drop k = bs.drop (sint.nat off + k) := by
      simp only [List.drop_drop, Nat.add_comm]
    rw [← hlen]
    simp only [subslice, List.take_length]
    rw [← hd, List.take_append_drop]
  rw [Hsub] at E
  iintro Hb
  ihave H := E.1 $$ Hb
  icases H with ⟨Hb1, Hb2, Hb3⟩
  iframe Hb2
  iintro Hb2
  iapply E.2
  iframe

theorem getDatagram.wp_proof :
    getDatagram.spec (GF := GF) (hG := hG) := by
  intro b q bs
  wp_start as Hb
  ihave %Hlen := ownSlice_len _ _ _ $$ Hb
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hb
  ihave %Hmax := bytes.ownSlice_bytes_len_le _ _ _ $$ Hb
  unfold maxAddr at Hmax
  have HLz : sint.Z b.len = bs.length := by have := Hlen.1; word
  try wp_auto
  icases typedPointsto_not_null_dup _ _ _ $$ d with ⟨d, %Hdnn⟩
  by_cases hshort : bs.length < 37
  · have hnone : parseDg bs = none := by
      unfold parseDg; rw [if_pos (Or.inl (show bs.length < ackLenN from hshort))]
    rw [decide_eq_true (show sint.Z b.len < sint.Z (W64 37) by
      rw [HLz, show sint.Z (W64 37) = 37 from rfl]; omega)]
    try wp_auto
    iapply HΦ
    iframe Hb
    rw [hnone]
    ipureintro; rfl
  rw [decide_eq_false (show ¬ sint.Z b.len < sint.Z (W64 37) by
    rw [HLz, show sint.Z (W64 37) = 37 from rfl]; omega)]
  try wp_auto
  have E4 : (b ↦*{q} bs : IProp GF) ⊣⊢ b ↦*{q} (bs.take 4 ++ bs.drop 4) := by
    rw [List.take_append_drop]; exact .rfl
  ihave Hb := E4.1 $$ Hb
  wp_apply encoding.binary.wp_LittleEndian_Uint32 b (bs.take 4) q (bs.drop 4) (by simp; omega)
    $$ [$Hb] as Hb
  ihave Hb := E4.2 $$ Hb
  have hm0 : leToU32 (bs.take 4) = u32At bs 0 := by simp [u32At]
  rw [hm0]
  try wp_auto
  by_cases hmag' : u32At bs 0 ≠ udpMagicW
  · have hmag := hmag'
    have hnone : parseDg bs = none := by unfold parseDg; rw [if_pos (Or.inr hmag)]
    rw [decide_eq_false (show ¬ u32At bs 0 = W32 1146443339 from hmag)]
    try wp_auto
    iapply HΦ
    iframe Hb
    rw [hnone]
    ipureintro; rfl
  have hmag : u32At bs 0 = udpMagicW := Classical.not_not.mp hmag'
  rw [decide_eq_true (show u32At bs 0 = W32 1146443339 from hmag)]
  try wp_auto
  obtain ⟨x4, hx4⟩ : ∃ x, bs[4]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have Hbnd : 0 ≤ sint.Z (W64 4) ∧ sint.Z (W64 4) < sint.Z b.len := by
    rw [HLz]; constructor <;> word
  try simp only [Hbnd, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index b (sint.Z (W64 4)) _ q x4 (by decide) $$ [Hb] as Hb
  · iframe Hb; ipureintro; exact hx4
  try wp_auto
  have hgetD : bs.getD 4 0 = x4 := by rw [List.getD_eq_getElem?_getD, hx4]; rfl
  have HLc : sint.Z b.len ≤ sint.Z b.cap := Hwf.2
  rw [if_pos ⟨by decide, by rw [HLz, show sint.Z (W64 5) = 5 from rfl]; omega, HLc⟩]
  icases slice_at (GF := GF) b q bs (W64 5) 5 8 rfl (by decide) Hlen.1 Hlen.2 (by omega) $$ Hb
    with ⟨Hs, Hback⟩
  wp_apply encoding.binary.wp_LittleEndian_Uint64 _ ((bs.drop 5).take 8) q
    (bs.drop (5 + 8))
    (by simp only [List.length_take, List.length_drop]; omega) $$ [Hs] as Hs
  · iframe
  ihave Hb := Hback $$ Hs
  try wp_auto
  rw [if_pos ⟨by decide, by rw [HLz, show sint.Z (W64 13) = 13 from rfl]; omega, HLc⟩]
  icases slice_at (GF := GF) b q bs (W64 13) 13 8 rfl (by decide) Hlen.1 Hlen.2 (by omega) $$ Hb
    with ⟨Hs, Hback⟩
  wp_apply encoding.binary.wp_LittleEndian_Uint64 _ ((bs.drop 13).take 8) q
    (bs.drop (13 + 8))
    (by simp only [List.length_take, List.length_drop]; omega) $$ [Hs] as Hs
  · iframe
  ihave Hb := Hback $$ Hs
  try wp_auto
  rw [if_pos ⟨by decide, by rw [HLz, show sint.Z (W64 21) = 21 from rfl]; omega, HLc⟩]
  icases slice_at (GF := GF) b q bs (W64 21) 21 8 rfl (by decide) Hlen.1 Hlen.2 (by omega) $$ Hb
    with ⟨Hs, Hback⟩
  wp_apply encoding.binary.wp_LittleEndian_Uint64 _ ((bs.drop 21).take 8) q
    (bs.drop (21 + 8))
    (by simp only [List.length_take, List.length_drop]; omega) $$ [Hs] as Hs
  · iframe
  ihave Hb := Hback $$ Hs
  try wp_auto
  rw [if_pos ⟨by decide, by rw [HLz, show sint.Z (W64 29) = 29 from rfl]; omega, HLc⟩]
  icases slice_at (GF := GF) b q bs (W64 29) 29 8 rfl (by decide) Hlen.1 Hlen.2 (by omega) $$ Hb
    with ⟨Hs, Hback⟩
  wp_apply encoding.binary.wp_LittleEndian_Uint64 _ ((bs.drop 29).take 8) q
    (bs.drop (29 + 8))
    (by simp only [List.length_take, List.length_drop]; omega) $$ [Hs] as Hs
  · iframe
  ihave Hb := Hback $$ Hs
  try wp_auto
  have h1 : ¬(bs.length < ackLenN ∨ u32At bs 0 ≠ udpMagicW) := by
    simp only [ackLenN, ne_eq, not_or, Decidable.not_not]; exact ⟨hshort, hmag⟩
  have hP : parseDg bs = (if x4 = kindAckB then
        (if bs.length = ackLenN then some ⟨x4, u64At bs 5, u64At bs 13, u64At bs 21, u64At bs 29, 0, 0, []⟩
          else none)
      else if x4 ≠ kindFragmentB ∨ bs.length ≤ fragHeaderLenN ∨ fragHeaderLenN + chunkSizeN < bs.length
        then none
      else if (u32At bs 41).toNat = 0 ∨ maxFragmentsN < (u32At bs 41).toNat ∨
          (u32At bs 41).toNat ≤ (u32At bs 37).toNat then none
      else some ⟨x4, u64At bs 5, u64At bs 13, u64At bs 21, u64At bs 29, u32At bs 37, u32At bs 41,
        bs.drop fragHeaderLenN⟩) := by
    unfold parseDg
    rw [if_neg h1]
    simp only [hgetD]
    rfl
  by_cases hk : x4 = kindAckB
  · rw [decide_eq_true (show x4 = W8 2 from hk)]
    try wp_auto
    iapply HΦ
    iframe Hb
    rw [hP, if_pos hk]
    by_cases hl : bs.length = 37
    · rw [if_pos (show bs.length = ackLenN from hl),
        decide_eq_true (show b.len = W64 37 by word)]
      unfold dgOwn
      isplitr
      · ipureintro; rfl
      isplitr
      · ipureintro; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      iapply ownSlice_nil
    · rw [if_neg (show ¬ bs.length = ackLenN from hl),
        decide_eq_false (show ¬ b.len = W64 37 by
          intro h; apply hl; rw [h, show sint.Z (W64 37) = 37 from rfl] at HLz; omega)]
      ipureintro; rfl
  rw [decide_eq_false (show ¬ x4 = W8 2 from hk)]
  rw [if_neg hk] at hP
  try wp_auto
  by_cases hkf' : x4 ≠ kindFragmentB
  · rw [decide_eq_false (show ¬ x4 = W8 1 from hkf')]
    have hnone : parseDg bs = none := by rw [hP, if_pos (Or.inl hkf')]
    try wp_auto
    iapply HΦ
    iframe Hb
    rw [hnone]
    ipureintro; rfl
  have hkf : x4 = kindFragmentB := Classical.not_not.mp hkf'
  rw [decide_eq_true (show x4 = W8 1 from hkf)]
  try wp_auto
  by_cases hle : bs.length ≤ 45
  · rw [decide_eq_true (show sint.Z b.len ≤ sint.Z (W64 45) by
      rw [HLz, show sint.Z (W64 45) = 45 from rfl]; omega)]
    have hnone : parseDg bs = none := by
      rw [hP, if_pos (Or.inr (Or.inl (show bs.length ≤ fragHeaderLenN from hle)))]
    try wp_auto
    iapply HΦ
    iframe Hb
    rw [hnone]
    ipureintro; rfl
  rw [decide_eq_false (show ¬ sint.Z b.len ≤ sint.Z (W64 45) by
    rw [HLz, show sint.Z (W64 45) = 45 from rfl]; omega)]
  try wp_auto
  by_cases hgt : 524 < bs.length
  · rw [decide_eq_true (show sint.Z (W64 524) < sint.Z b.len by
      rw [HLz, show sint.Z (W64 524) = 524 from rfl]; omega)]
    have hnone : parseDg bs = none := by
      rw [hP, if_pos (Or.inr (Or.inr (show fragHeaderLenN + chunkSizeN < bs.length from hgt)))]
    try wp_auto
    iapply HΦ
    iframe Hb
    rw [hnone]
    ipureintro; rfl
  rw [decide_eq_false (show ¬ sint.Z (W64 524) < sint.Z b.len by
    rw [HLz, show sint.Z (W64 524) = 524 from rfl]; omega)]
  have hc1 : ¬(x4 ≠ kindFragmentB ∨ bs.length ≤ fragHeaderLenN ∨ fragHeaderLenN + chunkSizeN < bs.length) := by
    intro h; rcases h with h | h | h
    · exact h hkf
    · exact hle h
    · exact hgt h
  rw [if_neg hc1] at hP
  try wp_auto
  rw [if_pos ⟨by decide, by rw [HLz, show sint.Z (W64 37) = 37 from rfl]; omega, HLc⟩]
  icases slice_at (GF := GF) b q bs (W64 37) 37 4 rfl (by decide) Hlen.1 Hlen.2 (by omega) $$ Hb
    with ⟨Hs, Hback⟩
  wp_apply encoding.binary.wp_LittleEndian_Uint32 _ ((bs.drop 37).take 4) q
    (bs.drop (37 + 4))
    (by simp only [List.length_take, List.length_drop]; omega) $$ [Hs] as Hs
  · iframe
  ihave Hb := Hback $$ Hs
  try wp_auto
  rw [if_pos ⟨by decide, by rw [HLz, show sint.Z (W64 41) = 41 from rfl]; omega, HLc⟩]
  icases slice_at (GF := GF) b q bs (W64 41) 41 4 rfl (by decide) Hlen.1 Hlen.2 (by omega) $$ Hb
    with ⟨Hs, Hback⟩
  wp_apply encoding.binary.wp_LittleEndian_Uint32 _ ((bs.drop 41).take 4) q
    (bs.drop (41 + 4))
    (by simp only [List.length_take, List.length_drop]; omega) $$ [Hs] as Hs
  · iframe
  ihave Hb := Hback $$ Hs
  try wp_auto
  have eix : leToU32 ((bs.drop 37).take 4) = u32At bs 37 := rfl
  have eto : leToU32 ((bs.drop 41).take 4) = u32At bs 41 := rfl
  rw [eix, eto]
  wp_if_destruct
  · have hnone : parseDg bs = none := by
      rw [hP, if_pos (Or.inl (by rw [Hif]; rfl))]
    try wp_auto
    iapply HΦ
    iframe Hb
    rw [hnone]
    ipureintro; rfl
  have ht0 : (u32At bs 41).toNat ≠ 0 := fun h => Hif (by word)
  try wp_auto
  wp_if_destruct
  · have hnone : parseDg bs = none := by
      rw [hP, if_pos (Or.inr (Or.inl (by unfold maxFragmentsN; word)))]
    try wp_auto
    iapply HΦ
    iframe Hb
    rw [hnone]
    ipureintro; rfl
  have htm : ¬ maxFragmentsN < (u32At bs 41).toNat := by unfold maxFragmentsN; word
  try wp_auto
  wp_if_destruct
  · have hnone : parseDg bs = none := by
      rw [hP, if_pos (Or.inr (Or.inr (by word)))]
    try wp_auto
    iapply HΦ
    iframe Hb
    rw [hnone]
    ipureintro; rfl
  have hit : ¬ (u32At bs 41).toNat ≤ (u32At bs 37).toNat := by word
  have hc2 : ¬((u32At bs 41).toNat = 0 ∨ maxFragmentsN < (u32At bs 41).toNat ∨
      (u32At bs 41).toNat ≤ (u32At bs 37).toNat) := by
    intro h; rcases h with h | h | h
    · exact ht0 h
    · exact htm h
    · exact hit h
  rw [if_neg hc2] at hP
  try wp_auto
  have H45 : sint.Z (W64 45) ≤ sint.Z b.len := by rw [HLz, show sint.Z (W64 45) = 45 from rfl]; omega
  rw [if_pos ⟨by decide, H45, HLc⟩]
  have Hrng : 0 ≤ sint.Z (W64 45) ∧ sint.Z (W64 45) ≤ sint.Z b.len ∧ sint.Z b.len ≤ sint.Z b.len :=
    ⟨by decide, H45, Int.le_refl _⟩
  icases (ownSlice_slice (GF := GF) (V := w8) (W64 45) b.len b q bs Hrng).1 $$ Hb with ⟨Hb1, Hb2, Hb3⟩
  have hsub : subslice (sint.nat (W64 45)) (sint.nat b.len) bs = bs.drop fragHeaderLenN := by
    rw [← Hlen.1]; simp only [subslice, List.take_length]; rfl
  have E45 : (slice.slice b w8 (W64 45) b.len ↦*{q} subslice (sint.nat (W64 45)) (sint.nat b.len) bs :
      IProp GF) ⊣⊢ slice.slice b w8 (W64 45) b.len ↦*{q} bs.drop fragHeaderLenN := by
    rw [hsub]; exact .rfl
  ihave Hb2 := E45.1 $$ Hb2
  wp_apply wp_slice_append slice.nil [] _ (bs.drop fragHeaderLenN) q $$ [Hb2] as %ch ⟨Hch, -, Hb2⟩
  · iframe Hb2
    isplitl []
    · iapply ownSlice_nil
    · iapply ownSliceCap_nil
  ihave Hb2 := E45.2 $$ Hb2
  ihave Hb := (ownSlice_slice (GF := GF) (V := w8) (W64 45) b.len b q bs Hrng).2 $$ [Hb1 Hb2 Hb3]
  · iframe
  try wp_auto
  iapply HΦ
  iframe Hb
  rw [hP]
  unfold dgOwn
  isplitr
  · ipureintro; rfl
  isplitr
  · ipureintro; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  rw [List.nil_append]
  first | iexact Hch | iapply Hch
end proof

end raft_kvnet
end EtcdGrove
end Perennial
