/- Lean-first (no Rocq counterpart). The proof of `(*decoder).u64` (W4c U5): the loop ORs in the
`i`-th byte shifted by `8 i`, the accumulator the low `8 i` bits of `x` (`u64Acc`). -/
module

public import LinuxFs.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.decoder__u64

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.wal

section pure
variable [GooseExts]

theorem u64_off_ok (k n : Nat) (len : w64) (h : k + 8 ≤ n) (hn : n ≤ 0x40000000)
    (hl : n = sint.nat len ∧ 0 ≤ sint.Z len) :
    ¬ uint.Z len < uint.Z (W64 (k : Int) + W64 8) := by
  obtain ⟨hl1, hl2⟩ := hl
  word

theorem u64_idx_ok (k n : Nat) (len : w64) (i : w64) (h : k + 8 ≤ n) (hn : n ≤ 0x40000000)
    (hl : n = sint.nat len ∧ 0 ≤ sint.Z len) (hi : uint.nat i < 8) :
    0 ≤ sint.Z (W64 (k : Int) + i) ∧ sint.Z (W64 (k : Int) + i) < sint.Z len := by
  obtain ⟨hl1, hl2⟩ := hl
  constructor <;> word

theorem u64_byte (bs : List w8) (k : Nat) (x : w64) (r : List w8) (hdrop : bs.drop k = tU64 x ++ r)
    (i : w64) (hi : uint.nat i < 8) (hk : k + 8 ≤ bs.length) (hn : bs.length ≤ 0x40000000) :
    bs[(sint.Z (W64 (k : Int) + i)).toNat]? =
      some (W8 (uint.Z (x >>> W64 (8 * ((uint.nat i : Nat) : Int))))) := by
  have e : (sint.Z (W64 (k : Int) + i)).toNat = k + uint.nat i := by word
  rw [e]
  have := congrArg (·[uint.nat i]?) hdrop
  simp only [List.getElem?_drop] at this
  rw [this, List.getElem?_append_left (by rw [tU64_length]; exact hi), tU64_getElem? x _ hi]

theorem u64_step (x i : w64) (hi : uint.nat i < 8) :
    u64Acc x (uint.nat i) |||
        W64 (uint.Z (W8 (uint.Z (x >>> W64 (8 * ((uint.nat i : Nat) : Int)))))) <<< (W64 8 * i) =
      u64Acc x (uint.nat (i + W64 1)) := by
  have hc : ∀ b : w8, (W64 (uint.Z b) : w64) = b.setWidth 64 := by
    intro b
    apply BitVec.eq_of_toNat_eq
    have := b.isLt
    simp only [uint.Z, W64, BitVec.toNat_setWidth, BitVec.toNat_ofInt]
    omega
  have e1 : W64 8 * i = W64 8 * W64 ((uint.nat i : Nat) : Int) := by word
  have e2 : uint.nat (i + W64 1) = uint.nat i + 1 := by word
  rw [hc, e1, e2]
  exact u64Acc_step x _ hi

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]

theorem decoder.u64.wp_proof : decoder.u64.spec (GF := GF) (hG := hG) := by
  intro d bs k x r hdrop
  wp_start as Hd
  iunfold decRep at Hd
  icases Hd with ⟨%sl, Hd, #Hsl, %Hk⟩
  ihave %Hlen := ownSlice_len $$ Hsl
  wp_auto
  have hk8 := (drop_app hdrop Hk.1).2
  rw [tU64_length] at hk8
  wp_if_destruct
  · exfalso; exact u64_off_ok k bs.length sl.len hk8 Hk.2 Hlen Hif
  ihave HI : (∃ (i : w64),
      "i" ∷ i_ptr ↦ i ∗ "x" ∷ x_ptr ↦ u64Acc x (uint.nat i) ∗
      "%Hi" ∷ ⌜uint.nat i ≤ 8⌝ : IProp GF) $$ [i x]
  · iexists W64 0
    rw [show uint.nat (W64 0) = 0 from rfl, u64Acc_zero]
    iframe
    ipureintro; omega
  wp_for HI
  wp_if_destruct
  · have hi8 : uint.nat i < 8 := by word
    have hb := u64_idx_ok k bs.length sl.len i hk8 Hk.2 Hlen hi8
    simp only [hb, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index sl _ bs DFrac.discard _ hb.1 $$ [Hsl] as -
    · isplitl []
      · iexact Hsl
      · ipureintro; exact u64_byte bs k x r hdrop i hi8 hk8 Hk.2
    rw [u64_step x i hi8]
    wp_for_post
    iframe
    iexists i + W64 1
    iframe
    ipureintro; word
  · have hi8 : uint.nat i = 8 := by word
    rw [hi8, u64Acc_eight]
    iapply HΦ
    iunfold decRep
    iexists sl
    rw [show W64 (k : Int) + W64 8 = W64 ((k + 8 : Nat) : Int) by word]
    isplitl [Hd]
    · iexact Hd
    isplitl []
    · iexact Hsl
    ipureintro; omega

end proof

end etcd_wal
end EtcdGrove
end Perennial
