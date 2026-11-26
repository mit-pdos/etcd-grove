/- Lean-first (no Rocq counterpart).

The pure lemmas and list conversions of `remoteWriters`' proof (#50 N10a): writer `c`'s Puts
(`writerPuts`, the subslice `[c * nops, (c + 1) * nops)` of the Puts), their encoding's size
(`kvsBytes_length_le`), and a separating list over a list's elements as one over its indices
(`bigSepL_range_of`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.WriterWire

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc

section pure
variable [GooseExts]

/-- **Writer `c`'s Puts**: `trs[c * m, (c + 1) * m)`. -/
def writerPuts (trs : List etcdstart.wkv) (m c : Nat) : List etcdstart.wkv := subslice (c * m) ((c + 1) * m) trs

theorem writerPuts_length_le (trs : List etcdstart.wkv) (m c : Nat) : (writerPuts trs m c).length ≤ m := by
  unfold writerPuts subslice
  simp only [List.length_drop, List.length_take]
  rw [Nat.add_mul, Nat.one_mul]
  omega

theorem mem_writerPuts {trs : List etcdstart.wkv} {m c : Nat} {p : etcdstart.wkv} (h : p ∈ writerPuts trs m c) :
    p ∈ trs := by
  unfold writerPuts subslice at h
  exact List.mem_of_mem_take (List.mem_of_mem_drop h)

theorem kvs_flat_le : ∀ (ps : List etcdstart.wkv), (∀ p ∈ ps, wkvSmall p) →
    (ps.flatMap (fun p => encStr p.Key' ++ encStr p.Val')).length ≤ 32 * ps.length
  | [], _ => by simp
  | p :: ps, h => by
    have h1 := h p List.mem_cons_self
    have ih := kvs_flat_le ps (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [List.flatMap_cons, List.length_append, encStr, encU64_length, List.length_cons] at ih ⊢
    obtain ⟨hk, hv⟩ := h1
    omega

/-- **Small Puts encode in `8 + 32` bytes per Put.** -/
theorem kvsBytes_length_le (ps : List etcdstart.wkv) (h : ∀ p ∈ ps, wkvSmall p) :
    (kvsBytes ps).length ≤ 8 + 32 * ps.length := by
  unfold kvsBytes
  rw [List.length_append, encU64_length]
  have := kvs_flat_le ps h
  omega

/-- Writer `c`'s bounds in `tried` (`c * nops`, `(c + 1) * nops`), without overflow. -/
theorem writer_bounds (k nops : w64) (N : Nat) (hk0 : 0 ≤ sint.Z k) (hk : sint.Z k < N)
    (hn0 : 0 ≤ sint.Z nops) (hN : (N : Int) * sint.Z nops < 2 ^ 63) :
    sint.Z (k * nops) = sint.Z k * sint.Z nops ∧
    sint.Z ((k + W64 1) * nops) = sint.Z k * sint.Z nops + sint.Z nops ∧
    sint.nat (k * nops) = sint.nat k * sint.nat nops ∧
    sint.nat ((k + W64 1) * nops) = (sint.nat k + 1) * sint.nat nops ∧
    sint.Z k * sint.Z nops + sint.Z nops ≤ (N : Int) * sint.Z nops := by
  have h1 : (sint.Z k + 1) * sint.Z nops ≤ (N : Int) * sint.Z nops :=
    Int.mul_le_mul_of_nonneg_right (by omega) hn0
  rw [Int.add_mul, Int.one_mul] at h1
  have h0 : 0 ≤ sint.Z k * sint.Z nops := Int.mul_nonneg hk0 hn0
  have hlo : sint.Z (k * nops) = sint.Z k * sint.Z nops := by word
  have hhi : sint.Z ((k + W64 1) * nops) = sint.Z k * sint.Z nops + sint.Z nops := by
    by_cases hz : sint.Z nops = 0
    · have hn : nops = 0 := by word
      subst hn
      rw [hz, Int.mul_zero, Int.add_zero]
      first
        | word
        | (simp only [BitVec.mul_zero]; word)
        | (rw [show (k + W64 1) * (0 : w64) = 0 by simp]; rfl)
    · have hpos : 1 ≤ sint.Z nops := by omega
      have hNn : (N : Int) * 1 ≤ N * sint.Z nops :=
        Int.mul_le_mul_of_nonneg_left hpos (Int.natCast_nonneg N)
      rw [Int.mul_one] at hNn
      have hkb : sint.Z k + 1 < 2 ^ 63 := by omega
      have hk1 : sint.Z (k + W64 1) = sint.Z k + 1 := by word
      have hb2 : sint.Z (k + W64 1) * sint.Z nops < 2 ^ 63 := by
        rw [hk1, Int.add_mul, Int.one_mul]; omega
      have h0' : 0 ≤ sint.Z (k + W64 1) * sint.Z nops := by
        rw [hk1]; exact Int.mul_nonneg (by omega) hn0
      generalize k + W64 1 = k' at hk1 hb2 h0' ⊢
      have hm : sint.Z (k' * nops) = sint.Z k' * sint.Z nops := by word
      rw [hm, hk1, Int.add_mul, Int.one_mul]
  refine ⟨hlo, hhi, ?_, ?_, h1⟩
  · have : ((sint.nat (k * nops) : Nat) : Int) = ((sint.nat k * sint.nat nops : Nat) : Int) := by
      push_cast
      rw [show ((sint.nat (k * nops) : Nat) : Int) = sint.Z (k * nops) by word, hlo]
      rw [show ((sint.nat k : Nat) : Int) = sint.Z k by word,
        show ((sint.nat nops : Nat) : Int) = sint.Z nops by word]
    exact_mod_cast this
  · have : ((sint.nat ((k + W64 1) * nops) : Nat) : Int) =
        (((sint.nat k + 1) * sint.nat nops : Nat) : Int) := by
      push_cast
      rw [show ((sint.nat ((k + W64 1) * nops) : Nat) : Int) = sint.Z ((k + W64 1) * nops) by word,
        hhi]
      rw [show ((sint.nat k : Nat) : Int) = sint.Z k by word,
        show ((sint.nat nops : Nat) : Int) = sint.Z nops by word, Int.add_mul, Int.one_mul]
    exact_mod_cast this

end pure

section sep
variable {GF : BundledGFunctors}

/-- **A separating list over a list's elements, over its indices.** -/
theorem bigSepL_range_of {A : Type} : ∀ (l : List A) (F : Nat → A → IProp GF),
    ([∗list] c ↦ a ∈ l, F c a) ⊢
      [∗list] c ∈ List.range l.length, ∃ a, ⌜l[c]? = some a⌝ ∗ F c a
  | [], F => by
    simp only [List.length_nil, List.range_zero]
    iintro _
    iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    iempintro
  | x :: t, F => by
    iintro H
    icases (BigSepL.bigSepL_cons (PROP := IProp GF)).1 $$ H with ⟨H0, Ht⟩
    ihave Ht := bigSepL_range_of t (fun c a => F (c + 1) a) $$ Ht
    rw [List.length_cons, List.range_succ_eq_map]
    iapply (BigSepL.bigSepL_cons (PROP := IProp GF)).2
    isplitl [H0]
    · iexists x
      iframe H0
      ipureintro; rfl
    rw [BigSepL.bigSepL_map]
    iapply (BigSepL.bigSepL_mono (PROP := IProp GF) (fun {_ _} _ => by
      simp only [List.getElem?_cons_succ]
      exact .rfl)) $$ Ht

end sep

end etcd_dist_client
end EtcdGrove
end Perennial
