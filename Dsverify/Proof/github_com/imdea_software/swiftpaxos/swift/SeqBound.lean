/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/SeqBound.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
SWB-7: the replica's sequence is shorter than `2^63 - 1` (`getDepAndHashes`'s premise:
`lightKeyInfo.add` appends to `C`). The sequence is duplicate-free (`swift.localOk`'s last
conjunct) and its commands are registered (its `locLb` carries their `cmdIs`; `sp.cmdIs_ok`:
`ClientId ≥ 1`), so it has at most `(2^31 - 1)·2^32` ids.
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Inv

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

/-! ## Pure: counting -/

theorem swift.cl_toNat_lt (c : w32) (h : 1 ≤ c.toInt) : 1 ≤ c.toNat ∧ c.toNat < 2 ^ 31 := by
  rw [BitVec.toInt_eq_toNat_cond] at h
  have := c.isLt
  split at h <;> omega

theorem swift.nodup_nat_len {l : List Nat} {n : Nat} (hnd : l.Nodup) (hl : ∀ a ∈ l, a < n) :
    l.length ≤ n := by
  have := List.Nodup.length_le_of_subset hnd (l₂ := List.range n)
    (fun a ha => List.mem_range.mpr (hl a ha))
  simpa using this

theorem swift.nodup_map_on {α β : Type} (f : α → β) : ∀ (l : List α),
    (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) → l.Nodup → (l.map f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, hi, hn => by
    rw [List.nodup_cons] at hn
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, swift.nodup_map_on f l
      (fun x hx y hy => hi x (by simp [hx]) y (by simp [hy])) hn.2⟩
    obtain ⟨z, hz, he⟩ := List.mem_map.mp hm
    exact hn.1 (hi z (by simp [hz]) a (by simp) he ▸ hz)

/-- A duplicate-free list of ids with `ClientId ≥ 1` has at most `(2^31 - 1)·2^32` entries. -/
theorem swift.ids_len_bound (l : List sp.CmdId) (hnd : l.Nodup) (hcl : ∀ x ∈ l, 1 ≤ x.cl.toInt) :
    l.length ≤ (2 ^ 31 - 1) * 2 ^ 32 := by
  let f : sp.CmdId → Nat := fun x => (x.cl.toNat - 1) * 2 ^ 32 + x.seq.toNat
  have hinj : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y := by
    intro x hx y hy he
    obtain ⟨a1, a2⟩ := swift.cl_toNat_lt _ (hcl x hx)
    obtain ⟨b1, b2⟩ := swift.cl_toNat_lt _ (hcl y hy)
    have sx := x.seq.isLt
    have sy := y.seq.isLt
    simp only [f] at he
    have h1 : x.cl.toNat = y.cl.toNat := by omega
    have h2 : x.seq.toNat = y.seq.toNat := by omega
    cases x; cases y
    simp only at h1 h2
    rw [BitVec.toNat_inj] at h1 h2
    subst h1; subst h2; rfl
  have hm : (l.map f).Nodup := swift.nodup_map_on f l hinj hnd
  have := swift.nodup_nat_len hm (n := (2 ^ 31 - 1) * 2 ^ 32) (by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
    obtain ⟨a1, a2⟩ := swift.cl_toNat_lt _ (hcl x hx)
    have := x.seq.isLt
    simp only [f]
    have : (x.cl.toNat - 1) * 2 ^ 32 ≤ (2 ^ 31 - 2) * 2 ^ 32 := Nat.mul_le_mul_right _ (by omega)
    omega)
  simpa using this

/-- The bound `getDepAndHashes` needs. -/
theorem swift.seq_len_bound (s : sp.Seq) (hnd : (s.map Prod.fst).Nodup)
    (hcl : ∀ p ∈ s, 1 ≤ p.1.cl.toInt) : s.length + 1 < 2 ^ 63 := by
  have := swift.ids_len_bound (s.map Prod.fst) hnd (by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    exact hcl p hp)
  simp only [List.length_map] at this
  omega

/-! ## The registered commands of a `locLb` -/

section laws
variable [GoGlobalContext] [G : GooseGlobalGS .hasLC netDistGF] [π : NetProtoGS] [Perennial.github_com.imdea_software.swiftpaxos.sp.GobFmt]
variable {γ : sp.Names} {γc γm γl : GName}

theorem swift.bigSepL_cl : ∀ (s : sp.Seq) (Φ : Nat → sp.CmdId × sp.Cmd → IProp netDistGF),
    (∀ i p, Φ i p ⊢ sp.cmdIs γ p.1 p.2) →
    sp.inv γ γc γm γl ∗ ([∗list] i ↦ p ∈ s, Φ i p) ⊢ |={↑sp.spN}=> ⌜∀ p ∈ s, 1 ≤ p.1.cl.toInt⌝
  | [], _, _ => by
    iintro -
    imodintro
    ipureintro
    simp
  | a :: s, Φ, hΦ => by
    iintro ⟨#Hinv, H⟩
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨H0, Hs⟩
    ihave Ha := hΦ 0 a $$ H0
    imod sp.cmdIs_ok a.1 a.2 $$ [Hinv Ha] with %ha
    · iframe Hinv Ha
    imod swift.bigSepL_cl s (fun k p => Φ (k + 1) p) (fun k p => hΦ (k + 1) p) $$ [Hinv Hs] with %hs
    · iframe Hinv Hs
    imodintro
    ipureintro
    intro p hp
    rcases List.mem_cons.mp hp with e | hp
    · subst e; exact ha.2.1
    · exact hs p hp

/-- The commands of a `locLb` are registered with `ClientId ≥ 1`. -/
theorem swift.locLb_cl (r b : Nat) (s : sp.Seq) :
    sp.inv γ γc γm γl ∗ sp.locLb γ r b s ⊢ |={↑sp.spN}=> ⌜∀ p ∈ s, 1 ≤ p.1.cl.toInt⌝ := by
  unfold sp.locLb
  exact swift.bigSepL_cl s _ (fun _ _ => by iintro ⟨-, H⟩; iexact H)

end laws

end Perennial.github_com.imdea_software.swiftpaxos
