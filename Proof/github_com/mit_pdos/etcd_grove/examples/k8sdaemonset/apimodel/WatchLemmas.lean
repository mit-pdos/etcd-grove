/-
**The watches' lemmas**: a new watcher's freshness among the registered ones (its stop flag's
points-to is exclusive), the log index a watch starts at (`logStart`). Lean-first.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apimodel

open Iris Iris.BI Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8sdaemonset

section pure
variable [FfiSyntax]

/-- **The log index a watch from `n` starts at**, as the Go loop finds it: every change before
`k` is at most `n`, and the one at `k` (if any) after it. -/
theorem logStart_eq (l : List Change) (n : w64) (k : Nat) (hk : k ≤ l.length)
    (hle : ∀ j (hj : j < k), (l[j]'(by omega)).rv.toNat ≤ n.toNat)
    (hgt : ∀ (hk' : k < l.length), n.toNat < (l[k]'hk').rv.toNat) :
    logStart l n = k := by
  unfold logStart
  induction l generalizing k with
  | nil => simp at hk ⊢; omega
  | cons c l ih =>
    cases k with
    | zero =>
      have := hgt (by simp)
      simp only [List.getElem_cons_zero] at this
      simp [List.takeWhile_cons, show ¬ (c.rv.toNat ≤ n.toNat) by omega]
    | succ k =>
      have h0 := hle 0 (by omega)
      simp only [List.getElem_cons_zero] at h0
      simp only [List.takeWhile_cons, show (decide (c.rv.toNat ≤ n.toNat)) = true by simp [h0],
        ↓reduceIte, List.length_cons]
      congr 1
      apply ih k (by simp at hk; omega)
      · intro j hj
        have := hle (j + 1) (by omega)
        simpa using this
      · intro hk'
        have := hgt (by simp; omega)
        simpa using this

theorem w64_succ_nat (n : w64) (h0 : 0 ≤ sint.Z n) (hlt : sint.nat n < 2 ^ 63 - 1) :
    0 ≤ sint.Z (n + W64 1) ∧ sint.nat (n + W64 1) = sint.nat n + 1 := by
  constructor <;> word

theorem sint_nat_lt (x : w64) : sint.nat x < 2 ^ 63 := by word

theorem sint_nat_le_of_not_lt (n m : w64) (h : ¬ sint.Z n < sint.Z m) (hn : 0 ≤ sint.Z n) :
    sint.nat m ≤ sint.nat n := by word

theorem sint_nat_lt_of_lt (n m : w64) (h : sint.Z n < sint.Z m) (hn : 0 ≤ sint.Z n) :
    sint.nat n < sint.nat m := by word

/-- An issued version is at most the last one. -/
theorem issuedMap_le (k : Nat) (s : GoString) (n : w64) (hk : k < 2 ^ 64)
    (h : issuedMap k !! s = some n) : n.toNat ≤ k := by
  induction k with
  | zero => simp [issuedMap] at h
  | succ k ih =>
    simp only [issuedMap, GMap.lookup_insert_eq_iff] at h
    split at h
    · cases h
      simp only [W64]
      rw [BitVec.toNat_ofInt]
      omega
    · have := ih (by omega) h
      omega

theorem w64_of_sint_nat (n : w64) (h : 0 ≤ sint.Z n) : W64 (sint.nat n) = n := by word

end pure

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- Two full points-tos of one boolean cell cannot be. -/
theorem bool_pointsto_excl (l : Loc) (b1 b2 : Bool) :
    (l ↦ b1 : IProp GF) ∗ l ↦ b2 ⊢ ⌜False⌝ := by
  rw [typedPointsto_unseal]
  unfold typedPointstoWrap
  iintro ⟨⟨H1, _⟩, ⟨H2, _⟩⟩
  rw [show typedPointstoDef (GF := GF) l b1 (DFrac.own 1) = heapPointsto l (DFrac.own 1) #b1 from rfl,
    show typedPointstoDef (GF := GF) l b2 (DFrac.own 1) = heapPointsto l (DFrac.own 1) #b2 from rfl]
  icombine H1 H2 gives %h
  ipureintro
  exact dfrac_own_one_op_invalid _ h.1

/-- A log's entry in the heap carries the change's version. -/
theorem changes_rv_at (cs : List apimodel.change) (log : List Change) (i : Nat)
    (c : apimodel.change) (e : Change) (h1 : cs[i]? = some c) (h2 : log[i]? = some e) :
    ([∗list] c;e ∈ cs;log, changeAt (GF := GF) c e) ⊢
      ([∗list] c;e ∈ cs;log, changeAt (GF := GF) c e) ∗ ⌜c.rv' = e.rv⌝ := by
  iintro H
  icases (BigSepL2.bigSepL2_lookup_acc (PROP := IProp GF) (Φ := fun _ c e => changeAt (GF := GF) c e) h1 h2) $$ H with ⟨Hce, Hback⟩
  iunfold changeAt at Hce
  icases Hce with ⟨%hce, Hobj⟩
  isplitl
  · iapply Hback
    iunfold changeAt
    iframe
    ipureintro; exact hce
  · ipureintro; exact hce.2

end lemmas

end apimodel
end EtcdGrove
end Perennial
