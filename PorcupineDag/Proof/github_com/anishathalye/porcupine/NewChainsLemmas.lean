/-
Lean-first (no Rocq counterpart).

# `newChains`'s lemmas (2026-11-02)

The chains at no operation linearized: every head `0` (`List.replicate nc 0`), the candidates of
`[]` are the first operations of the chains with no dependency (`cand_init`, from `cand_iff`),
two of them are unrelated in real time (`init_unrelated`, what `addToFrontier` needs), the
frontier built from them is their sorted list (`candList_init`), and `ChainsInv h cs []` follows
from the state's parts (`chainsInv_init`).
-/
module

public import PorcupineDag.Proof.github_com.anishathalye.porcupine.ChainsOwn

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial
namespace github_com.anishathalye.porcupine
namespace Theory

variable {α : Type} {h : List (Op α)} {cs : List (List Nat)}

theorem replicate_getD (n c : Nat) : (List.replicate n (0 : Nat)).getD c 0 = 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

theorem headsSet_init (hok : ChainsOk h cs) :
    ∀ y, y ∈ ([] : List Nat) ↔ headsSet cs (List.replicate cs.length 0) y :=
  ids_iff_headsSet hok posOk_nil (fun _ hy => absurd hy (List.not_mem_nil))

/-- At no operation linearized, a chain's first operation with no dependency is a candidate. -/
theorem cand_init (hok : ChainsOk h cs) (hwf : CallLeRet h) {c : Nat} (hc : c < cs.length)
    (hl : 0 < (chain cs c).length) (hd : deps h cs (List.replicate cs.length 0) c = 0) :
    Cand h (Before h cs) [] (opAt cs c 0) :=
  (cand_iff hok hwf (headsSet_init hok) (fun _ _ hw => absurd hw List.not_mem_nil)).mpr
    ⟨c, hc, by rw [replicate_getD]; exact hl, by rw [replicate_getD], hd⟩

/-- Two such first operations are unrelated in real time. -/
theorem init_unrelated (hok : ChainsOk h cs) (hwf : CallLeRet h) {c v : Nat}
    (hc : c < cs.length) (hlc : 0 < (chain cs c).length)
    (hdc : deps h cs (List.replicate cs.length 0) c = 0)
    (hv : v < cs.length) (hlv : 0 < (chain cs v).length)
    (hdv : deps h cs (List.replicate cs.length 0) v = 0) :
    ¬ Prec h (opAt cs c 0) (opAt cs v 0) ∧ ¬ Prec h (opAt cs v 0) (opAt cs c 0) := by
  have h1 := cand_init hok hwf hc hlc hdc
  have h2 := cand_init hok hwf hv hlv hdv
  exact ⟨fun hp => cand_not_prec h1 h2 (Or.inl hp), fun hp => cand_not_prec h2 h1 (Or.inl hp)⟩

/-- The frontier at no operation linearized: the sorted candidates of `[]`. -/
theorem candList_init (hok : ChainsOk h cs) (hwf : CallLeRet h) {fr : List Nat}
    (hpw : (fr.map (fun c => opAt cs c 0)).Pairwise (KeyGt h cs))
    (hmem : ∀ x, x ∈ fr ↔ x < cs.length ∧ 0 < (chain cs x).length ∧
      deps h cs (List.replicate cs.length 0) x = 0) :
    CandList h cs (Before h cs) [] (fr.map (fun c => opAt cs c 0)) := by
  refine ⟨hpw, fun y => ?_⟩
  rw [cand_iff hok hwf (headsSet_init hok) (fun _ _ hw => absurd hw List.not_mem_nil),
    List.mem_map]
  simp only [replicate_getD]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨h1, h2, h3⟩ := (hmem x).mp hx
    exact ⟨x, h1, h2, rfl, h3⟩
  · rintro ⟨x, h1, h2, rfl, h3⟩
    exact ⟨x, (hmem x).mpr ⟨h1, h2, h3⟩, rfl⟩

theorem chain_eq_getElem {i : Nat} (hi : i < cs.length) : chain cs i = cs[i] := by
  unfold chain; simp [List.getD_eq_getElem?_getD, hi]

/-- The chains hold the partition's operations: their lengths add up to its size (`numOps`). -/
theorem chains_length_sum (hok : ChainsOk h cs) : (cs.map List.length).sum = h.length := by
  have hnd : cs.flatten.Nodup := by
    unfold List.Nodup
    rw [List.pairwise_flatten]
    refine ⟨fun l hl => ?_, ?_⟩
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hl
      have := (hok.1 i).1
      rw [chain_eq_getElem hi] at this
      exact this
    · rw [List.pairwise_iff_getElem]
      intro i j hi hj hij x hx y hy hxy
      subst hxy
      have := hok.2.2 x i j (by rw [chain_eq_getElem hi]; exact hx)
        (by rw [chain_eq_getElem hj]; exact hy)
      omega
  have hperm : cs.flatten.Perm (List.range h.length) := by
    refine (List.perm_ext_iff_of_nodup hnd List.nodup_range).mpr fun y => ?_
    rw [List.mem_flatten, List.mem_range, hok.2.1 y]
    constructor
    · rintro ⟨l, hl, hy⟩
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hl
      exact ⟨i, hi, by rw [chain_eq_getElem hi]; exact hy⟩
    · rintro ⟨i, hi, hy⟩
      exact ⟨cs[i], List.getElem_mem hi, by rw [chain_eq_getElem hi] at hy; exact hy⟩
  rw [← List.length_flatten, hperm.length_eq, List.length_range]

/-- `nDeps` at no operation linearized: the clients whose operations precede the first. -/
theorem deps_init {c : Nat} (hl : 0 < (chain cs c).length) :
    deps h cs (List.replicate cs.length 0) c =
      ((List.range cs.length).filter (fun d => decide (d ≠ c ∧ 0 < FUe h cs c d 0))).length := by
  unfold deps
  congr 1
  apply List.filter_congr
  intro d _
  simp only [replicate_getD, hl, true_and]

/-- The count of the first `j` clients, one more. -/
theorem count_succ (p : Nat → Bool) (j : Nat) :
    ((List.range (j + 1)).filter p).length =
      ((List.range j).filter p).length + (if p j then 1 else 0) := by
  rw [List.range_succ, List.filter_append, List.length_append]
  cases hp : p j <;> simp [hp]

end Theory

open Theory

/-- `ChainsInv` at no operation linearized, from the state's parts. -/
theorem chainsInv_init [GooseExts] {h : List (Op OpV)} {cs : List (List Nat)} (hok : ChainsOk h cs)
    (hwf : CallLeRet h) {st : ChSt} (hshape : ShapeOk cs st)
    (hheads : st.heads = List.replicate cs.length 0) (hfu : FuOk h cs st)
    (hvis : ∀ c, 0 < (chain cs c).length → st.visAt c 0 = true)
    (hnd : ∀ c, c < cs.length → 0 < (chain cs c).length →
      sint.Z (st.nDeps.getD c 0) = deps h cs (List.replicate cs.length 0) c)
    (hpw : (frOf cs st).Pairwise (KeyGt h cs))
    (hmem : ∀ x, x ∈ st.frontier ↔ x < cs.length ∧ 0 < (chain cs x).length ∧
      deps h cs (List.replicate cs.length 0) x = 0) :
    ChainsInv h cs [] st := by
  have hhd : ∀ c, st.head c = 0 := fun c => by unfold ChSt.head; rw [hheads, replicate_getD]
  have hfr : frOf cs st = st.frontier.map (fun c => opAt cs c 0) := by
    unfold frOf hdOp; simp only [hhd]
  refine ⟨hshape, ?_, ?_, ?_, fun _ _ hw => absurd hw List.not_mem_nil,
    fun _ hy => absurd hy List.not_mem_nil, hfu, ?_, ?_, ?_, ?_⟩
  · rw [hheads, headsOf_eq posOk_nil headsOk_nil]
  · rw [hheads]; exact posOk_nil
  · rw [hheads]; exact headsOk_nil
  · intro c k hk hkh
    rw [hhd] at hkh
    have : k = 0 := by omega
    subst this
    exact hvis c hk
  · intro c hc hl
    rw [hhd] at hl
    rw [hnd c hc hl, hheads]
  · intro c hcm
    obtain ⟨h1, h2, -⟩ := (hmem c).mp hcm
    exact ⟨h1, by rw [hhd]; exact h2⟩
  · rw [hfr]
    exact candList_init hok hwf (by rw [← hfr]; exact hpw) hmem

section heap
open Iris Iris.BI Iris.ProofMode
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

/-- Client `c`'s struct as `newChains`'s first loop stores it. -/
def clientAt (sls : List GoSlice) (c : Nat) : client :=
  ⟨W64 (c : Int), sls.getD c slice.nil, W64 0, W64 0⟩

/-- `firstUnks` cut into `n` pieces of `nc` ints, one per operation id. -/
theorem ownSlice_pieces (s : GoSlice) (nc n : Nat) (hb : ((n * nc : Nat) : Int) < 2 ^ 63) :
    (slice.slice s w64 (W64 0) (W64 ((n * nc : Nat) : Int)) ↦*
        List.replicate (n * nc) (W64 0) : IProp GF) ⊢
      ([∗list] y ∈ List.range n,
        slice.slice s w64 (W64 ((y * nc : Nat) : Int)) (W64 (((y + 1) * nc : Nat) : Int)) ↦*
          List.replicate nc (W64 0) : IProp GF) := by
  induction n with
  | zero =>
    simp only [List.range_zero]
    exact BigSepL.bigSepL_nil_intro
  | succ n ih =>
    have hle : n * nc ≤ (n + 1) * nc := Nat.mul_le_mul_right _ (Nat.le_succ n)
    have hb' : ((n * nc : Nat) : Int) < 2 ^ 63 := by omega
    iintro H
    have hn : sint.nat (W64 ((n * nc : Nat) : Int)) = n * nc := by word
    have hz : sint.nat (W64 0) = 0 := rfl
    icases (ownSlice_split (W64 ((n * nc : Nat) : Int)) s (DFrac.own 1) _ (W64 0)
      (W64 (((n + 1) * nc : Nat) : Int)) ⟨by word, by word, by word⟩).1 $$ H with ⟨H1, H2⟩
    rw [hn, hz, Nat.sub_zero, List.take_replicate, List.drop_replicate,
      Nat.min_eq_left hle,
      show (n + 1) * nc - n * nc = nc by rw [Nat.succ_mul]; omega]
    rw [List.range_succ]
    iapply BigSepL.bigSepL_snoc.2
    isplitl [H1]
    · iapply (ih hb') $$ H1
    · iexact H2

end heap

end github_com.anishathalye.porcupine
end Perennial
