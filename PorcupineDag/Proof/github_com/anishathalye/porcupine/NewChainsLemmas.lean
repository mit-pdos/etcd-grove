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

end github_com.anishathalye.porcupine
end Perennial
