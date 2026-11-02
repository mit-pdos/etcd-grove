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

/-- `idx_auto` (`ComputeFirstUnkLemmas.lean`) under its own name: resolve the bounds checks with
the given facts, then step; repeated while it makes progress. -/
syntax "nc_idx" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| nc_idx [$ts,*]) =>
    `(tactic| repeat (simp only [$ts,*, _root_.and_self, ↓reduceIte]; wp_auto))

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

/-- The operation ids are the chains' operations, chain by chain. -/
theorem chains_flatMap_perm (hok : ChainsOk h cs) :
    (List.range h.length).Perm ((List.range cs.length).flatMap (chain cs)) := by
  have hnd : ((List.range cs.length).flatMap (chain cs)).Nodup := by
    unfold List.Nodup
    rw [List.pairwise_flatMap]
    refine ⟨fun c _ => (hok.1 c).1, ?_⟩
    refine (List.pairwise_lt_range (n := cs.length)).imp ?_
    intro a b hab y hya z hzb hyz
    subst hyz
    have := hok.2.2 y a b hya hzb
    omega
  refine (List.perm_ext_iff_of_nodup List.nodup_range hnd).mpr fun y => ?_
  rw [List.mem_range, hok.2.1 y, List.mem_flatMap]
  simp only [List.mem_range]

theorem chain_length_le' (hok : ChainsOk h cs) (c : Nat) : (chain cs c).length ≤ h.length := by
  have := List.Nodup.length_le_of_subset (l₂ := List.range h.length) (hok.1 c).1
    (fun y hy => List.mem_range.mpr (lt_length_of_mem hok hy))
  simpa using this

theorem sum_take_le (cs : List (List Nat)) (m : Nat) :
    ((cs.take m).map List.length).sum ≤ (cs.map List.length).sum := by
  conv => rhs; rw [← List.take_append_drop m cs]
  rw [List.map_append, List.sum_append]
  omega

theorem sum_take_succ (cs : List (List Nat)) {m : Nat} (hm : m < cs.length) :
    ((cs.take (m + 1)).map List.length).sum =
      ((cs.take m).map List.length).sum + (chain cs m).length := by
  rw [List.take_add_one, List.getElem?_eq_getElem hm, chain_eq_getElem hm, List.map_append,
    List.sum_append]
  simp

theorem set_prefix_replicate {β : Type} (f : Nat → β) (z : β) {k L : Nat} (hk : k < L) :
    ((List.range k).map f ++ List.replicate (L - k) z).set k (f k) =
      (List.range (k + 1)).map f ++ List.replicate (L - (k + 1)) z := by
  have hL : L - k = (L - (k + 1)) + 1 := by omega
  rw [List.set_append_right _ _ (by simp), hL, List.replicate_succ]
  simp [List.range_succ]

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

/-- The chains' state as `newChains` builds it: heads `0`, `nDeps` `0`, no frontier, nothing
visited, every `firstUnk` all zeros. -/
def chStInit (cs : List (List Nat)) : ChSt where
  heads := List.replicate cs.length 0
  nDeps := List.replicate cs.length (W64 0)
  frontier := []
  vis := cs.map (fun l => List.replicate l.length false)
  fu := cs.map (fun l => List.replicate l.length (List.replicate cs.length (W64 0)))

theorem getD_map_chain {β : Type} {cs : List (List Nat)} (f : List Nat → List β) (hf : f [] = [])
    (c : Nat) : (cs.map f).getD c [] = f (chain cs c) := by
  unfold chain
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases cs[c]? <;> simp [hf]

theorem init_visAt {cs : List (List Nat)} (c k : Nat) : (chStInit cs).visAt c k = false := by
  unfold ChSt.visAt chStInit
  simp only
  rw [getD_map_chain (fun l => List.replicate l.length false) (by simp)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

theorem init_fuAt {cs : List (List Nat)} {c k : Nat} (hk : k < (chain cs c).length) :
    (chStInit cs).fuAt c k = List.replicate cs.length (W64 0) := by
  unfold ChSt.fuAt chStInit
  simp only
  rw [getD_map_chain (fun l => List.replicate l.length (List.replicate cs.length (W64 0))) (by simp)]
  simp [List.getD_eq_getElem?_getD, hk]

theorem init_head {cs : List (List Nat)} (c : Nat) : (chStInit cs).head c = 0 := by
  unfold ChSt.head chStInit; exact replicate_getD _ _

theorem init_nDeps {cs : List (List Nat)} (c : Nat) : (chStInit cs).nDeps.getD c 0 = W64 0 := by
  unfold chStInit
  simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

theorem init_shape (cs : List (List Nat)) : ShapeOk cs (chStInit cs) := by
  refine ⟨by simp [chStInit], by simp [chStInit], by simp [chStInit], by simp [chStInit],
    fun c k hk => ⟨?_, ?_, ?_⟩⟩
  · unfold chStInit; simp only
    rw [getD_map_chain (fun l => List.replicate l.length false) (by simp)]; simp
  · unfold chStInit; simp only
    rw [getD_map_chain (fun l => List.replicate l.length (List.replicate cs.length (W64 0)))
      (by simp)]; simp
  · rw [init_fuAt hk]; simp

theorem init_fuOk {α : Type} (h : List (Op α)) (cs : List (List Nat)) : FuOk h cs (chStInit cs) := by
  intro c k hv
  rw [init_visAt] at hv
  cases hv

/-- A `firstUnk` set: still fresh (`CoFresh` does not read it). -/
theorem coFresh_set_fu [GooseExts] {h : List (Op OpV)} {ch : List Nat} {cos : List clientOperation} {j : Nat}
    {co : clientOperation} (hf : CoFresh h ch cos) (hco : cos[j]? = some co) (s : GoSlice) :
    CoFresh h ch (cos.set j { co with firstUnk' := s }) := by
  refine ⟨by rw [List.length_set]; exact hf.1, fun k co' hk => ?_⟩
  by_cases hkj : k = j
  · subst hkj
    rw [List.getElem?_set_self (List.getElem?_eq_some_iff.mp hco).1] at hk
    cases hk
    exact hf.2 k co hco
  · rw [List.getElem?_set_ne (Ne.symm hkj)] at hk
    exact hf.2 k co' hk

theorem take_set_succ {β : Type} {l : List β} {j : Nat} (hj : j < l.length) (a : β) :
    (l.set j a).take (j + 1) = l.take j ++ [a] := by
  rw [List.take_add_one, List.getElem?_set_self hj, List.take_set,
    List.set_eq_of_length_le (by simp; omega)]
  rfl

theorem w64_eq_of_sint {a : w64} {n : Nat} (ha : sint.Z a = (n : Int)) (hn : (n : Int) < 2 ^ 63) :
    a = W64 (n : Int) := by
  word

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

/-- `newChains`' third loop's invariant, at its counter `i`: heads `0`, no frontier, the clients
below `i` have their first operation visited and their `nDeps` counted. -/
def NcInv {α : Type} (h : List (Op α)) (cs : List (List Nat)) (i : Nat) (st : ChSt) : Prop :=
  st.heads = List.replicate cs.length 0 ∧ st.frontier = [] ∧ ShapeOk cs st ∧ FuOk h cs st ∧
  (∀ c k, st.visAt c k = decide (c < i ∧ k = 0 ∧ k < (chain cs c).length)) ∧
  (∀ c, c < i → 0 < (chain cs c).length →
    sint.Z (st.nDeps.getD c 0) = deps h cs (List.replicate cs.length 0) c)

theorem ncInv_init {α : Type} (h : List (Op α)) (cs : List (List Nat)) :
    NcInv h cs 0 (chStInit cs) :=
  ⟨rfl, rfl, init_shape cs, init_fuOk h cs, fun c k => by rw [init_visAt]; simp,
    fun _ hc => absurd hc (Nat.not_lt_zero _)⟩

theorem ncInv_head {α : Type} {h : List (Op α)} {cs : List (List Nat)} {i : Nat} {st : ChSt}
    (hinv : NcInv h cs i st) (c : Nat) : st.head c = 0 := by
  unfold ChSt.head; rw [hinv.1, replicate_getD]

/-- One client counted: the state after `computeFirstUnk(i)` (`st1`) with `nDeps[i]` set. -/
theorem ncInv_step {α : Type} {h : List (Op α)} {cs : List (List Nat)} {i : Nat} {st st1 : ChSt}
    (hinv : NcInv h cs i st) (hi : i < cs.length)
    (h1 : st1.heads = st.heads ∧ st1.nDeps = st.nDeps ∧ st1.frontier = st.frontier ∧
      ShapeOk cs st1 ∧ FuOk h cs st1 ∧
      ∀ c' k, st1.visAt c' k = (st.visAt c' k ||
        decide (c' = i ∧ k = st.head c' ∧ k < (chain cs c').length)))
    (nd : w64) (hnd : 0 < (chain cs i).length → sint.Z nd = deps h cs (List.replicate cs.length 0) i) :
    NcInv h cs (i + 1) { st1 with nDeps := st1.nDeps.set i nd } := by
  obtain ⟨hh, hn, hf, hsh, hfu, hv⟩ := h1
  obtain ⟨i1, i2, i3, i4, i5, i6⟩ := hinv
  refine ⟨by simp only; rw [hh, i1], by simp only; rw [hf, i2], ?_, hfu, ?_, ?_⟩
  · obtain ⟨s1, s2, s3, s4, s5⟩ := hsh
    exact ⟨s1, by simp only; rw [List.length_set]; exact s2, s3, s4, s5⟩
  · intro c k
    show st1.visAt c k = _
    rw [hv, i5]
    have hhd : st.head c = 0 := by unfold ChSt.head; rw [i1, replicate_getD]
    rw [hhd]
    by_cases hc : c = i
    · subst hc; simp
    · by_cases hci : c < i
      · simp [hc, hci, show c < i + 1 by omega]
      · simp [hc, hci, show ¬ c < i + 1 by omega]
  · intro c hc hl
    simp only
    by_cases hci : c = i
    · subst hci
      rw [List.getD_eq_getElem?_getD, List.getElem?_set_self (by rw [hn, i3.2.1]; exact hi)]
      exact hnd hl
    · rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hci), ← List.getD_eq_getElem?_getD,
        hn]
      exact i6 c (by omega) hl

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

/-- Two lists of the same length, element by element. -/
theorem bigSepL_transfer {A B : Type} {Φ : Nat → A → IProp GF} {Ψ : Nat → B → IProp GF} :
    ∀ (l1 : List A) (l2 : List B), l1.length = l2.length →
      (∀ k x y, l1[k]? = some x → l2[k]? = some y → Φ k x ⊢ Ψ k y) →
      ([∗list] k ↦ x ∈ l1, Φ k x) ⊢ [∗list] k ↦ y ∈ l2, Ψ k y
  | [], [], _, _ => BigSepL.bigSepL_nil_intro
  | [], _ :: _, hl, _ => absurd hl (by simp)
  | _ :: _, [], hl, _ => absurd hl (by simp)
  | x :: l1, y :: l2, hl, hf => by
    refine BigSepL.bigSepL_cons.1.trans ((sep_mono ?_ ?_).trans BigSepL.bigSepL_cons.2)
    · exact hf 0 x y rfl rfl
    · exact bigSepL_transfer (Φ := fun k x => Φ (k + 1) x) (Ψ := fun k y => Ψ (k + 1) y) l1 l2
        (by simpa using hl) (fun k x' y' h1 h2 => hf (k + 1) x' y' h1 h2)

/-- `firstUnks`' pieces, regrouped by client (the ids of client `c` are its chain's). -/
theorem pieces_regroup {h : List (Theory.Op OpV)} {cs : List (List Nat)} (hok : ChainsOk h cs)
    (P : Nat → IProp GF) {B : Type} (l : List B) (hl : l.length = cs.length) :
    ([∗list] y ∈ List.range h.length, P y) ⊢ [∗list] c ↦ _x ∈ l, [∗list] y ∈ chain cs c, P y := by
  refine (BigSepL.bigSepL_perm (chains_flatMap_perm hok)).1.trans ?_
  rw [BigSepL.bigSepL_flatMap]
  refine bigSepL_transfer _ _ (by simp [hl]) ?_
  intro k x y hx hy
  have hk : k < cs.length := by rw [← hl]; exact (List.getElem?_eq_some_iff.mp hy).1
  rw [List.getElem?_range hk] at hx
  cases hx; exact .rfl

/-- The chains opened at client `i`: everything, client `i`'s struct taken out of the slice. -/
theorem chains_open (ch : Loc) (cl : GoSlice) (h : List (Theory.Op OpV)) (cs : List (List Nat))
    (st : ChSt) (i : Int) (hi : 0 ≤ i) (hc : i.toNat < cs.length) :
    (chainsOwnCl ch cl h cs st : IProp GF) ⊢ ∃ (chV : chains) (cvs : List client) (cv : client),
      ⌜chV.clients' = cl ∧ cvs.length = cs.length ∧ sint.Z chV.numOps' = h.length ∧
        cvs[i.toNat]? = some cv⌝ ∗
      ch ↦ chV ∗ chV.frontier' ↦* (st.frontier.map (fun (c : Nat) => (W64 (c : Int) : w64))) ∗
      ownSliceCap w64 chV.frontier' (DFrac.own 1) ∗
      sliceIndexRef client i cl ↦ cv ∗
      (∀ v', sliceIndexRef client i cl ↦ v' -∗ cl ↦* cvs.set i.toNat v') ∗
      ([∗list] k ↦ y ∈ cvs, if k = i.toNat then emp else clientOwn h cs st k y) ∗
      clientOwn h cs st i.toNat cv := by
  unfold chainsOwnCl chainsRepr
  iintro ⟨%chV, Hch, %Hclq, %cvs, Hcl, %Hcvs, Hfr, Hcap, Hcls⟩
  subst Hclq
  obtain ⟨cv, hcv⟩ : ∃ cv, cvs[i.toNat]? = some cv :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  icases ownSlice_elem_acc i cv chV.clients' _ cvs hi hcv $$ Hcl with ⟨Hcv, Hcl⟩
  icases (BigSepL.bigSepL_delete_cond (PROP := IProp GF)
    (Φ := fun k cv => clientOwn h cs st k cv) hcv).1 $$ Hcls with ⟨Hc, Hrest⟩
  iexists chV, cvs, cv
  iframe
  ipureintro
  exact ⟨rfl, Hcvs.1, Hcvs.2, hcv⟩

/-- The chains closed again, client `i`'s struct (now `cv'`) put back, at the state `st'` (the
other clients' structs unchanged). -/
theorem chains_close (ch : Loc) (chV : chains) (cl : GoSlice) (h : List (Theory.Op OpV))
    (cs : List (List Nat)) (st st' : ChSt) (cvs : List client) (i : Int) (cv' : client)
    (hcl : chV.clients' = cl) (hlen : cvs.length = cs.length ∧ sint.Z chV.numOps' = h.length)
    (hc : i.toNat < cvs.length)
    (hother : ∀ k, k ≠ i.toNat → ∀ cv, clientOwn (GF := GF) h cs st' k cv = clientOwn h cs st k cv) :
    (ch ↦ chV : IProp GF) ∗
      chV.frontier' ↦* (st'.frontier.map (fun (c : Nat) => (W64 (c : Int) : w64))) ∗
      ownSliceCap w64 chV.frontier' (DFrac.own 1) ∗
      sliceIndexRef client i cl ↦ cv' ∗
      (∀ v', sliceIndexRef client i cl ↦ v' -∗ cl ↦* cvs.set i.toNat v') ∗
      ([∗list] k ↦ y ∈ cvs, if k = i.toNat then emp else clientOwn h cs st k y) ∗
      clientOwn h cs st' i.toNat cv' ⊢ chainsOwnCl ch cl h cs st' := by
  iintro ⟨Hch, Hfr, Hcap, Hcv, Hw, Hrest, Hc⟩
  ihave Hcl := Hw $$ %cv' Hcv
  subst hcl
  iapply chainsOwnCl_fold ch chV chV.clients' h cs st' rfl
  iframe Hch
  unfold chainsRepr
  iexists cvs.set i.toNat cv'
  iframe Hcl Hfr Hcap
  isplitr
  · ipureintro; exact ⟨by rw [List.length_set]; exact hlen.1, hlen.2⟩
  iapply (BigSepL.bigSepL_delete_cond (PROP := IProp GF)
    (Φ := fun k cv => clientOwn h cs st' k cv) (List.getElem?_set_self hc)).2
  iframe Hc
  iapply (bigSepL_transfer _ _ (List.length_set ..).symm ?_) $$ Hrest
  intro k x y hx hy
  by_cases hk : k = i.toNat
  · simp only [hk, ↓reduceIte]; exact .rfl
  · rw [List.getElem?_set_ne (Ne.symm hk), hx] at hy
    cases hy
    simp only [hk, ↓reduceIte, hother k hk x]; exact .rfl

/-- Operation `y`'s piece of `firstUnks` (`fsl`), `nc` ints. -/
noncomputable def fuPiece (fsl : GoSlice) (nc y : Nat) : IProp GF :=
  slice.slice fsl w64 (W64 ((y * nc : Nat) : Int)) (W64 (((y + 1) * nc : Nat) : Int)) ↦*
    List.replicate nc (W64 0)

/-- Client `c`'s operations (at `sl`), not yet given their `firstUnk` pieces. -/
noncomputable def coPend (h : List (Theory.Op OpV)) (cs : List (List Nat)) (fsl : GoSlice) (c : Nat)
    (sl : GoSlice) : IProp GF :=
  iprop(∃ cos : List clientOperation, sl ↦* cos ∗ ⌜CoFresh h (chain cs c) cos⌝ ∗
    [∗list] y ∈ chain cs c, fuPiece fsl cs.length y)

/-- Client `c`'s operations (at `sl`), each given its `firstUnk` piece. -/
noncomputable def coDone (h : List (Theory.Op OpV)) (cs : List (List Nat)) (c : Nat) (sl : GoSlice) : IProp GF :=
  iprop(∃ cos : List clientOperation, sl ↦* cos ∗ ⌜CoFresh h (chain cs c) cos⌝ ∗
    [∗list] k ↦ co ∈ cos, co.firstUnk' ↦* List.replicate cs.length (W64 0))

/-- Before `newChains`' second loop: every client pending, with its operations' pieces. -/
theorem pend_init {h : List (Theory.Op OpV)} {cs : List (List Nat)} (hok : ChainsOk h cs)
    (sls : List GoSlice) (hl : sls.length = cs.length) (fsl : GoSlice) (m : Nat) (hm : m = 0) :
    ([∗list] c ↦ sl ∈ sls, ∃ cos : List clientOperation, sl ↦* cos ∗ ⌜CoFresh h (chain cs c) cos⌝)
      ∗ ([∗list] y ∈ List.range h.length, fuPiece fsl cs.length y) ⊢
      [∗list] c ↦ sl ∈ sls, if c < m then coDone (GF := GF) h cs c sl else coPend h cs fsl c sl := by
  iintro ⟨H1, H2⟩
  ihave H2 := pieces_regroup hok _ sls hl $$ H2
  ihave H := BigSepL.bigSepL_sep_eqv.2 $$ [H1 H2]
  · iframe
  iapply (BigSepL.bigSepL_mono ?_) $$ H
  intro c sl _
  subst hm
  simp only [Nat.not_lt_zero, ↓reduceIte]
  unfold coPend
  iintro ⟨Hp, %cos, Hs, %Hf⟩
  iexists cos
  iframe
  ipureintro; exact Hf

/-- Client `i` taken out of the loop's conjunction (it is pending). -/
theorem bigSepL_if_take {A : Type} (l : List A) (i : Nat) (x : A) (hx : l[i]? = some x)
    (D F : Nat → A → IProp GF) :
    ([∗list] k ↦ y ∈ l, if k < i then D k y else F k y) ⊢
      F i x ∗ [∗list] k ↦ y ∈ l, if k = i then emp else (if k < i then D k y else F k y) := by
  iintro H
  icases (BigSepL.bigSepL_delete_cond (PROP := IProp GF)
    (Φ := fun k y => if k < i then D k y else F k y) hx).1 $$ H with ⟨Hi, Hr⟩
  simp only [Nat.lt_irrefl, ↓reduceIte]
  iframe

/-- Client `i` put back, done. -/
theorem bigSepL_if_step {A : Type} (l : List A) (i : Nat) (x : A) (hx : l[i]? = some x)
    (D F : Nat → A → IProp GF) :
    D i x ∗ ([∗list] k ↦ y ∈ l, if k = i then emp else (if k < i then D k y else F k y)) ⊢
      [∗list] k ↦ y ∈ l, if k < i + 1 then D k y else F k y := by
  iintro ⟨Hd, Hr⟩
  iapply (BigSepL.bigSepL_delete_cond (PROP := IProp GF)
    (Φ := fun k y => if k < i + 1 then D k y else F k y) hx).2
  simp only [Nat.lt_succ_self, ↓reduceIte]
  iframe Hd
  iapply (BigSepL.bigSepL_mono ?_) $$ Hr
  intro k y _
  by_cases hk : k = i
  · simp only [hk, ↓reduceIte]; exact .rfl
  · by_cases hki : k < i
    · simp only [hk, hki, show k < i + 1 by omega, ↓reduceIte]; exact .rfl
    · simp only [hk, hki, show ¬ k < i + 1 by omega, ↓reduceIte]; exact .rfl

/-- A client whose operations got their `firstUnk` pieces: its struct, at the initial state. -/
theorem clientOwn_init {h : List (Theory.Op OpV)} {cs : List (List Nat)} (sls : List GoSlice)
    (c : Nat) (sl : GoSlice) (hsl : sls[c]? = some sl) (hc : (c : Int) < 2 ^ 63) :
    coDone h cs c sl ⊢ clientOwn (GF := GF) h cs (chStInit cs) c (clientAt sls c) := by
  unfold clientOwn clientAt coDone
  iintro ⟨%cos, Hsl, %Hf, Hfu⟩
  isplitr
  · ipureintro
    refine ⟨by simp only; word, by simp only; rw [init_head]; rfl, by simp only; rw [init_nDeps]⟩
  iexists cos
  simp only [List.getD_eq_getElem?_getD, hsl, Option.getD_some]
  iframe Hsl
  isplitr
  · ipureintro
    refine ⟨Hf.1, fun k co hco => ?_⟩
    obtain ⟨y, o, h1, h2, h3, -, h5, h6, h7, h8, h9⟩ := Hf.2 k co hco
    refine ⟨y, o, h1, h2, h3, h5, h6, h7, h8, ?_⟩
    rw [h9]
    have := init_visAt (cs := cs) c k
    unfold ChSt.visAt at this
    exact this.symm
  iapply (BigSepL.bigSepL_mono ?_) $$ Hfu
  intro k co hco
  have hk : k < (chain cs c).length := by rw [← Hf.1]; exact (List.getElem?_eq_some_iff.mp hco).1
  rw [init_fuAt hk]

end heap

end github_com.anishathalye.porcupine
end Perennial
