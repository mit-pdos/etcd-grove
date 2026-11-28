/-
Lean-first (no Rocq counterpart).

# k8s-dist K9 step 5: the full mode accepts every `SRun` (`notes/k8s-dist-k9.md` §2.9)

`searchRun_accepts`: every run of the semantic model (`SRun`, over the outputs' plain values, as K8's
run gives it) from the seeded store `g0` is accepted, in the same order, by `SharedModel`'s sequential
model in the full mode (`sharedM g0 R 2`), for the revisions `R` `HistoryRevs` returns
(`AnchorsOk (0 :: R.anchors)`, its post). Through `fullCompleteN` (K4's theorem with the revision
floor), with K4's anchors `A = [0, g0.st.rv] ++ R.anchors`: a landing of K4's (`landingsFull A [] []
rv`) at a configuration at revision `rv ≥ g0.st.rv` is `rv + 1`, or an anchor `a ≥ rv` or `a + 1`
above `rv + 1`; the seed's `a ≤ g0.st.rv ≤ rv` give none, the others are Go's (`landingsL`'s anchors
part: `dropWhile` drops only anchors below `rv`). Pure: no `R.anchors` order is needed.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.SharedModelDefs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI
open k8s_dist
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj)

section pure
variable [GooseExts]

/-- An operation with its output's plain value (`Raw` zeroed: what the model reads). -/
def plainIO (p : Input × Output) : Input × Output := (p.1, plainOut p.2)

/-- `OpAnchors` asks only memberships: more anchors keep it. -/
theorem opAnchors_mono {A B : List Nat} (hAB : ∀ a ∈ A, a ∈ B) {x : Input} {y : Output}
    (h : OpAnchors A x y) : OpAnchors B x y := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun hc r hr => hAB _ (h1 hc r hr), fun r hp hr => hAB _ (h2 r hp hr),
    fun hk hf evs he e hm ht => hAB _ (h3 hk hf evs he e hm ht), fun hk => ?_⟩
  obtain ⟨a1, a2, a3, a4, a5⟩ := h4 hk
  exact ⟨hAB _ a1, hAB _ a2, fun he => hAB _ (a3 he), fun hk' he os ho o hm => hAB _ (a4 hk' he os ho o hm),
    fun o hm hu => hAB _ (a5 o hm hu)⟩

/-- `dropWhile` drops only elements satisfying the test. -/
theorem mem_dropWhile_of_not {α : Type} (p : α → Bool) (a : α) :
    ∀ (l : List α), a ∈ l → p a = false → a ∈ l.dropWhile p := by
  intro l
  induction l with
  | nil => intro h; cases h
  | cons b l ih =>
    intro h hp
    simp only [List.dropWhile]
    by_cases hb : p b = true
    · rw [hb]
      rcases List.mem_cons.mp h with rfl | h
      · rw [hp] at hb; cases hb
      · exact ih h hp
    · rw [Bool.not_eq_true] at hb; rw [hb]; exact h

/-- **Go's full-mode landings contain K4's**, at a configuration at or above the seed's revision, for
K4's anchors `[0, n0] ++ R.anchors`. -/
theorem landingsL_full_has (R : RevsL) (n0 : Nat) (b : w64) (x : Input) (y : Output) (c : GCfg)
    (w : Input) (l : Nat) (hn : n0 ≤ uint.nat c.st.st.rv)
    (hl : l ∈ landingsFull (List.range (n0 + 1) ++ R.anchors.map uint.nat) [] [] (uint.nat c.st.st.rv))
    (hl64 : l < 2 ^ 64) :
    l ∈ (landingsL R c.st.st.rv w b (decide (2 = 2)) x y).map uint.nat := by
  have hd : decide (2 = 2) = true := rfl
  rw [hd]
  unfold landingsFull at hl
  rcases List.mem_cons.mp hl with e | e
  · -- the next revision
    refine List.mem_map.mpr ⟨c.st.st.rv + W64 1, ?_, by word⟩
    unfold landingsL
    simp only [ite_true]
    apply List.mem_append_left
    split <;> simp
  · obtain ⟨hm, hgt⟩ := List.mem_filter.mp e
    simp only [decide_eq_true_eq] at hgt
    simp only [List.nil_append, List.mem_flatMap, List.mem_filter, decide_eq_true_eq] at hm
    obtain ⟨a, ⟨ha, hle⟩, hal⟩ := hm
    rcases List.mem_append.mp ha with ha | ha
    · rw [List.mem_range] at ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hal
      omega
    · obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
      have hdrop : a' ∈ R.anchors.dropWhile fun a => decide (uint.nat a < uint.nat c.st.st.rv) :=
        mem_dropWhile_of_not _ a' R.anchors ha' (by simp; omega)
      have hok : ∀ r : w64, uint.nat r = l →
          landOkL c.st.st.rv w b true x y r = true := by
        intro r hr
        unfold landOkL
        simp only [Bool.true_or, Bool.and_true, decide_eq_true_eq]
        word
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hal
      have key : ∀ r : w64, r ∈ [a', a' + W64 1] → uint.nat r = l →
          l ∈ (landingsL R c.st.st.rv w b true x y).map uint.nat := by
        intro r hr hrl
        refine List.mem_map.mpr ⟨r, ?_, hrl⟩
        unfold landingsL
        simp only [ite_true]
        apply List.mem_append_right
        exact List.mem_filter.mpr ⟨List.mem_flatMap.mpr ⟨a', hdrop, hr⟩, hok r hrl⟩
      rcases hal with hal | hal
      · exact key a' (by simp) hal.symm
      · exact key (a' + W64 1) (by simp) (by word)

end pure

section go
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

open github_com.anishathalye.porcupine (Theory.run)

include sem package_sem in
/-- **K9's theorem** (`notes/k8s-dist-k9.md` §2.9): every `SRun` from the seeded store `g0` (over the
plain outputs) is accepted by the full mode's sequential model, in the same order, for revisions `R`
naming every revision the operations name (`HistoryRevs`' post). -/
theorem searchRun_accepts (g0 : HSt) (R : RevsL) (xs : List (Input × Output)) (c' : GCfg)
    (hw : HWf g0)
    (hseed : ∀ g ∈ g0.hist, ∀ it ∈ g.items, uint.nat it.obj'.ResourceVersion' ≤ uint.nat g0.st.rv)
    (hA : AnchorsOk (0 :: R.anchors.map uint.nat) xs)
    (hrun : SRun g0 ⟨g0, []⟩ (xs.map plainIO) c') :
    ∃ S, Theory.run (sharedM g0 R 2) (sharedM g0 R 2).init
      (xs.map fun p => (boxIn p.1, boxOut p.2)) = some S := by
  let n0 := uint.nat g0.st.rv
  let A := List.range (n0 + 1) ++ R.anchors.map uint.nat
  have hAB : ∀ a ∈ 0 :: R.anchors.map uint.nat, a ∈ A := by
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact List.mem_append_left _ (List.mem_range.mpr (by omega))
    · exact List.mem_append_right _ ha
  have hA' : AnchorsOk A (xs.map plainIO) := by
    refine ⟨hAB 0 List.mem_cons_self, fun p hp => ?_⟩
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact opAnchors_mono hAB (hA.2 q hq)
  have hN := fullCompleteN g0 A _ c' hw.1 hw.2 hseed (by
      refine ⟨hA'.1, hA'.2⟩) hrun
  have main : ∀ (ys : List (Input × Output)) (c : GCfg), SearchRunN A n0 c (ys.map plainIO) →
      ∀ S : GCfg → Prop, S c → ∃ S', Theory.run (sharedM g0 R 2) S
        (ys.map fun p => (boxIn p.1, boxOut p.2)) = some S' := by
    intro ys
    induction ys with
    | nil => intro c _ S _; exact ⟨S, rfl⟩
    | cons q ys ih =>
      intro c hr S hS
      rcases hr with _ | ⟨hn, hst, hrest⟩
      obtain ⟨d, hsd, he⟩ := hst
      rename_i e
      have hgo : GoStep R 2 c q.1 q.2 e := by
        unfold GoStep
        rw [if_neg (fun h => absurd h.1 (by decide))]
        exact ⟨d, settleL_with (fun c w l hn hl hl64 =>
          landingsL_full_has R n0 (boundL q.1 q.2) q.1 q.2 c w l hn hl hl64) hsd hn, he⟩
      have hstep : (sharedM g0 R 2).step S (boxIn q.1, boxOut q.2) =
          some (fun e => ∃ c, S c ∧ GoStep R 2 c q.1 q.2 e) := by
        unfold sharedM
        dsimp only
        rw [decIO_box (sem := sem) (package_sem := package_sem)]
        dsimp only
        rw [if_pos ⟨e, c, hS, hgo⟩]
      obtain ⟨S', hS'⟩ := ih e hrest (fun e => ∃ c, S c ∧ GoStep R 2 c q.1 q.2 e) ⟨c, hS, hgo⟩
      exact ⟨S', by simp only [List.map_cons, Theory.run, hstep]; exact hS'⟩
  exact main xs _ hN _ rfl

end go

end k8s_etcd3
end EtcdGrove
end Perennial
