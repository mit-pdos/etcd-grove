/-
Lean-first (no Rocq counterpart).

# k8setcd3: the seeded configuration's facts for the maintainers' checker (k8s 7g step 5)

`RunOk g0s`: what `realCheck`'s pure core (B2, B4, B5) needs of the configuration `Check` starts from,
proved for the driver's seeded store and history (`g0s`, `Seed.lean`), so that `Main`, `MainCluster` and
`MainPartition` discharge `Check`'s premise `RunOk g0`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Seed
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.RealRun

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open k8s_correctness
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore)

section pure
variable [GooseExts]

theorem st1_items : st1.items = [] := rfl

theorem st2_items' : st2.items = [⟨kA, dA.toObj (W64 2), false⟩] := by
  simp only [st2_items, itA, seedItem_kA]

theorem st3_items' : st3.items = [⟨kA, dA.toObj (W64 2), false⟩, ⟨kB, dB.toObj (W64 3), false⟩] := by
  simp only [st3_items, itA, itB, seedItem_kA, seedItem_kB]

theorem histN_g0s (r : Nat) (hr : r ≤ 3) :
    histN g0s.hist r = if r = 0 then zSt else if r = 1 then st1 else if r = 2 then st2 else st3 := by
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) with rfl | rfl | rfl | rfl <;> rfl

theorem itemOk_dA (n : w64) : itemOk (dA.toObj n) :=
  itemOk_of _ (DObj.toObj_fits _ _) rfl (by simp [dA])

theorem itemOk_dB (n : w64) : itemOk (dB.toObj n) :=
  itemOk_of _ (DObj.toObj_fits _ _) rfl (by simp [dB])

theorem stOk_st1 : StOk st1 := ⟨by simp [st1, SortedI], by simp [st1]⟩

theorem stOk_st2 : StOk st2 := by
  refine ⟨by rw [st2_items']; simp only [SortedI, List.map]; decide, fun it hit => ?_⟩
  rw [st2_items'] at hit; simp only [List.mem_cons, List.not_mem_nil, or_false] at hit; subst hit; rfl

theorem stOk_st3 : StOk st3 := by
  refine ⟨by rw [st3_items']; simp only [SortedI, List.map]; decide, fun it hit => ?_⟩
  rw [st3_items'] at hit; simp only [List.mem_cons, List.not_mem_nil, or_false] at hit
  rcases hit with rfl | rfl <;> rfl

/-- The stores at revisions `0..3`: sorted, unannotated, their objects `itemOk` with revisions in
`[1, r]`. -/
theorem histN_g0s_ok (r : Nat) (hr : r ≤ 3) :
    StOk (histN g0s.hist r) ∧ ∀ it ∈ (histN g0s.hist r).items,
      itemOk it.obj' ∧ 1 ≤ uint.nat it.obj'.ResourceVersion' ∧ uint.nat it.obj'.ResourceVersion' ≤ r := by
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) with rfl | rfl | rfl | rfl
  · exact ⟨⟨by simp [histN, zSt, SortedI], by simp [histN, zSt]⟩, by simp [histN, zSt]⟩
  · exact ⟨stOk_st1, by simp [show histN g0s.hist 1 = st1 from rfl, st1_items]⟩
  · rw [show histN g0s.hist 2 = st2 from rfl]
    refine ⟨stOk_st2, fun it hit => ?_⟩
    rw [st2_items'] at hit; simp only [List.mem_cons, List.not_mem_nil, or_false] at hit; subst hit
    exact ⟨itemOk_dA _, by simp [DObj.toObj], by simp [DObj.toObj]⟩
  · rw [show histN g0s.hist 3 = st3 from rfl]
    refine ⟨stOk_st3, fun it hit => ?_⟩
    rw [st3_items'] at hit; simp only [List.mem_cons, List.not_mem_nil, or_false] at hit
    rcases hit with rfl | rfl
    · exact ⟨itemOk_dA _, by simp [DObj.toObj], by simp [DObj.toObj]⟩
    · exact ⟨itemOk_dB _, by simp [DObj.toObj], by simp [DObj.toObj]⟩

theorem histAtL_g0s (q : w64) (hq0 : 0 < uint.nat q) (hq : uint.nat q ≤ uint.nat g0s.st.rv) :
    histAtL g0s.hist q = histN g0s.hist (uint.nat q) := rfl

theorem g0s_rv : uint.nat g0s.st.rv = 3 := rfl

theorem changeAt_g0s2 :
    changeAtL (histN g0s.hist 1).items (histN g0s.hist 2).items 2 =
      some ⟨kA, none, some (dA.toObj (W64 2)), 2⟩ := by
  show changeAtL st1.items st2.items 2 = _
  rw [st1_items, st2_items']; rfl

theorem changeAt_g0s3 :
    changeAtL (histN g0s.hist 2).items (histN g0s.hist 3).items 3 =
      some ⟨kB, none, some (dB.toObj (W64 3)), 3⟩ := by
  show changeAtL st2.items st3.items 3 = _
  rw [st2_items', st3_items']
  simp only [changeAtL, show ¬ go.GoStringLt kA kA from go.goStringLt_irrefl kA, decide_false,
    Bool.false_eq_true, ↓reduceIte, decide_true]

/-- **The seeded configuration is one `realCheck`'s pure core runs from.** -/
theorem runOk_g0s : RunOk g0s := by
  have hrv : uint.nat g0s.st.rv = 3 := rfl
  have hst : g0s.st = st3 := rfl
  have hall := histN_g0s_ok 3 (by omega)
  have h3 : histN g0s.hist 3 = st3 := rfl
  rw [h3] at hall
  refine ⟨⟨?_, ?_, ?_, by rw [hrv]; omega, fun q hq0 hq => ?_⟩, ⟨rfl, rfl, fun q hq0 hq => ?_⟩,
    fun r hr => ?_, ⟨fun r it hr hit => ?_, fun r ch hr2 hr ho => ?_⟩, by rw [hrv]; omega⟩
  · rw [hst]; exact hall.1
  · rw [hst]; exact fun it hit => (hall.2 it hit).1
  · rw [hst]
    exact rmWf_absR st3 fun it hit => (hall.2 it hit).2.2
  · rw [hrv] at hq
    rw [histAtL_g0s q hq0 (by rw [hrv]; exact hq), histN_g0s _ hq]
    rcases (by omega : uint.nat q = 1 ∨ uint.nat q = 2 ∨ uint.nat q = 3) with h | h | h <;>
      simp only [h] <;> simp [st1, st2, st3] <;> word
  · rw [hrv] at hq
    rw [histAtL_g0s q hq0 (by rw [hrv]; exact hq)]
    have := histN_g0s_ok _ hq
    exact ⟨this.1, fun it hit => (this.2 it hit).1⟩
  · exact (histN_g0s_ok r hr).1.1
  · have := (histN_g0s_ok r hr).2 it hit
    exact ⟨this.2.1, this.2.2, (histN_g0s_ok r hr).1.2 it hit⟩
  · have hr' : r = 2 ∨ r = 3 := by have : g0s.hist.length = 3 := rfl; omega
    rcases hr' with rfl | rfl
    · rw [show 2 - 1 = 1 from rfl, changeAt_g0s2] at ho
      cases ho
      exact ⟨fun o h => by cases h; exact ⟨by simp [DObj.toObj], rfl⟩, fun o h => by cases h⟩
    · rw [show 3 - 1 = 2 from rfl, changeAt_g0s3] at ho
      cases ho
      exact ⟨fun o h => by cases h; exact ⟨by simp [DObj.toObj], rfl⟩, fun o h => by cases h⟩

end pure

end k8s_etcd3
end EtcdGrove
end Perennial
