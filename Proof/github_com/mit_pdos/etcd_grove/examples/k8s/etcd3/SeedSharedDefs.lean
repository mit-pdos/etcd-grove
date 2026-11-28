/-
Lean-first (no Rocq counterpart).

# The seeded history of the shared store (k8s-dist K9 §2.8: `SeedShared`'s pure half)

- `seedStepL h k rv`: one seed `Put` of `SeedShared`/`SeededAt`'s loop: the store `h.st` repeated at
  each revision strictly between its own and `rv` (writes of others), then the store with `k`'s seed
  item at `rv`;
- `seedSharedL r1 r2`: the history from the empty store at revision 1, the seeds `ns-1/pod-1` at `r1`
  and `ns-2/pod-2` at `r2`;
- `seedSharedL_ok`: for `1 < r1 < r2` it is what `Seeded.SharedModel` and K4's `FullComplete` take of
  a seeded store: `HWf`, its items' revisions at most its own, a revision of at least 2, at most two
  items.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Seed
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.KSteps
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.dist.SharedHist
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.SharedDefs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore)

section pure
variable [GooseExts]

/-- The stores `SeededAt`'s inner loop appends: `items` at each revision from `lo` up to, not
including, `hi`. -/
def padL (items : List item) (lo hi : Nat) : List GSt :=
  (List.range' lo (hi - lo)).map fun (r : Nat) => (⟨items, W64 (r : Int)⟩ : GSt)

/-- One seed `Put` (see the file header). -/
def seedStepL (h : HSt) (k : GoString) (rv : w64) : HSt :=
  let st' : GSt := ⟨setItemL h.st.items (seedItem k rv), rv⟩
  ⟨st', h.hist ++ padL h.st.items (uint.nat h.st.rv + 1) (uint.nat rv) ++ [st']⟩

/-- The empty store at revision 1, its own history. -/
def seedInitL : HSt := ⟨⟨[], W64 1⟩, [⟨[], W64 1⟩]⟩

/-- **The seeded shared store** (see the file header). -/
def seedSharedL (r1 r2 : w64) : HSt := seedStepL (seedStepL seedInitL kA r1) kB r2

/-- The history after the first `n` seeds (`n ≤ 2`). -/
def seedPrefL (r1 r2 : w64) (n : Nat) : HSt :=
  if n = 0 then seedInitL else if n = 1 then seedStepL seedInitL kA r1 else seedSharedL r1 r2

/-- The items of every store of `h`'s history, and of `h.st`, carry revisions at most `h.st.rv`. -/
def ItemsBelow (h : HSt) : Prop :=
  (∀ g ∈ h.hist, ∀ it ∈ g.items, uint.nat it.obj'.ResourceVersion' ≤ uint.nat h.st.rv) ∧
  (∀ it ∈ h.st.items, uint.nat it.obj'.ResourceVersion' ≤ uint.nat h.st.rv)

theorem padL_length (items : List item) (lo hi : Nat) : (padL items lo hi).length = hi - lo := by
  simp [padL]

theorem padL_snoc (items : List item) (lo hi : Nat) (h : lo ≤ hi) :
    padL items lo (hi + 1) = padL items lo hi ++ [⟨items, W64 (hi : Int)⟩] := by
  unfold padL
  rw [show hi + 1 - lo = (hi - lo) + 1 by omega, List.range'_concat, List.map_append]
  simp only [List.map_cons, List.map_nil]
  rw [show lo + 1 * (hi - lo) = hi by omega]

theorem padL_self (items : List item) (lo : Nat) : padL items lo lo = [] := by simp [padL]

theorem seedStepL_wf {h : HSt} {k : GoString} {rv : w64} (hw : HWf h)
    (hlt : uint.nat h.st.rv < uint.nat rv) : HWf (seedStepL h k rv) := by
  obtain ⟨h1, h2⟩ := hw
  refine ⟨?_, ?_⟩
  · simp only [seedStepL, List.length_append, padL_length, List.length_singleton, h1]
    omega
  · simp [seedStepL]

theorem seedStepL_below {h : HSt} {k : GoString} {rv : w64} (hb : ItemsBelow h)
    (hlt : uint.nat h.st.rv < uint.nat rv) : ItemsBelow (seedStepL h k rv) := by
  obtain ⟨h1, h2⟩ := hb
  have hst : ∀ it ∈ setItemL h.st.items (seedItem k rv),
      uint.nat it.obj'.ResourceVersion' ≤ uint.nat rv := by
    intro it hit
    rcases k8s_dist.setItemL_mem _ _ _ hit with rfl | hit
    · simp [seedItem]
    · exact Nat.le_trans (h2 it hit) (Nat.le_of_lt hlt)
  refine ⟨fun g hg it hit => ?_, hst⟩
  simp only [seedStepL, List.mem_append, List.mem_singleton] at hg
  rcases hg with (hg | hg) | rfl
  · exact Nat.le_trans (h1 g hg it hit) (Nat.le_of_lt hlt)
  · simp only [padL, List.mem_map] at hg
    obtain ⟨_, _, rfl⟩ := hg
    exact Nat.le_trans (h2 it hit) (Nat.le_of_lt hlt)
  · exact hst it hit

/-- **The seeded shared store is a seeded store** (see the file header). -/
theorem seedSharedL_ok (r1 r2 : w64) (h1 : 1 < uint.nat r1) (h12 : uint.nat r1 < uint.nat r2) :
    HWf (seedSharedL r1 r2) ∧
    (∀ g ∈ (seedSharedL r1 r2).hist, ∀ it ∈ g.items,
      uint.nat it.obj'.ResourceVersion' ≤ uint.nat (seedSharedL r1 r2).st.rv) ∧
    (seedSharedL r1 r2).st.rv = r2 ∧ 2 ≤ uint.nat (seedSharedL r1 r2).st.rv ∧
    (seedSharedL r1 r2).st.items.length ≤ 2 := by
  have hi0 : uint.nat seedInitL.st.rv = 1 := by simp [seedInitL]
  have w0 : HWf seedInitL := ⟨by simp [seedInitL], rfl⟩
  have b0 : ItemsBelow seedInitL := ⟨by simp [seedInitL], by simp [seedInitL]⟩
  have hA : uint.nat (seedStepL seedInitL kA r1).st.rv = uint.nat r1 := rfl
  refine ⟨seedStepL_wf (seedStepL_wf w0 (by omega)) (by omega),
    (seedStepL_below (seedStepL_below b0 (by omega)) (by omega)).1, rfl, by
      show 2 ≤ uint.nat r2; omega, ?_⟩
  show (setItemL (setItemL [] (seedItem kA r1)) (seedItem kB r2)).length ≤ 2
  have a := setItemL_length (setItemL [] (seedItem kA r1)) (seedItem kB r2)
  have b := setItemL_length ([] : List item) (seedItem kA r1)
  simp only [List.length_nil] at b
  omega

end pure

end k8s_etcd3
end EtcdGrove
end Perennial
