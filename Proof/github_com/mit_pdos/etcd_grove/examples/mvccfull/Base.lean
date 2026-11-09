/-
The full tester of mvcc (`examples/mvccfull`, `notes/mvccfull-proof-plan.md`): its package fact and
its keys. Lean-first (no Rocq counterpart).

`mvccfull` has no package variable and no `init()`: its fact is `True`. Its keys are not a package
variable (as `mvccrand`'s `keys` is) but computed by `walkKeys(nil, "", cfg.Depth)` and kept in
`runner.keys`: the strings over `a`, `b`, `c` of length `1` to the depth, in increasing order
(`keysOf`, `keysOf_sorted`). The model (`Model.lean`, ...) takes the keys as a parameter `ks` with
`ks.Pairwise go.GoStringLt`.
-/
module

public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.mvccfull
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace github_com.mit_pdos.etcd_grove.examples.mvccfull

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccfull :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccfull :=
  build_get_is_pkg_init_wf

end init

end github_com.mit_pdos.etcd_grove.examples.mvccfull

namespace EtcdGrove
namespace mvccfull

/-! ## The keys (`walkKeys`) -/

/-- The three letters `walkKeys` extends a prefix with, in increasing order. -/
def keyLetters : List w8 := [W8 97, W8 98, W8 99]

/-- **`walkKeys(ks, p, depth)`'s appended keys** with `n = depth - len(p)` letters left to add: `p`
itself unless empty, then the extensions of `p+"a"`, `p+"b"`, `p+"c"` (Go's recursion). -/
def walkM (p : GoString) : Nat → List GoString
  | 0 => if p = [] then [] else [p]
  | n + 1 => (if p = [] then [] else [p]) ++ walkM (p ++ [W8 97]) n ++ walkM (p ++ [W8 98]) n ++
      walkM (p ++ [W8 99]) n

/-- **The tester's keys at depth `d`** (`walkKeys(nil, "", d)`): the strings over `a`, `b`, `c` of
length `1` to `d`, in increasing order. -/
def keysOf (d : Nat) : List GoString := walkM [] d

/-- The suffixes (the empty one first) of length at most `n` over the letters, in increasing
order. -/
def walkS : Nat → List GoString
  | 0 => [[]]
  | n + 1 => [] :: ((walkS n).map (W8 97 :: ·) ++ (walkS n).map (W8 98 :: ·) ++
      (walkS n).map (W8 99 :: ·))

theorem walkM_eq (p : GoString) (n : Nat) :
    walkM p n = ((walkS n).map (p ++ ·)).filter (fun s => !decide (s = [])) := by
  induction n generalizing p with
  | zero => by_cases hp : p = [] <;> simp [walkM, walkS, hp]
  | succ n ih =>
    have hne : ∀ (x : w8) (l : List GoString),
        ((l.map ((p ++ [x]) ++ ·)).filter (fun s => !decide (s = []))) = l.map ((p ++ [x]) ++ ·) := by
      intro x l
      rw [List.filter_eq_self]
      intro s hs
      obtain ⟨t, -, rfl⟩ := List.mem_map.1 hs
      simp
    simp only [walkM, walkS, ih, List.map_cons, List.map_append, List.filter_cons,
      List.filter_append, List.append_nil]
    rw [hne, hne, hne]
    have hf : ∀ (q : GoString) (x : w8) (l : List GoString),
        (l.map (fun s => q ++ x :: s)).filter (fun s => !decide (s = [])) =
          l.map (fun s => q ++ x :: s) := by
      intro q x l
      rw [List.filter_eq_self]
      intro s hs
      obtain ⟨t, -, rfl⟩ := List.mem_map.1 hs
      simp
    have hf0 : ∀ (x : w8) (l : List GoString),
        (l.map (fun s => x :: s)).filter (fun s => !decide (s = [])) = l.map (fun s => x :: s) :=
      fun x l => by have h := hf [] x l; simp only [List.nil_append] at h; exact h
    simp only [List.map_map, Function.comp_def, List.append_assoc, List.cons_append,
      List.nil_append]
    by_cases hp : p = [] <;> simp [hp, hf, hf0]

theorem goStringLt_append_left (p s t : GoString) :
    go.GoStringLt (p ++ s) (p ++ t) ↔ go.GoStringLt s t := by
  induction p with
  | nil => rfl
  | cons x p ih =>
    rw [List.cons_append, List.cons_append, go.goStringLt_cons_iff]
    constructor
    · rintro (h | ⟨-, h⟩)
      · exact absurd h (Int.lt_irrefl _)
      · exact ih.1 h
    · intro h; exact Or.inr ⟨rfl, ih.2 h⟩

theorem walkS_sorted (n : Nat) : (walkS n).Pairwise go.GoStringLt := by
  induction n with
  | zero => simp [walkS]
  | succ n ih =>
    have hc : ∀ x : w8, ((walkS n).map (x :: ·)).Pairwise go.GoStringLt := fun x =>
      List.pairwise_map.2 (ih.imp fun h => (go.goStringLt_cons_iff _ _ _ _).2 (Or.inr ⟨rfl, h⟩))
    have hx : ∀ (x y : w8), uint.Z x < uint.Z y → ∀ a ∈ (walkS n).map (x :: ·),
        ∀ b ∈ (walkS n).map (y :: ·), go.GoStringLt a b := by
      intro x y hxy a ha b hb
      obtain ⟨s, -, rfl⟩ := List.mem_map.1 ha
      obtain ⟨t, -, rfl⟩ := List.mem_map.1 hb
      exact (go.goStringLt_cons_iff _ _ _ _).2 (Or.inl hxy)
    have hab : uint.Z (W8 97) < uint.Z (W8 98) := by decide
    have hbc : uint.Z (W8 98) < uint.Z (W8 99) := by decide
    have hac : uint.Z (W8 97) < uint.Z (W8 99) := by decide
    simp only [walkS]
    refine List.pairwise_cons.2 ⟨?_, ?_⟩
    · intro a ha
      simp only [List.mem_append, List.mem_map] at ha
      rcases ha with (⟨s, -, rfl⟩ | ⟨s, -, rfl⟩) | ⟨s, -, rfl⟩ <;> exact go.goStringLt_nil_cons _ _
    · refine List.pairwise_append.2 ⟨List.pairwise_append.2 ⟨hc _, hc _, hx _ _ hab⟩, hc _, ?_⟩
      intro a ha b hb
      rcases List.mem_append.1 ha with ha | ha
      · exact hx _ _ hac a ha b hb
      · exact hx _ _ hbc a ha b hb

/-- **The keys are strictly increasing.** -/
theorem keysOf_sorted (d : Nat) : (keysOf d).Pairwise go.GoStringLt := by
  unfold keysOf
  rw [walkM_eq]
  exact (List.pairwise_map.2 ((walkS_sorted d).imp fun h =>
    (goStringLt_append_left [] _ _).2 h)).filter _

theorem keysOf_nodup (d : Nat) : (keysOf d).Nodup :=
  (keysOf_sorted d).imp fun {a b} h (e : a = b) => go.goStringLt_irrefl a (by rw [e] at h ⊢; exact h)

/-- Every key is non-empty (the watch ranges' probe, `covers_eq_inRangeM`, needs it). -/
theorem keysOf_ne_nil (d : Nat) : ∀ k ∈ keysOf d, k ≠ [] := by
  intro k hk
  unfold keysOf at hk
  rw [walkM_eq] at hk
  simpa using (List.mem_filter.1 hk).2

/-- At depth `1` or more, `"a"` is a key (so there are keys). -/
theorem keysOf_ne (d : Nat) (hd : 1 ≤ d) : keysOf d ≠ [] := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  unfold keysOf
  cases n <;> simp [walkM]

end mvccfull
end EtcdGrove
end Perennial
