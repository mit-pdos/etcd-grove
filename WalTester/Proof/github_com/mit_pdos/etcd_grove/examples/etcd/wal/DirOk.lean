/- Lean-first (no Rocq counterpart).

# `dirOk` (`examples/etcd/wal/wal.go`): the directories `Main` accepts

`dirOk(p)` scans `p` after its leading `/` one byte at a time (`tStep`), keeping whether every
component so far was accepted, the current component's length and whether it is all `.`; a component
is accepted by `compOk` (`tCompOk`: nonempty, neither `.` nor `..`, at most 255 bytes). A `true` result
means `tDirOk p`: `p` is `/s₁/…/sₙ` (`n ≥ 1`) of clean segments of at most 255 bytes, shorter than
4000 bytes (`tScan_sound`). Of the area and the oracle's directory, that gives the facts the tester's
proof takes of them (`tArgsOk`, `tArgsOk_of`).
-/
module

public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.RestartOk
public import Proof.path.Segs
public import GooseLang.Ext.Fs.PathFitsLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Fs WalFs _root_.Perennial.EtcdGrove.path

/-! ## The scan -/

/-- `compOk(n, dots)`: a component of `n` bytes, all `.` if `dots`, is nonempty, neither `.` nor `..`,
and at most 255 bytes. -/
def tCompOk (n : Nat) (dots : Bool) : Bool := n != 0 && decide (n ≤ 255) && !(dots && decide (n ≤ 2))

/-- One byte of `dirOk`'s loop on its state `(ok, n, dots)`. -/
def tStep (st : Bool × Nat × Bool) (c : w8) : Bool × Nat × Bool :=
  if c = slash then (st.1 && tCompOk st.2.1 st.2.2, 0, true)
  else (st.1, st.2.1 + 1, st.2.2 && decide (c = dot))

/-- `dirOk`'s result from the loop's final state. -/
def tFinal (st : Bool × Nat × Bool) : Bool := st.1 && tCompOk st.2.1 st.2.2

/-- **A directory `dirOk` accepts**: `/s₁/…/sₙ`, `n ≥ 1`, of clean segments of at most 255 bytes,
shorter than 4000 bytes. -/
def tDirOk (p : GoString) : Prop :=
  ∃ segs : List (List w8), segs ≠ [] ∧ (∀ s ∈ segs, cleanSeg s ∧ s.length ≤ 255) ∧
    p = segsPath segs ∧ p.length < 4000

theorem tScan_false (q : List w8) (n : Nat) (d : Bool) :
    (q.foldl tStep (false, n, d)).1 = false := by
  induction q generalizing n d with
  | nil => rfl
  | cons c q ih =>
    simp only [List.foldl_cons, tStep]
    split
    · exact ih _ _
    · exact ih _ _

theorem tCompOk_seg {s : List w8} (hs : ∀ c ∈ s, c ≠ slash)
    (h : tCompOk s.length (s.all (· = dot)) = true) : cleanSeg s ∧ s.length ≤ 255 := by
  simp only [tCompOk, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, Bool.not_eq_true',
    Bool.and_eq_false_imp, List.all_eq_true] at h
  obtain ⟨⟨h0, h255⟩, hd⟩ := h
  refine ⟨⟨fun e => h0 (by rw [e]; rfl), hs, ?_, ?_⟩, h255⟩
  · rintro rfl; simp at hd
  · rintro rfl; simp at hd

/-- **The scan's soundness**, from a component `s` read so far: a `true` result means `/s` and the
rest `q` are clean segments. -/
theorem tScan_sound (q s : List w8) (hs : ∀ c ∈ s, c ≠ slash)
    (h : tFinal (q.foldl tStep (true, s.length, s.all (· = dot))) = true) :
    ∃ segs : List (List w8), segs ≠ [] ∧ (∀ x ∈ segs, cleanSeg x ∧ x.length ≤ 255) ∧
      slash :: (s ++ q) = segsPath segs := by
  induction q generalizing s with
  | nil =>
    refine ⟨[s], by simp, ?_, by simp [segsPath]⟩
    intro x hx
    simp only [List.mem_singleton] at hx
    subst hx
    exact tCompOk_seg hs (by simpa [tFinal] using h)
  | cons c q ih =>
    simp only [List.foldl_cons, tStep] at h
    split at h
    · next hc =>
      subst hc
      cases hk : tCompOk s.length (s.all (· = dot))
      · rw [hk] at h
        simp [tFinal, tScan_false] at h
      · rw [hk] at h
        obtain ⟨segs, hne, hgood, hp⟩ :=
          ih [] (by simp) (by simpa using h)
        refine ⟨s :: segs, by simp, ?_, ?_⟩
        · intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact tCompOk_seg hs hk
          · exact hgood x hx
        · rw [segsPath_cons, ← hp]
          simp
    · next hc =>
      have e1 : s.length + 1 = (s ++ [c]).length := by simp
      have e2 : (s.all (· = dot) && decide (c = dot)) = (s ++ [c]).all (· = dot) := by simp
      rw [e1, e2] at h
      obtain ⟨segs, hne, hgood, hp⟩ := ih (s ++ [c]) (by
        intro x hx
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hs x hx
        · exact hc) h
      exact ⟨segs, hne, hgood, by rw [← hp]; simp⟩

/-- **`dirOk`'s result is sound**: `true` only for a directory `tDirOk` accepts. -/
theorem tDirOk_of_scan (p : GoString) (hl : p.length < 4000) (h0 : p[0]? = some slash)
    (h : tFinal ((p.drop 1).foldl tStep (true, 0, true)) = true) : tDirOk p := by
  obtain ⟨segs, hne, hgood, hp⟩ := tScan_sound (p.drop 1) [] (by simp) (by simpa using h)
  refine ⟨segs, hne, hgood, ?_, hl⟩
  rw [← hp]
  cases p with
  | nil => simp at h0
  | cons c q => simp at h0; subst h0; rfl

/-! ## The tester's facts of its directories -/

/-- **The facts the tester's proof takes of its directories**: the oracle file one `durable` can
manage (`DFile.Ok`), the WAL's paths the area's (`tWalPathsOk`), and the WAL directory and its
`.tmp` fitting (`PathFits`). -/
def tArgsOk (e : TEnv) : Prop :=
  e.orFile.Ok ∧ tWalPathsOk e.area ∧ PathFits (tWalDir e.area ++ go!".tmp") ∧ PathFits (tWalDir e.area)

theorem segsPath_flatten (segs : List (List w8)) :
    segsPath segs = (segs.map (go!"/" ++ ·)).flatten := by
  induction segs with
  | nil => rfl
  | cons s segs ih =>
    rw [segsPath_cons, ih]
    simp only [List.map_cons, List.flatten_cons]
    rfl

theorem winOk_foldl (segs : List (List w8)) (h : ∀ s ∈ segs, s.length ≤ 255) :
    ∀ acc : List w8, WinOk acc → WinOk (segs.foldl (fun a s => a ++ [slash] ++ s) acc) := by
  induction segs with
  | nil => intro acc ha; exact ha
  | cons s segs ih =>
    intro acc ha
    simp only [List.foldl_cons]
    refine ih (fun x hx => h x (by simp [hx])) _ ?_
    have := winOk_child ha (h s (by simp))
    simpa [child, slashB] using this

theorem winOk_segsPath (segs : List (List w8)) (h : ∀ s ∈ segs, s.length ≤ 255) :
    WinOk (segsPath segs) :=
  winOk_foldl segs h [] (winOk_short (by simp))

theorem tArgsOk_of (e : TEnv) (ha : tDirOk e.area) (ho : tDirOk e.orDir) : tArgsOk e := by
  obtain ⟨sa, ahne, agood, ahp, ahl⟩ := ha
  obtain ⟨os, ohne, ogood, ohp, ohl⟩ := ho
  have hwin : WinOk e.area := ahp ▸ winOk_segsPath sa (fun s hs => (agood s hs).2)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, by decide, ?_, ?_⟩, ?_, ?_⟩
  rotate_left 1
  · show cleanSeg tOrBase; unfold cleanSeg tOrBase; decide
  · show cleanSeg (go!".durable-" ++ tOrBase); unfold cleanSeg tOrBase; decide
  · show NameOk tOrBase; unfold tOrBase; decide
  · show NameOk (go!".durable-" ++ tOrBase); unfold tOrBase; decide
  rotate_right 1
  · exact ⟨os, ohne, fun s hs => (ogood s hs).1, ohp⟩
  · show e.orDir.length + (go!".durable-state").length < 2 ^ 40
    have : (go!".durable-state" : GoString).length = 14 := by decide
    omega
  · exact ⟨by unfold walNameOk; decide, by simp only [tWalDir, List.append_assoc]; rfl⟩
  · refine ⟨sa, ahne, fun c hc => ?_, by rw [ahp, segsPath_flatten]⟩
    obtain ⟨⟨h1, h2, h3, h4⟩, -⟩ := agood c hc
    exact ⟨h1, fun hm => h2 _ hm rfl, h3, h4⟩
  · have : (go!"/wal" : GoString).length = 4 := by decide
    simp only [tWalDir, List.length_append, this]
    omega
  · have e1 : tWalDir e.area ++ go!".tmp" = child e.area go!"wal.tmp" := by
      simp only [tWalDir, child, List.append_assoc]; rfl
    rw [e1]
    exact pathFits_child hwin (by decide) (by
      have : (go!"wal.tmp" : GoString).length = 7 := by decide
      omega)
  · have e1 : tWalDir e.area = child e.area go!"wal" := by
      simp only [tWalDir, child]; rfl
    rw [e1]
    exact pathFits_child hwin (by decide) (by
      have : (go!"wal" : GoString).length = 3 := by decide
      omega)

end etcd_wal
end EtcdGrove
end Perennial
