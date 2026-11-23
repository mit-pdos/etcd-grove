/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/jsoncodec/Frame.lean (lab master 915f964;
notes/dsv-vr.md).
-/
/-
The framing facts of the events' encodings, pure: the scanner on a line and on a strict
prefix of one, validity, and unique framing of a stream of lines (`lines_prefix`).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.jsoncodec.Inj

@[expose] public section

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace VsrJson

open Perennial VsrModel

theorem decN_iff (a b : Nat) : decN a = decN b ↔ a = b :=
  ⟨decN_inj a b, fun h => by rw [h]⟩

theorem logJV_inj (e e' : Entry) (h : logJV e = logJV e') : e = e' := by
  obtain ⟨o, c, r⟩ := e; obtain ⟨o', c', r'⟩ := e'
  simp [logJV, mkObj, qn, decN_iff] at h
  obtain ⟨rfl, rfl, rfl⟩ := h; rfl

theorem logsJV_inj (es es' : List Entry) (h : logsJV es = logsJV es') : es = es' := by
  simp only [logsJV, JV.arr.injEq] at h
  induction es generalizing es' with
  | nil => cases es' with
    | nil => rfl
    | cons _ _ => simp [mkArr] at h
  | cons e es ih => cases es' with
    | nil => simp [mkArr] at h
    | cons e' es' =>
      simp only [List.map_cons, mkArr, JVs.cons.injEq] at h
      rw [logJV_inj e e' h.1, ih es' h.2]

theorem logsJV_iff (es es' : List Entry) : logsJV es = logsJV es' ↔ es = es' :=
  ⟨logsJV_inj es es', fun h => by rw [h]⟩

theorem evJV_inj (m m' : Msg) (h : evJV m = evJV m') : m = m' := by
  simp only [evJV, mkObj, JV.obj.injEq, JMs.cons.injEq, JV.num.injEq, true_and] at h
  obtain ⟨ht, hp, -⟩ := h
  cases m <;> cases m' <;> simp [typeN] at ht <;>
    simp [payJV, mkObj, qn, reqJV, decN_iff, logsJV_iff] at hp ⊢ <;> (try exact hp)
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hp
    refine ⟨h1, h2, h3, ?_, h5⟩
    obtain ⟨a, b, c⟩ := h4
    rename_i e1 _ _ _ _ e2 _
    cases e1; cases e2; simp_all
  · rename_i d1 d2
    obtain ⟨h1, h2, h3, -, h5, h6⟩ := hp
    cases d1; cases d2; simp_all

theorem encEvent_plain (m : Msg) (hm : PlainMsg m) : encEvent m = ser (evJV m) := by
  simp [encEvent, hm]

theorem encEvent_ne_nil (m : Msg) : encEvent m ≠ [] := by
  unfold encEvent; split
  · simp [evJV, ser]
  · simp

theorem evJV_maxd (m : Msg) : (evJV m).depth ≤ maxDepth := by
  have := evJV_depth m; simp only [maxDepth]; omega

/-- The scanner on a line's value after whitespace: done at its end. -/
theorem scanL_line (ws : List w8) (m : Msg) (rest : List w8) (eof : Bool)
    (hws : ∀ c ∈ ws, spB c = true) (hm : PlainMsg m) :
    scanL (ws ++ encEvent m ++ rest) eof = (0, ws.length + (encEvent m).length) := by
  rw [encEvent_plain m hm, scanL, List.append_assoc, goL_spaces ws _ hws]
  rw [top_v (evJV m) (evJV_ok m hm) rest _ false eof (evJV_maxd m) (by simp [evJV, termOK])]
  simp

/-- The scanner on whitespace and a strict prefix of a value: more. -/
theorem scanL_partial_v (eof : Bool) (ws pre : List w8) (v : JV) (hv : v.ok)
    (hd : v.depth ≤ maxDepth) (hn : ∀ n, v = .num n → eof = false)
    (hws : ∀ c ∈ ws, spB c = true) (hpre : pre <+: ser v) (hne : pre ≠ ser v) :
    (scanL (ws ++ pre) eof).1 = 1 := by
  rw [scanL, goL_spaces ws _ hws]
  exact part_v eof v hv [] (by simpa using hd) (fun n h => by simp [hn n h]) pre hpre
    (Or.inr hne) _ _

/-- The scanner on whitespace and a strict prefix of an event's encoding: more (at the end of
the stream too: an event is an object). -/
theorem scanL_partial (eof : Bool) (ws pre : List w8) (m : Msg) (hws : ∀ c ∈ ws, spB c = true)
    (hm : PlainMsg m) (hpre : pre <+: encEvent m) (hne : pre ≠ encEvent m) :
    (scanL (ws ++ pre) eof).1 = 1 := by
  rw [encEvent_plain m hm] at hpre hne
  exact scanL_partial_v eof ws pre (evJV m) (evJV_ok m hm) (evJV_maxd m)
    (fun n h => by simp [evJV] at h) hws hpre hne

/-- The scanner on whitespace only: more. -/
theorem scanL_space (ws : List w8) (eof : Bool) (hws : ∀ c ∈ ws, spB c = true) :
    scanL ws eof = (1, ws.length) := by
  have := goL_spaces ws [] hws 0 [] 0 false eof
  rw [List.append_nil] at this
  rw [scanL, this, goL_nil]; simp

/-- A whole value after whitespace and before whitespace: what `jsonValid` asks, as `scanL`. -/
theorem scanL_value (ws : List w8) (v : JV) (hv : v.ok) (hd : v.depth ≤ maxDepth)
    (hws : ∀ c ∈ ws, spB c = true) (ht : termOK v []) :
    scanL (ws ++ ser v) true = (0, ws.length + (ser v).length) := by
  rw [scanL, goL_spaces ws _ hws]
  have := top_v v hv [] ws.length false true hd ht
  rw [List.append_nil] at this
  rw [Nat.zero_add, this]

/-- Two lines of valid messages that start the same stream are the same (the second message's
strings are plain). -/
theorem frame_unique (m m' : Msg) (X X' : List w8) (hm' : PlainMsg m')
    (h : encEvent m ++ 10#8 :: X = encEvent m' ++ 10#8 :: X') : m = m' ∧ X = X' := by
  by_cases hm : PlainMsg m
  · rw [encEvent_plain m hm, encEvent_plain m' hm'] at h
    obtain ⟨h1, h2⟩ := split_v _ _ _ _ (evJV_ok m hm) (evJV_ok m' hm') (evJV_maxd m)
      (evJV_maxd m') (by simp [evJV, termOK]) (by simp [evJV, termOK]) h
    refine ⟨evJV_inj m m' (ser_inj _ _ (evJV_ok m hm) (evJV_ok m' hm') (evJV_maxd m)
      (evJV_maxd m') h1), by simpa using h2⟩
  · rw [encEvent_plain m' hm'] at h
    simp [encEvent, hm, evJV, ser] at h
    exact absurd h.1 (by decide)

/-- The lines of messages. -/
noncomputable def linesL (ms : List Msg) : List w8 := (ms.map (fun m => encEvent m ++ [10#8])).flatten

/-- If the lines of `ms` start the lines of `ms'` (plain), `ms` starts `ms'`. -/
theorem lines_prefix (ms ms' : List Msg) (hms' : ∀ m ∈ ms', PlainMsg m)
    (h : linesL ms <+: linesL ms') : ms <+: ms' := by
  induction ms generalizing ms' with
  | nil => exact List.nil_prefix
  | cons m t ih =>
    cases ms' with
    | nil =>
      simp only [linesL, List.map_cons, List.flatten_cons, List.map_nil, List.flatten_nil,
        List.prefix_nil, List.append_eq_nil_iff] at h
      exact absurd h.1.1 (encEvent_ne_nil m)
    | cons m' t' =>
      obtain ⟨z, hz⟩ := h
      simp only [linesL, List.map_cons, List.flatten_cons, List.append_assoc,
        List.singleton_append, List.cons_append] at hz
      obtain ⟨rfl, h2⟩ := frame_unique m m' _ _ (hms' m' (by simp)) hz
      have : linesL t <+: linesL t' := ⟨z, by simpa [linesL] using h2⟩
      exact List.cons_prefix_cons.2 ⟨rfl, ih t' (fun x hx => hms' x (by simp [hx])) this⟩

end VsrJson
