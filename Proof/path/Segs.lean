/-
**Rooted paths of plain segments** (rafthttp stage 5d): what `Clean`, `Join`, `Base` and `Dir`
give on the paths rafthttp builds (`/raft/stream/msgapp/<id>`). Lean-first; pure, over the
models of `Proof/path/Model.lean`.

A plain segment is non-empty, with neither `/` nor `.` (a member id's hexadecimal rendering, a
stream endpoint's elements). `segsPath segs` is `/s1/s2/.../sn`: `Clean` leaves it as it is, and
of `segsPath (segs ++ [s])`, `Base` is `s` and `Dir` is `segsPath segs`.
-/
module

public import Proof.path.Model

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace path

/-- A non-empty segment without `/` or `.`. -/
def plainSeg (s : List w8) : Prop := s ≠ [] ∧ ∀ c ∈ s, c ≠ slash ∧ c ≠ dot

instance : DecidablePred plainSeg := fun s => by unfold plainSeg; infer_instance

/-- `/s1/s2/.../sn`. -/
def segsPath (segs : List (List w8)) : List w8 := segs.foldl (fun acc s => acc ++ [slash] ++ s) []

theorem segsPath_foldl (acc : List w8) (segs : List (List w8)) :
    segs.foldl (fun acc s => acc ++ [slash] ++ s) acc = acc ++ segsPath segs := by
  induction segs generalizing acc with
  | nil => simp [segsPath]
  | cons s segs ih =>
    simp only [List.foldl_cons, segsPath]
    rw [ih, ih ([] ++ [slash] ++ s)]
    simp

theorem segsPath_append (a b : List (List w8)) : segsPath (a ++ b) = segsPath a ++ segsPath b := by
  rw [segsPath, List.foldl_append, segsPath_foldl]; rfl

theorem segsPath_cons (s : List w8) (b : List (List w8)) :
    segsPath (s :: b) = [slash] ++ s ++ segsPath b := by
  rw [show s :: b = [s] ++ b from rfl, segsPath_append]; simp [segsPath]

theorem segsPath_snoc (segs : List (List w8)) (s : List w8) :
    segsPath (segs ++ [s]) = segsPath segs ++ [slash] ++ s := by
  rw [segsPath_append]; simp [segsPath]

/-- A non-empty path starts with `/`, then a plain segment's first byte. -/
theorem segsPath_cons_ne (s : List w8) (b : List (List w8)) :
    ∃ rest, segsPath (s :: b) = slash :: rest := ⟨s ++ segsPath b, by rw [segsPath_cons]; simp⟩

theorem plainSeg_length (s : List w8) (h : plainSeg s) : 1 ≤ s.length := by
  cases s with | nil => exact absurd rfl h.1 | cons _ _ => simp

/-- What follows a segment in a path: the end, or a `/`. -/
theorem segsPath_tail (b : List (List w8)) (t : List w8) (ht : t = [] ∨ t.head? = some slash) :
    segsPath b ++ t = [] ∨ (segsPath b ++ t).head? = some slash := by
  cases b with
  | nil => simpa [segsPath] using ht
  | cons s b => right; obtain ⟨rest, h⟩ := segsPath_cons_ne s b; rw [h]; rfl

/-- The copy of a segment without `/`, followed by the end or a `/`. -/
theorem copyElem_seg (pre s rest o : List w8) (hs : ∀ c ∈ s, c ≠ slash)
    (hrest : rest = [] ∨ rest.head? = some slash) :
    copyElem (pre ++ s ++ rest) pre.length o = (pre.length + s.length, o ++ s) := by
  induction s generalizing pre o with
  | nil =>
    rw [copyElem_stop]
    · simp
    · rintro ⟨h1, h2⟩
      rcases hrest with rfl | hr
      · simp at h1
      · apply h2
        cases rest with
        | nil => simp at hr
        | cons x xs => simp at hr; subst hr; simp
  | cons c s ih =>
    have hc : c ≠ slash := hs c (by simp)
    rw [copyElem_step _ _ _ (by simp) (by simp; exact hc)]
    have h := ih (pre ++ [c]) (o ++ [c]) (fun x hx => hs x (by simp [hx]))
    have e1 : pre ++ [c] ++ s ++ rest = pre ++ c :: s ++ rest := by simp
    have e2 : (pre ++ [c]).length = pre.length + 1 := by simp
    rw [e1, e2] at h
    have e3 : (pre ++ c :: s ++ rest).getD pre.length 0 = c := by simp
    rw [e3, h]
    simp; omega

/-- A `/` is skipped. -/
theorem cleanLoop_slash (p : List w8) (rt : Bool) (r : Nat) (o : List w8) (dd : Nat)
    (hr : r < p.length) (h : p.getD r 0 = slash) :
    cleanLoop p rt r o dd = cleanLoop p rt (r + 1) o dd := by
  rw [cleanLoop_step _ _ _ _ _ hr, cleanStep, if_pos h]

/-- A plain segment of a rooted path is copied, after a `/` unless the output is the root. -/
theorem cleanLoop_seg (pre s rest o : List w8) (hs : plainSeg s)
    (hrest : rest = [] ∨ rest.head? = some slash) :
    cleanLoop (pre ++ s ++ rest) true pre.length o 1 =
      cleanLoop (pre ++ s ++ rest) true (pre.length + s.length)
        ((if o.length ≠ 1 then o ++ [slash] else o) ++ s) 1 := by
  obtain ⟨hne, hcs⟩ := hs
  obtain ⟨c, s', rfl⟩ : ∃ c s', s = c :: s' := by
    cases s with | nil => exact absurd rfl hne | cons c s' => exact ⟨c, s', rfl⟩
  have hc := hcs c (by simp)
  have hlen : pre.length < (pre ++ c :: s' ++ rest).length := by simp
  have hg : (pre ++ c :: s' ++ rest).getD pre.length 0 = c := by simp
  rw [cleanLoop_step _ _ _ _ _ hlen]
  have hcs' : ∀ x ∈ c :: s', x ≠ slash := fun x hx => (hcs x hx).1
  have hce := copyElem_seg pre (c :: s') rest (if o.length ≠ 1 then o ++ [slash] else o) hcs' hrest
  have Hst : cleanStep (pre ++ c :: s' ++ rest) true pre.length o 1 =
      (pre.length + (c :: s').length,
        (if o.length ≠ 1 then o ++ [slash] else o) ++ c :: s', 1) := by
    rw [cleanStep, if_neg (by rw [hg]; exact hc.1), if_neg (by rw [hg]; intro h; exact hc.2 h.1),
      if_neg (by rw [hg]; intro h; exact hc.2 h.1)]
    have e : (decide (true = true ∧ o.length ≠ 1) || decide ((!true) = true ∧ o.length ≠ 0)) =
        decide (o.length ≠ 1) := by simp
    simp only [Bool.not_true, Bool.false_eq_true, false_and, or_false, true_and]
    rw [hce]
  rw [Hst]

theorem segsPath_length_two (a : List (List w8)) (ha : a ≠ []) (hp : ∀ s ∈ a, plainSeg s) :
    2 ≤ (segsPath a).length := by
  cases a with
  | nil => exact absurd rfl ha
  | cons s b =>
    have := plainSeg_length s (hp s (by simp))
    rw [segsPath_cons]; simp; omega

/-- **A rooted path of plain segments, then the end or a `/`**: from the end of its first
segments `a`, `Clean`'s loop reaches the end of `a ++ b` with that path as its output. -/
theorem cleanLoop_segs (a b : List (List w8)) (t : List w8) (ha : a ≠ [])
    (hpa : ∀ s ∈ a, plainSeg s) (hb : ∀ s ∈ b, plainSeg s) (ht : t = [] ∨ t.head? = some slash) :
    cleanLoop (segsPath (a ++ b) ++ t) true (segsPath a).length (segsPath a) 1 =
      cleanLoop (segsPath (a ++ b) ++ t) true (segsPath (a ++ b)).length (segsPath (a ++ b)) 1 := by
  induction b generalizing a with
  | nil => simp
  | cons s b ih =>
    have hs := hb s (by simp)
    have hb' : ∀ s ∈ b, plainSeg s := fun x hx => hb x (by simp [hx])
    have hp : segsPath (a ++ s :: b) ++ t = (segsPath a ++ [slash]) ++ s ++ (segsPath b ++ t) := by
      rw [segsPath_append, segsPath_cons]; simp
    have h2 := segsPath_length_two a ha hpa
    have hpa' : ∀ x ∈ a ++ [s], plainSeg x := by
      intro x hx
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact hpa x hx
      · exact hs
    have ih' := ih (a ++ [s]) (by simp) hpa' hb'
    rw [show a ++ [s] ++ b = a ++ s :: b by simp, segsPath_snoc] at ih'
    have hlt : (segsPath a).length < (segsPath (a ++ s :: b) ++ t).length := by
      rw [hp]; simp
    have hsl : (segsPath (a ++ s :: b) ++ t).getD (segsPath a).length 0 = slash := by
      rw [hp]; simp
    rw [cleanLoop_slash _ _ _ _ _ hlt hsl]
    have hseg := cleanLoop_seg (segsPath a ++ [slash]) s (segsPath b ++ t) (segsPath a) hs
      (segsPath_tail b t ht)
    rw [← hp] at hseg
    have e1 : (segsPath a ++ [slash]).length = (segsPath a).length + 1 := by simp
    rw [e1, if_pos (by omega)] at hseg
    rw [hseg]
    have e2 : (segsPath a ++ [slash] ++ s).length = (segsPath a).length + 1 + s.length := by
      simp; omega
    rw [e2] at ih'
    exact ih'

/-- **`Clean` of a rooted path of plain segments, then the end or one `/`**: the path. -/
theorem cleanModel_segs (segs : List (List w8)) (t : List w8) (hne : segs ≠ [])
    (hp : ∀ s ∈ segs, plainSeg s) (ht : t = [] ∨ t = [slash]) :
    cleanModel (segsPath segs ++ t) = segsPath segs := by
  obtain ⟨s1, b, rfl⟩ : ∃ s1 b, segs = s1 :: b := by
    cases segs with | nil => exact absurd rfl hne | cons s1 b => exact ⟨s1, b, rfl⟩
  have hs1 := hp s1 (by simp)
  have hb : ∀ s ∈ b, plainSeg s := fun x hx => hp x (by simp [hx])
  have ht' : t = [] ∨ t.head? = some slash := by rcases ht with rfl | rfl <;> simp
  have hp1 : segsPath (s1 :: b) ++ t = [slash] ++ s1 ++ (segsPath b ++ t) := by
    rw [segsPath_cons]; simp
  have hpne : segsPath (s1 :: b) ++ t ≠ [] := by rw [hp1]; simp
  have hhead : (segsPath (s1 :: b) ++ t).getD 0 0 = slash := by rw [hp1]; simp
  unfold cleanModel
  rw [if_neg hpne]
  simp only [hhead, decide_true, ↓reduceIte]
  -- the first segment, after the root
  have hseg := cleanLoop_seg [slash] s1 (segsPath b ++ t) [slash] hs1 (segsPath_tail b t ht')
  rw [← hp1] at hseg
  simp only [List.length_singleton, ne_eq, not_true_eq_false, ↓reduceIte] at hseg
  rw [hseg]
  have hseg1 : [slash] ++ s1 = segsPath [s1] := by simp [segsPath]
  have e1 : 1 + s1.length = (segsPath [s1]).length := by rw [← hseg1]; simp; omega
  rw [hseg1, e1]
  have hall := cleanLoop_segs [s1] b t (by simp) (by simpa using hs1) hb ht'
  simp only [List.singleton_append] at hall
  rw [hall]
  -- the end, after at most one `/`
  have hlen : 1 ≤ (segsPath (s1 :: b)).length := by rw [segsPath_cons]; simp
  have hfin : cleanLoop (segsPath (s1 :: b) ++ t) true (segsPath (s1 :: b)).length
      (segsPath (s1 :: b)) 1 = segsPath (s1 :: b) := by
    rcases ht with rfl | rfl
    · rw [cleanLoop_stop _ _ _ _ _ (by simp)]
    · rw [cleanLoop_slash _ _ _ _ _ (by simp) (by simp), cleanLoop_stop _ _ _ _ _ (by simp)]
  rw [hfin, if_neg (by intro h; rw [h] at hlen; simp at hlen)]

/-! ### `Join`, `Base`, `Dir` -/

/-- `Join(segsPath segs, s)`: the path with `s` appended. -/
theorem joinModel_segs (segs : List (List w8)) (s : List w8) (hne : segs ≠ [])
    (hp : ∀ x ∈ segs, plainSeg x) (hs : plainSeg s) :
    joinModel [segsPath segs, s] = segsPath (segs ++ [s]) := by
  have hl := segsPath_length_two segs hne hp
  have h0 : segsPath segs ≠ [] := by intro h; rw [h] at hl; simp at hl
  have hA : 0 < (segsPath segs).length := by omega
  have hb : joinBuf [segsPath segs, s] [] = segsPath (segs ++ [s]) := by
    rw [segsPath_snoc]
    simp [joinBuf, h0, hA]
  have hsum : ([segsPath segs, s].map List.length).sum ≠ 0 := by
    intro h
    have : (segsPath segs).length ≤ ([segsPath segs, s].map List.length).sum := by simp
    omega
  unfold joinModel
  rw [if_neg hsum, hb]
  have := cleanModel_segs (segs ++ [s]) [] (by simp) (by
    intro x hx; simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hp x hx
    · exact hs) (Or.inl rfl)
  simpa using this

/-- The last `/` of `q ++ "/" ++ s`, for `s` without `/`. -/
theorem lastIndexByte_seg (q s : List w8) (hs : ∀ c ∈ s, c ≠ slash) :
    lastIndexByte (q ++ [slash] ++ s) slash = q.length := by
  unfold lastIndexByte
  have key : ∀ k, k ≤ s.length → lastIdxFrom (q ++ [slash] ++ s) slash (q.length + 1 + k) = q.length := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [show q.length + 1 + 0 = q.length + 1 by omega, lastIdxFrom, if_pos (by simp)]
    | succ k ih =>
      intro hk
      rw [show q.length + 1 + (k + 1) = (q.length + 1 + k) + 1 by omega, lastIdxFrom, if_neg]
      · exact ih (by omega)
      · have hsk : k < s.length := by omega
        have : (q ++ [slash] ++ s).getD (q.length + 1 + k) 0 = s[k] := by
          rw [List.getD_eq_getElem?_getD, List.append_assoc,
            List.getElem?_append_right (by omega)]
          rw [show q.length + 1 + k - q.length = k + 1 by omega]
          simp [hsk]
        rw [this]; exact hs _ (List.getElem_mem hsk)
  have := key s.length (Nat.le_refl _)
  simp only [List.length_append, List.length_singleton] at this ⊢
  rw [show q.length + 1 + s.length = q.length + (1 + s.length) by omega] at this
  rw [show q.length + 1 + s.length = q.length + (1 + s.length) by omega]
  exact this

/-- `Base(q ++ "/" ++ s)` of a plain segment `s`: `s`. -/
theorem baseModel_seg (q s : List w8) (hs : plainSeg s) : baseModel (q ++ [slash] ++ s) = s := by
  obtain ⟨hne, hcs⟩ := hs
  obtain ⟨s', x, rfl⟩ : ∃ s' x, s = s' ++ [x] := by
    cases h : s.reverse with
    | nil => exact absurd (List.reverse_eq_nil_iff.1 h) hne
    | cons x r => exact ⟨r.reverse, x, by rw [← List.reverse_reverse s, h]; simp⟩
  have hx : x ≠ slash := (hcs x (by simp)).1
  have hst : stripSlashes (q ++ [slash] ++ (s' ++ [x])) = q ++ [slash] ++ (s' ++ [x]) := by
    rw [show q ++ [slash] ++ (s' ++ [x]) = (q ++ [slash] ++ s') ++ [x] by simp,
      stripSlashes_snoc_ne _ _ hx]
  have hl := lastIndexByte_seg q (s' ++ [x]) (fun c hc => (hcs c hc).1)
  unfold baseModel
  rw [if_neg (by simp)]
  simp only [hst, hl]
  simp

/-- `Dir(segsPath segs ++ "/" ++ s)` of a plain segment `s`: `segsPath segs`. -/
theorem dirModel_segs (segs : List (List w8)) (s : List w8) (hne : segs ≠ [])
    (hp : ∀ x ∈ segs, plainSeg x) (hs : plainSeg s) :
    dirModel (segsPath segs ++ [slash] ++ s) = segsPath segs := by
  have hl := lastIndexByte_seg (segsPath segs) s (fun c hc => (hs.2 c hc).1)
  unfold dirModel splitModel
  rw [hl]
  have : (((segsPath segs).length : Int) + 1).toNat = (segsPath segs).length + 1 := by omega
  rw [this]
  have ht : List.take ((segsPath segs).length + 1) (segsPath segs ++ [slash] ++ s) =
      segsPath segs ++ [slash] := by
    rw [List.append_assoc, List.take_append]; simp [List.take_of_length_le]
  simp only [ht]
  exact cleanModel_segs segs [slash] hne hp (Or.inr rfl)

end path
end EtcdGrove
end Perennial
