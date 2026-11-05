/-
A directory's ghost view (`DirG`) as a function of the namespace's history: the namespace a
generation booted with, `H0`, and the operations logged since, `H` (`dview H0 H d`). Each
operation changes `d`'s entries by `lopFor`: the one `LOp` of a file operation of `d` (`put`,
`del`, `mv`), otherwise the entries' difference (`lopsDiff`). Untrusted.
-/
module

public import GooseLang.Ext.OsFs.NsLemmas

@[expose] public section

noncomputable section

namespace Perennial

/-! ## The difference of two directories' entries -/

theorem lreplay_setTo (e2 : Ents) (K : List GoString) (m : Ents) (c : GoString) :
    lreplay (K.map (setTo e2)) m !! c = if c ∈ K then e2 !! c else m !! c := by
  induction K generalizing m with
  | nil => simp [lreplay]
  | cons b K ih =>
    show lreplay (K.map (setTo e2)) ((setTo e2 b).apply m) !! c = _
    rw [ih]
    by_cases hc : c ∈ K
    · simp [hc]
    · simp only [hc, ↓reduceIte, List.mem_cons, _root_.or_false]
      by_cases hbc : b = c
      · subst hbc
        simp only [↓reduceIte]
        unfold setTo
        cases h : e2 !! b with
        | none => show (GMap.delete b m) !! b = none; exact GMap.lookup_delete_eq _ _
        | some n => show (<[b := n]> m) !! b = some n; exact GMap.lookup_insert _ _ _
      · rw [if_neg (Ne.symm hbc)]
        unfold setTo
        cases e2 !! b with
        | none => exact GMap.lookup_delete_ne _ hbc
        | some n => exact GMap.lookup_insert_ne _ _ hbc

theorem lreplay_lopsDiff (e1 e2 : Ents) : lreplay (lopsDiff e1 e2) e1 = e2 := by
  unfold lopsDiff
  split
  · rename_i h; subst h; rfl
  · apply GMap.ext; intro c
    rw [lreplay_setTo]
    split
    · rfl
    · rename_i hc
      have h1 : e1 !! c = none := by
        cases h : e1 !! c with
        | none => rfl
        | some v => exact absurd (List.mem_map.2 ⟨(c, v), List.mem_append_left _ ((GMap.mem_toList _ _ _).2 h), rfl⟩) hc
      have h2 : e2 !! c = none := by
        cases h : e2 !! c with
        | none => rfl
        | some v => exact absurd (List.mem_map.2 ⟨(c, v), List.mem_append_right _ ((GMap.mem_toList _ _ _).2 h), rfl⟩) hc
      rw [h1, h2]

/-! ## The changes of an operation -/

theorem lreplay_single (o : LOp) (e : Ents) : lreplay [o] e = o.apply e := rfl

theorem lopFor_correct (m : NsMap) (d : GoString) (o : NsOp) :
    lreplay (lopFor m d o) (entsOf m d) = entsOf (o.apply m) d := by
  cases o with
  | create p k =>
    simp only [lopFor]
    split
    · rename_i h
      obtain ⟨hp, hb⟩ := h
      rw [lreplay_single]
      show (<[baseOf p := OsNode.file k]> (entsOf m d)) = entsOf (<[p := .file k]> m) d
      conv => rhs; rw [hp]
      rw [entsOf_insert_child _ _ _ _ hb]
    · exact lreplay_lopsDiff _ _
  | mkdir p =>
    simp only [lopFor]
    split
    · rename_i h
      obtain ⟨hp, hb⟩ := h
      rw [lreplay_single]
      show (<[baseOf p := OsNode.dir]> (entsOf m d)) = entsOf (<[p := .dir]> m) d
      conv => rhs; rw [hp]
      rw [entsOf_insert_child _ _ _ _ hb]
    · exact lreplay_lopsDiff _ _
  | remove p =>
    simp only [lopFor]
    split
    · rename_i h
      obtain ⟨hp, -⟩ := h
      rw [lreplay_single]
      show GMap.delete (baseOf p) (entsOf m d) = entsOf (GMap.delete p m) d
      conv => rhs; rw [hp]
      rw [entsOf_delete_child]
    · exact lreplay_lopsDiff _ _
  | rename s t =>
    simp only [lopFor]
    split
    · rename_i h
      obtain ⟨hs, ht, hbs, hbt, hne, hf⟩ := h
      rw [lreplay_single]
      unfold isFileAt at hf
      split at hf
      · rename_i k hk
        have hrhs : NsOp.apply (.rename s t) m = <[t := .file k]> (GMap.delete s m) := by
          simp only [NsOp.apply, hk]
        rw [hrhs]
        have hl : entsOf m d !! baseOf s = some (.file k) := by
          rw [entsOf_child _ _ _ hbs, show child d (baseOf s) = s from hs.symm, hk]
        show (match entsOf m d !! baseOf s with
          | some n => <[baseOf t := n]> (GMap.delete (baseOf s) (entsOf m d))
          | none => entsOf m d) = _
        rw [hl]
        conv => rhs; rw [ht]
        rw [entsOf_insert_child _ _ _ _ hbt]
        conv => rhs; rw [hs]
        rw [entsOf_delete_child]
      · cases hf
    · exact lreplay_lopsDiff _ _

/-! ## A directory's view -/

theorem lreplay_append' (a b : List LOp) (m : Ents) :
    lreplay (a ++ b) m = lreplay b (lreplay a m) := lreplay_append a b m

theorem lreplay_lopsAlong (m : NsMap) (H : List NsOp) (d : GoString) :
    lreplay (lopsAlong m H d) (entsOf m d) = entsOf (nsReplay H m) d := by
  induction H generalizing m with
  | nil => rfl
  | cons o os ih =>
    show lreplay (lopFor m d o ++ lopsAlong (o.apply m) os d) _ = entsOf (nsReplay os (o.apply m)) d
    rw [lreplay_append', lopFor_correct, ih]

theorem dview_now (H0 : NsMap) (H : List NsOp) (d : GoString) :
    (dview H0 H d).now = entsOf (nsReplay H H0) d :=
  lreplay_lopsAlong H0 H d

theorem lopsAlong_take (m : NsMap) (H : List NsOp) (d : GoString) (n : Nat) :
    ∃ i, i ≤ (lopsAlong m H d).length ∧ (lopsAlong m H d).take i = lopsAlong m (H.take n) d := by
  induction H generalizing m n with
  | nil => exact ⟨0, by simp, by simp [lopsAlong]⟩
  | cons o os ih =>
    cases n with
    | zero => exact ⟨0, by simp, by simp [lopsAlong]⟩
    | succ n =>
      obtain ⟨i, hi, he⟩ := ih (o.apply m) n
      refine ⟨(lopFor m d o).length + i, ?_, ?_⟩
      · simp only [lopsAlong, List.length_append]; omega
      · simp only [lopsAlong, List.take_succ_cons]
        rw [List.take_append, List.take_of_length_le (by omega), Nat.add_sub_cancel_left, he]

/-- **Every prefix of the history leaves the directory one of its view's crash outcomes.** -/
theorem dview_crashTo (H0 : NsMap) (H : List NsOp) (d : GoString) (n : Nat) :
    (dview H0 H d).CrashTo (entsOf (nsReplay (H.take n) H0) d) := by
  obtain ⟨i, hi, he⟩ := lopsAlong_take H0 H d n
  refine ⟨i, hi, ?_⟩
  show _ = lreplay ((lopsAlong H0 H d).take i) (entsOf H0 d)
  rw [he, lreplay_lopsAlong]

theorem lopsAlong_snoc (m : NsMap) (H : List NsOp) (o : NsOp) (d : GoString) :
    lopsAlong m (H ++ [o]) d = lopsAlong m H d ++ lopFor (nsReplay H m) d o := by
  induction H generalizing m with
  | nil => simp [lopsAlong, nsReplay]
  | cons o' os ih =>
    show lopFor m d o' ++ lopsAlong (o'.apply m) (os ++ [o]) d = _
    rw [ih]; simp [lopsAlong, nsReplay, List.foldl]

theorem dview_snoc (H0 : NsMap) (H : List NsOp) (o : NsOp) (d : GoString) :
    dview H0 (H ++ [o]) d =
      ⟨(dview H0 H d).dur, (dview H0 H d).pend ++ lopFor (nsReplay H H0) d o⟩ := by
  unfold dview; rw [lopsAlong_snoc]

/-- A file created, removed or renamed in `d`, or a directory made in `d`: the view pushes its one
change. -/
theorem dview_create (H0 : NsMap) (H : List NsOp) (d b k : GoString) (hb : NameOk b) :
    dview H0 (H ++ [.create (child d b) k]) d = (dview H0 H d).push (.put b (.file k)) := by
  rw [dview_snoc]
  simp only [lopFor, baseOf_child' d b hb, hb, _root_.and_self, ↓reduceIte]
  rfl

theorem dview_mkdir (H0 : NsMap) (H : List NsOp) (d b : GoString) (hb : NameOk b) :
    dview H0 (H ++ [.mkdir (child d b)]) d = (dview H0 H d).push (.put b .dir) := by
  rw [dview_snoc]
  simp only [lopFor, baseOf_child' d b hb, hb, _root_.and_self, ↓reduceIte]
  rfl

theorem dview_remove (H0 : NsMap) (H : List NsOp) (d b : GoString) (hb : NameOk b) :
    dview H0 (H ++ [.remove (child d b)]) d = (dview H0 H d).push (.del b) := by
  rw [dview_snoc]
  simp only [lopFor, baseOf_child' d b hb, hb, _root_.and_self, ↓reduceIte]
  rfl

theorem dview_rename (H0 : NsMap) (H : List NsOp) (d bs bt k : GoString) (hbs : NameOk bs)
    (hbt : NameOk bt) (hne : bs ≠ bt) (hf : nsReplay H H0 !! child d bs = some (.file k)) :
    dview H0 (H ++ [.rename (child d bs) (child d bt)]) d = (dview H0 H d).push (.mv bs bt) := by
  rw [dview_snoc]
  have hfa : isFileAt (nsReplay H H0) (child d bs) = true := by simp [isFileAt, hf]
  simp only [lopFor, baseOf_child' d bs hbs, baseOf_child' d bt hbt, hbs, hbt, hne, hfa,
    _root_.and_self, ↓reduceIte, ne_eq, not_false_eq_true, _root_.true_and]
  rfl

/-- No operation: the view of the empty history. -/
theorem dview_nil (H0 : NsMap) (d : GoString) : dview H0 [] d = ⟨entsOf H0 d, []⟩ := rfl

end Perennial

end
