/-
The read path's (U6, `notes/bbolt-proof-plan.md`) cursor positions: what a move does to
`stackPos` (`Model/Cursor.lean`), over the bounds of a path. `Model/Cursor.lean`'s own lemmas
use private copies of the first half (it cannot import this module); the moves `next` makes
(`stackPos_succ_up`, `stackPos_succ_leaf`) are here, since `rStackAt_next`/`wStackAt_next`
are not provable as stated (`notes/bbolt-proof-plan.md`, "U6: deviations and findings").
-/
module

public import Proof.go_etcd_io.bbolt.Model.Cursor

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Read

section cursor
variable [GooseExts]

/-- Entries strictly increasing by key. -/
def esSorted (es : List BoltEnt) : Prop := es.Pairwise (fun a b => go.GoStringLt a.1 b.1)

theorem bktEnts_sorted (m : BktData) : esSorted (bktEnts m) := by
  unfold bktEnts esSorted
  have hn : ((m.toList.mergeSort (fun a b => !decide (go.GoStringLt b.1 a.1))).map
      Prod.fst).Nodup :=
    (((List.mergeSort_perm m.toList _).map Prod.fst).nodup_iff).2 (GMap.toList_keys_nodup m)
  have hle : (m.toList.mergeSort (fun a b => !decide (go.GoStringLt b.1 a.1))).Pairwise
      (fun a b => (!decide (go.GoStringLt b.1 a.1)) = true) := by
    apply List.pairwise_mergeSort
    · intro a b c h1 h2
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at *
      intro h3
      rcases Classical.em (go.GoStringLt b.1 a.1) with h | h
      · exact h1 h
      · rcases Classical.em (go.GoStringLt c.1 b.1) with h' | h'
        · exact h2 h'
        · have e1 := Classical.byContradiction fun hne : ¬ (a.1 = b.1 ∨ go.GoStringLt a.1 b.1) => by
            exact hne (by
              rcases Classical.em (go.GoStringLt a.1 b.1) with h4 | h4
              · exact Or.inr h4
              · exact Or.inl (go.goStringLt_eq_of_not_lt h4 h))
          rcases e1 with e1 | e1
          · rw [e1] at h3; exact h2 h3
          · exact h2 (go.goStringLt_trans h3 e1)
    · intro a b
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, Bool.or_eq_true]
      rcases Classical.em (go.GoStringLt b.1 a.1) with h | h
      · right; exact go.goStringLt_asymm h
      · left; exact h
  rw [List.Nodup, List.pairwise_map] at hn
  refine (hle.and hn).imp (fun ⟨h1, h2⟩ => ?_)
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h1
  rcases Classical.em (go.GoStringLt _ _) with h | h
  · exact h
  · exact absurd (go.goStringLt_eq_of_not_lt h h1) h2


theorem len_filter_sum (es : List BoltEnt) (f g h : BoltEnt → Bool)
    (hpt : ∀ e ∈ es, (if f e then 1 else 0) + (if g e then 1 else 0) = (if h e then 1 else 0)) :
    (es.filter f).length + (es.filter g).length = (es.filter h).length := by
  induction es with
  | nil => rfl
  | cons a t ih =>
    have ha := hpt a (List.mem_cons_self ..)
    have ht := ih (fun e he => hpt e (List.mem_cons_of_mem _ he))
    simp only [List.filter_cons]
    split <;> split <;> split <;> simp_all <;> omega

theorem takeWhile_lt_sorted (es : List BoltEnt) (k : List w8) (hs : esSorted es) :
    es.takeWhile (fun e => decide (go.GoStringLt e.1 k)) =
      es.filter (fun e => decide (go.GoStringLt e.1 k)) := by
  induction es with
  | nil => rfl
  | cons a t ih =>
    unfold esSorted at hs
    rw [List.pairwise_cons] at hs
    simp only [List.takeWhile_cons, List.filter_cons]
    by_cases ha : go.GoStringLt a.1 k
    · simp only [ha, decide_true, ↓reduceIte, ih hs.2]
    · simp only [ha, decide_false, Bool.false_eq_true, ↓reduceIte]
      symm
      rw [List.filter_eq_nil_iff]
      intro x hx hxk
      simp only [decide_eq_true_eq] at hxk
      exact ha (go.goStringLt_trans (hs.1 x hx) hxk)

theorem keyGe_lt {lo : Option (List w8)} {e k : List w8} (hk : keyGe lo k)
    (he : ¬ keyGe lo e) : go.GoStringLt e k := by
  cases lo with
  | none => exact absurd (fun _ h => nomatch h) he
  | some l =>
  have hel : go.GoStringLt e l := Classical.byContradiction fun h => he (fun l' hl => by
    cases hl; exact h)
  have := hk l rfl
  rcases Classical.em (go.GoStringLt l k) with h | h
  · exact go.goStringLt_trans hel h
  · rw [go.goStringLt_eq_of_not_lt this h]; exact hel

theorem keyLt_lt {hi : Option (List w8)} {e k : List w8} (hk : keyLt k hi)
    (he : go.GoStringLt e k) : keyLt e hi :=
  fun h hh => go.goStringLt_trans he (hk h hh)

open Classical in
/-- The position of a search's leaf index under the bounds `bnd` routing `k`. -/
theorem seek_count (es : List BoltEnt) (k : List w8) (bnd : Option (List w8) × Option (List w8))
    (hs : esSorted es) (hk : keyIn bnd.1 bnd.2 k) :
    (es.filter fun e => decide (¬ keyGe bnd.1 e.1)).length +
      ((entsIn es bnd).takeWhile fun e => decide (go.GoStringLt e.1 k)).length =
      seekIdx es k := by
  unfold seekIdx entsIn
  rw [takeWhile_lt_sorted es k hs, takeWhile_lt_sorted _ k (List.Pairwise.filter _ hs)]
  rw [List.filter_filter]
  apply len_filter_sum
  intro e _
  by_cases hg : keyGe bnd.1 e.1
  · by_cases hl : go.GoStringLt e.1 k
    · have := keyLt_lt hk.2 hl
      simp [hg, hl, keyIn, this]
    · simp [hg, hl]
  · have hl := keyGe_lt hk.1 hg
    simp [hg, hl, keyIn]

/-- A routed path's leaf bounds contain `k`. -/
theorem pathBndFrom_route (v : View) (k : List w8) :
    ∀ (els : List elemRef) (pids : List Nat) (b : Option (List w8) × Option (List w8)),
    pids.length = els.length → keyIn b.1 b.2 k →
    (∀ j pid e, pids[j]? = some pid → els[j]? = some e → j + 1 < els.length →
      let ks := pidKeys v pid
      e.index'.toNat < ks.length ∧
      (e.index'.toNat = 0 ∨ ∃ ki, ks[e.index'.toNat]? = some ki ∧ ¬ go.GoStringLt k ki) ∧
      ∀ kn, ks[e.index'.toNat + 1]? = some kn → go.GoStringLt k kn) →
    keyIn (pathBndFrom v b pids els).1 (pathBndFrom v b pids els).2 k
  | [], _, b, _, hb, _ => by cases ‹List Nat› <;> simpa [pathBndFrom] using hb
  | [_], pids, b, hl, hb, _ => by
    match pids, hl with
    | [_], _ => simpa [pathBndFrom] using hb
  | e :: e' :: es, pids, b, hl, hb, hr => by
    match pids, hl with
    | pid :: pid' :: ps, hl =>
      simp only [pathBndFrom]
      apply pathBndFrom_route v k (e' :: es) (pid' :: ps)
      · simpa using hl
      · obtain ⟨_, h0, h1⟩ := hr 0 pid e rfl rfl (by simp)
        refine ⟨?_, ?_⟩
        · simp only [entryBnd, childLo]
          split
          · exact hb.1
          · rcases h0 with h0 | ⟨ki, hki, hnk⟩
            · contradiction
            · intro l hlk
              simp only [Option.some.injEq] at hlk
              subst hlk
              rw [List.getD_eq_getElem?_getD, hki]; exact hnk
        · simp only [entryBnd, childHi]
          split
          · intro h hh
            simp only [Option.some.injEq] at hh
            subst hh
            rw [List.getD_eq_getElem?_getD]
            obtain ⟨kn, hkn⟩ : ∃ kn, (pidKeys v pid)[e.index'.toNat + 1]? = some kn :=
              Option.isSome_iff_exists.mp (by simp [*])
            rw [hkn]; exact h1 kn hkn
          · exact hb.2
      · intro j p x hp hx hj
        exact hr (j + 1) p x (by simpa using hp) (by simpa using hx) (by simp at hj ⊢; omega)

theorem pathBndFrom_first (v : View) :
    ∀ (els : List elemRef) (pids : List Nat) (b : Option (List w8) × Option (List w8)),
    (∀ e ∈ els, e.index'.toNat = 0) → (pathBndFrom v b pids els).1 = b.1
  | e :: e' :: es, pid :: pid' :: ps, b, hf => by
    simp only [pathBndFrom]
    rw [pathBndFrom_first v (e' :: es) (pid' :: ps) _ (fun x hx => hf x (List.mem_cons_of_mem _ hx))]
    simp [entryBnd, childLo, hf e (List.mem_cons_self ..)]
  | [], _, _, _ => by cases ‹List Nat› <;> simp [pathBndFrom]
  | [_], [], _, _ => by simp [pathBndFrom]
  | [_], [_], _, _ => by simp [pathBndFrom]
  | [e], _ :: _ :: _, _, hf => by simp [pathBndFrom, entryBnd, childLo, hf e (by simp)]
  | _ :: _ :: _, [], _, _ => by simp [pathBndFrom]
  | _ :: _ :: _, [_], _, _ => by simp [pathBndFrom]

theorem pathBndFrom_last (v : View) :
    ∀ (els : List elemRef) (pids : List Nat) (b : Option (List w8) × Option (List w8)),
    pids.length = els.length →
    (∀ j pid e, pids[j]? = some pid → els[j]? = some e → j + 1 < els.length →
      e.index'.toNat + 1 = (pidKeys v pid).length) → (pathBndFrom v b pids els).2 = b.2
  | e :: e' :: es, pid :: pid' :: ps, b, hl, hr => by
    simp only [pathBndFrom]
    rw [pathBndFrom_last v (e' :: es) (pid' :: ps) _ (by simpa using hl)
      (fun j p x hp hx hj => hr (j + 1) p x (by simpa using hp) (by simpa using hx)
        (by simp at hj ⊢; omega))]
    have := hr 0 pid e rfl rfl (by simp)
    simp [entryBnd, childHi, this]
  | [], _, _, _, _ => by cases ‹List Nat› <;> simp [pathBndFrom]
  | [_], [], _, _, _ => by simp [pathBndFrom]
  | [_], [_], _, _, _ => by simp [pathBndFrom]
  | [_], _ :: _ :: _, _, hl, _ => by simp at hl
  | _ :: _ :: _, [], _, _, _ => by simp [pathBndFrom]
  | _ :: _ :: _, [_], _, _, _ => by simp [pathBndFrom]

theorem stackPos_seek (v : View) (es : List BoltEnt) (pids : List Nat)
    (els : List elemRef) (k : List w8) (hs : esSorted es) (hl : pids.length = els.length)
    (hr : sRoutes v es pids els k) : stackPos v es pids els = seekIdx es k := by
  unfold stackPos
  rw [hr.2]
  exact seek_count es k _ hs (pathBndFrom_route v k els pids (none, none) hl
    (show keyIn (none : Option (List w8)) none k by
      unfold keyIn keyGe keyLt; simp)
    hr.1)

theorem seekIdx_le (es : List BoltEnt) (k : List w8) : seekIdx es k ≤ es.length :=
  List.IsPrefix.length_le (List.takeWhile_prefix _)

theorem stackPos_first (v : View) (es : List BoltEnt) (pids : List Nat)
    (els : List elemRef) (hf : sFirst els) : stackPos v es pids els = 0 := by
  unfold stackPos pathBnd
  rw [pathBndFrom_first v els pids _ hf]
  have : leafIdx els = 0 := by
    unfold leafIdx
    cases h : els.getLast? with
    | none => rfl
    | some e => simp [hf e (List.mem_of_getLast? h)]
  rw [this]
  simp [keyGe]

open Classical in
theorem stackPos_last (v : View) (es : List BoltEnt) (pids : List Nat)
    (els : List elemRef) (hl : pids.length = els.length) (hla : sLast v es pids els) :
    stackPos v es pids els = es.length - 1 := by
  unfold stackPos
  have h2 : (pathBnd v pids els).2 = none := pathBndFrom_last v els pids _ hl hla.1
  have hsum := len_filter_sum es (fun e => decide (¬ keyGe (pathBnd v pids els).1 e.1))
    (fun e => decide (keyIn (pathBnd v pids els).1 (pathBnd v pids els).2 e.1)) (fun _ => true)
    (by intro e _; by_cases h : keyGe (pathBnd v pids els).1 e.1 <;> simp [h, keyIn, keyLt, h2])
  have htrue : (es.filter fun _ => true) = es := List.filter_eq_self.2 (fun _ _ => rfl)
  rw [htrue] at hsum
  have hb := hla.2
  unfold entsIn at hb
  omega


theorem pathBndFrom_cons (v : View) (b : Option (List w8) × Option (List w8)) (p : Nat)
    (xs : List Nat) (e : elemRef) (es : List elemRef) (hx : xs ≠ []) :
    pathBndFrom v b (p :: xs) (e :: es) =
      pathBndFrom v (entryBnd b (pidKeys v p) e.index'.toNat) xs es := by
  cases xs with
  | nil => exact absurd rfl hx
  | cons x xs => simp [pathBndFrom]

/-- The bounds of a path, split after a prefix: the prefix's bounds, then the rest's. -/
theorem pathBndFrom_append (v : View) :
    ∀ (E : List elemRef) (P : List Nat) (b : Option (List w8) × Option (List w8))
      (x0 : Nat) (X : List Nat) (Y : List elemRef), P.length = E.length →
    pathBndFrom v b (P ++ x0 :: X) (E ++ Y) =
      pathBndFrom v (pathBndFrom v b (P ++ [x0]) E) (x0 :: X) Y
  | [], [], b, x0, X, Y, _ => by simp [pathBndFrom]
  | e :: E, p :: P, b, x0, X, Y, hl => by
    simp only [List.cons_append]
    rw [pathBndFrom_cons v b p _ e _ (by simp), pathBndFrom_cons v b p _ e _ (by simp)]
    exact pathBndFrom_append v E P _ x0 X Y (by simpa using hl)
  | [], _ :: _, _, _, _, _, hl => by simp at hl
  | _ :: _, [], _, _, _, _, hl => by simp at hl

theorem leafIdx_append (E R : List elemRef) (hR : R ≠ []) : leafIdx (E ++ R) = leafIdx R := by
  unfold leafIdx; rw [List.getLast?_append]
  cases h : R.getLast? with
  | none => simp at h; exact absurd h hR
  | some x => simp

open Classical in
/-- **`next`'s position, one level up** (`d` above the leaf): the old stack is at the end of
every level below `d` (branch indices the last, its leaf index at or past the leaf's last
entry), the new one one further at `d` and first below. The new position is the old one plus
what was left of the old leaf (one, or none past its end). -/
theorem stackPos_succ_up (v : View) (es : List BoltEnt) (P : List Nat) (E : List elemRef)
    (p : Nat) (Q Q' : List Nat) (e e' : elemRef) (R R' : List elemRef)
    (hPE : P.length = E.length) (hQR : Q.length = R.length) (hQR' : Q'.length = R'.length)
    (hR : R ≠ []) (hR' : R' ≠ [])
    (hidx : e'.index'.toNat = e.index'.toNat + 1)
    (hlt : e'.index'.toNat < (pidKeys v p).length)
    (hlast : ∀ j pid x, Q[j]? = some pid → R[j]? = some x → j + 1 < R.length →
      x.index'.toNat + 1 = (pidKeys v pid).length)
    (hfirst : ∀ x ∈ R', x.index'.toNat = 0)
    (hbnd : ∀ L H, pathBnd v (P ++ p :: Q) (E ++ e :: R) = (some L, some H) →
      ¬ go.GoStringLt H L)
    (hle : leafIdx R ≤ (entsIn es (pathBnd v (P ++ p :: Q) (E ++ e :: R))).length) :
    stackPos v es (P ++ p :: Q') (E ++ e' :: R') + leafIdx R =
      stackPos v es (P ++ p :: Q) (E ++ e :: R) +
        (entsIn es (pathBnd v (P ++ p :: Q) (E ++ e :: R))).length := by
  obtain ⟨q0, Q0, rfl⟩ : ∃ q0 Q0, Q = q0 :: Q0 := by
    cases Q with
    | nil => cases R with | nil => exact absurd rfl hR | cons _ _ => simp at hQR
    | cons q0 Q0 => exact ⟨q0, Q0, rfl⟩
  obtain ⟨q0', Q0', rfl⟩ : ∃ q0 Q0, Q' = q0 :: Q0 := by
    cases Q' with
    | nil => cases R' with | nil => exact absurd rfl hR' | cons _ _ => simp at hQR'
    | cons q0 Q0 => exact ⟨q0, Q0, rfl⟩
  have hold : pathBnd v (P ++ p :: q0 :: Q0) (E ++ e :: R) =
      pathBndFrom v (entryBnd (pathBndFrom v (none, none) (P ++ [p]) E) (pidKeys v p) e.index'.toNat) (q0 :: Q0) R := by
    unfold pathBnd
    rw [pathBndFrom_append v E P _ p _ _ hPE, pathBndFrom_cons v _ p _ e _ (by simp)]
  have hnew : pathBnd v (P ++ p :: q0' :: Q0') (E ++ e' :: R') =
      pathBndFrom v (entryBnd (pathBndFrom v (none, none) (P ++ [p]) E) (pidKeys v p) e'.index'.toNat) (q0' :: Q0') R' := by
    unfold pathBnd
    rw [pathBndFrom_append v E P _ p _ _ hPE, pathBndFrom_cons v _ p _ e' _ (by simp)]
  have hhi : (pathBnd v (P ++ p :: q0 :: Q0) (E ++ e :: R)).2 = some ((pidKeys v p).getD (e.index'.toNat + 1) []) := by
    rw [hold, pathBndFrom_last v R (q0 :: Q0) _ hQR hlast]
    simp only [entryBnd, childHi]
    rw [if_pos (show _ by omega)]
  have hlo : (pathBnd v (P ++ p :: q0' :: Q0') (E ++ e' :: R')).1 = some ((pidKeys v p).getD (e.index'.toNat + 1) []) := by
    rw [hnew, pathBndFrom_first v R' (q0' :: Q0') _ hfirst]
    simp only [entryBnd, childLo, hidx]
    simp
  have hli' : leafIdx (E ++ e' :: R') = 0 := by
    rw [show E ++ e' :: R' = (E ++ [e']) ++ R' by simp, leafIdx_append _ _ hR']
    unfold leafIdx
    cases h : R'.getLast? with
    | none => rfl
    | some x => simp [hfirst x (List.mem_of_getLast? h)]
  have hli : leafIdx (E ++ e :: R) = leafIdx R := by
    rw [show E ++ e :: R = (E ++ [e]) ++ R by simp, leafIdx_append _ _ hR]
  unfold stackPos
  rw [hli', hli, hlo]
  generalize hK : ((pidKeys v p).getD (e.index'.toNat + 1) []) = K at hhi hlo
  generalize hlo' : (pathBnd v (P ++ p :: q0 :: Q0) (E ++ e :: R)).1 = lo
  have hb : pathBnd v (P ++ p :: q0 :: Q0) (E ++ e :: R) = (lo, some K) := by
    rw [← hhi, ← hlo']
  have hlK : keyGe lo K := by
    intro L hL; exact hbnd L K (by rw [hb, hL])
  have hcount := len_filter_sum es (fun x => decide (¬ keyGe lo x.1))
    (fun x => decide (keyIn lo (some K) x.1)) (fun x => decide (¬ keyGe (some K) x.1))
    (by
      intro x _
      by_cases hg : keyGe lo x.1
      · by_cases hk : go.GoStringLt x.1 K
        · have : ¬ keyGe (some K) x.1 := fun h => h K rfl hk
          simp [hg, keyIn, keyLt, hk, this]
        · have : keyGe (some K) x.1 := by intro l hl; cases hl; exact hk
          simp [hg, keyIn, keyLt, hk, this]
      · have hk := keyGe_lt hlK hg
        have : ¬ keyGe (some K) x.1 := fun h => h K rfl hk
        simp [hg, keyIn, this])
  unfold entsIn at hle ⊢
  rw [hb] at hle ⊢
  simp only at hle ⊢
  omega

/-- **`next`'s position at the leaf**: the leaf index one further. -/
theorem stackPos_succ_leaf (v : View) (es : List BoltEnt) (P : List Nat) (E : List elemRef)
    (p : Nat) (e e' : elemRef) (hPE : P.length = E.length)
    (hidx : e'.index'.toNat = e.index'.toNat + 1) :
    stackPos v es (P ++ [p]) (E ++ [e']) = stackPos v es (P ++ [p]) (E ++ [e]) + 1 := by
  have h : ∀ x, pathBnd v (P ++ [p]) (E ++ [x]) = pathBndFrom v (none, none) (P ++ [p]) E := by
    intro x; unfold pathBnd
    rw [pathBndFrom_append v E P _ p [] [x] hPE]; simp [pathBndFrom]
  unfold stackPos
  rw [h, h, leafIdx_append _ _ (by simp), leafIdx_append _ _ (by simp)]
  simp [leafIdx, hidx]; omega

end cursor

end Read

end bbolt
end EtcdGrove
end Perennial
