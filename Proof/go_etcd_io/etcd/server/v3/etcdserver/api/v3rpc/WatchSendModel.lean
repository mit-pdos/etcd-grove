/-
**The send loop's ordering model** (the watch slice's unit W-S, pure): `watch.go`'s `sendLoop`
receives the mvcc watch stream's responses `rcv` (in order) and sends each at once (its watch id
announced in `ids`, or `-1`) or buffers it in `pending[id]`, flushed in order when the id's
created response is sent. Ghost model: the indices `S` of the responses sent (in send order),
the pending indices per id `pend`, the announced ids `ids`, and the id being flushed `ex`
(`SendInv`). `send_claim`: when the response `n` is sent, its watcher's responses with events
sent before, then it, are exactly its responses with events received up to `n`.
Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchStore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace v3rpc

/-- The response at index `m` of `rcv` has the watch id `X`. -/
def idOf (rcv : List mvcc.RespM) (X : w64) (m : Nat) : Bool :=
  decide ((rcv[m]?.map (·.id)) = some X)

/-- The indices of the responses of `rcv` with the watch id `X`, in order. -/
def idxOf (rcv : List mvcc.RespM) (X : w64) : List Nat :=
  (List.range rcv.length).filter (idOf rcv X)

/-- An update of a function at one point. -/
def upd {α : Type} (g : w64 → α) (X : w64) (a : α) : w64 → α :=
  fun Y => if Y = X then a else g Y

/-- **The send loop's invariant** (see the file header): per id, the received indices are the
sent ones, then the pending ones; an announced id (or `-1`) has nothing pending unless it is
being flushed; every sent index is a received one. -/
structure SendInv (rcv : List mvcc.RespM) (S : List Nat) (pend : w64 → List Nat)
    (ids : w64 → Bool) (ex : Option w64) : Prop where
  split : ∀ X, idxOf rcv X = S.filter (idOf rcv X) ++ pend X
  noPend : ∀ X, (ids X = true ∨ X = W64 (-1)) → ex ≠ some X → pend X = []
  bound : ∀ m ∈ S, m < rcv.length

/-! ## Lemmas on indices -/

theorem idOf_snoc_lt (rcv : List mvcc.RespM) (r : mvcc.RespM) (X : w64) {m : Nat}
    (h : m < rcv.length) : idOf (rcv ++ [r]) X m = idOf rcv X m := by
  unfold idOf; rw [List.getElem?_append_left h]

theorem idOf_snoc_len (rcv : List mvcc.RespM) (r : mvcc.RespM) (X : w64) :
    idOf (rcv ++ [r]) X rcv.length = decide (r.id = X) := by
  unfold idOf
  rw [List.getElem?_append_right (Nat.le_refl _)]
  simp

theorem idxOf_snoc (rcv : List mvcc.RespM) (r : mvcc.RespM) (X : w64) :
    idxOf (rcv ++ [r]) X = idxOf rcv X ++ (if r.id = X then [rcv.length] else []) := by
  unfold idxOf
  rw [List.length_append, List.length_singleton, List.range_succ, List.filter_append]
  congr 1
  · apply List.filter_congr
    intro m hm
    exact idOf_snoc_lt rcv r X (List.mem_range.1 hm)
  · rw [List.filter_cons, idOf_snoc_len]
    by_cases h : r.id = X <;> simp [h]

theorem filter_snoc_bound (rcv : List mvcc.RespM) (r : mvcc.RespM) (X : w64) (S : List Nat)
    (hb : ∀ m ∈ S, m < rcv.length) : S.filter (idOf (rcv ++ [r]) X) = S.filter (idOf rcv X) := by
  apply List.filter_congr
  intro m hm
  exact idOf_snoc_lt rcv r X (hb m hm)

theorem mem_idxOf {rcv : List mvcc.RespM} {X : w64} {m : Nat} (h : m ∈ idxOf rcv X) :
    m < rcv.length ∧ idOf rcv X m = true := by
  unfold idxOf at h
  rw [List.mem_filter, List.mem_range] at h
  exact h

theorem idOf_eq_id {rcv : List mvcc.RespM} {X : w64} {m : Nat} (h : idOf rcv X m = true) :
    ∃ x, rcv[m]? = some x ∧ x.id = X := by
  unfold idOf at h
  have h := of_decide_eq_true h
  cases hm : rcv[m]? with
  | none => rw [hm] at h; cases h
  | some x => rw [hm] at h; exact ⟨x, rfl, by simpa using h⟩

theorem idOf_unique {rcv : List mvcc.RespM} {X Y : w64} {m : Nat} (h1 : idOf rcv X m = true)
    (h2 : idOf rcv Y m = true) : X = Y := by
  obtain ⟨x, hx, rfl⟩ := idOf_eq_id h1
  obtain ⟨y, hy, rfl⟩ := idOf_eq_id h2
  rw [hx] at hy; cases hy; rfl

theorem idxOf_nodup (rcv : List mvcc.RespM) (X : w64) : (idxOf rcv X).Nodup :=
  (List.nodup_range).filter _

theorem range_filter_prefix (p : Nat → Bool) {k k' : Nat} (h : k ≤ k') :
    (List.range k).filter p <+: (List.range k').filter p := by
  induction k' with
  | zero => rw [Nat.le_zero.1 h]; exact List.prefix_refl _
  | succ k' ih =>
    by_cases hk : k = k' + 1
    · rw [hk]; exact List.prefix_refl _
    · have := ih (by omega)
      rw [List.range_succ, List.filter_append]
      exact this.trans (List.prefix_append _ _)

/-- Two prefixes of a list without duplicates ending at the same element are equal. -/
theorem cons_mid_eq {a b t u : List Nat} {x : Nat} (h : a ++ x :: t = b ++ x :: u)
    (ha : x ∉ a) (hb : x ∉ b) : a = b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons y b' =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.1 ▸ List.mem_cons_self) hb
  | cons c a' ih =>
    cases b with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.1 ▸ List.mem_cons_self) ha
    | cons d b' =>
      simp only [List.cons_append, List.cons.injEq] at h
      rw [h.1, ih h.2 (fun hm => ha (List.mem_cons_of_mem _ hm))
        (fun hm => hb (List.mem_cons_of_mem _ hm))]

theorem not_mem_of_nodup {a t : List Nat} {x : Nat} (h : (a ++ x :: t).Nodup) : x ∉ a := by
  intro hx
  rw [List.nodup_append] at h
  exact h.2.2 x hx x List.mem_cons_self rfl

theorem prefix_last_eq {l a b : List Nat} {x : Nat} (hl : l.Nodup) (ha : a ++ [x] <+: l)
    (hb : b ++ [x] <+: l) : a = b := by
  obtain ⟨t, ht⟩ := ha
  obtain ⟨u, hu⟩ := hb
  rw [List.append_assoc, List.singleton_append] at ht hu
  have hna := not_mem_of_nodup (ht ▸ hl)
  have hnb := not_mem_of_nodup (hu ▸ hl)
  exact cons_mid_eq (ht.trans hu.symm) hna hnb

theorem take_eq_filterMap (rcv : List mvcc.RespM) :
    ∀ k, k ≤ rcv.length → rcv.take k = (List.range k).filterMap (fun m => rcv[m]?)
  | 0, _ => by simp
  | k + 1, h => by
    rw [List.take_add_one, List.range_succ, List.filterMap_append,
      take_eq_filterMap rcv k (by omega)]
    congr 1

theorem filter_filterMap {α : Type} (L : List Nat) (f : Nat → Option α) (p : α → Bool) :
    (L.filterMap f).filter p =
      (L.filter (fun m => (f m).any p)).filterMap f := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    cases hf : f a with
    | none => simp [hf, ih]
    | some x =>
      by_cases hp : p x = true
      · simp [hf, ih, hp]
      · simp [hf, ih, hp]

/-! ## The invariant's steps -/

theorem sendInv_nil (ids : w64 → Bool) : SendInv [] [] (fun _ => []) ids none where
  split X := by simp [idxOf]
  noPend _ _ _ := rfl
  bound _ h := by cases h

/-- A response received and sent at once (its id announced, or `-1`). -/
theorem sendInv_recv_direct {rcv : List mvcc.RespM} {S : List Nat} {pend : w64 → List Nat}
    {ids : w64 → Bool} {r : mvcc.RespM} (hI : SendInv rcv S pend ids none)
    (hd : ids r.id = true ∨ r.id = W64 (-1)) :
    SendInv (rcv ++ [r]) (S ++ [rcv.length]) pend ids none where
  split X := by
    rw [idxOf_snoc, List.filter_append, filter_snoc_bound rcv r X S hI.bound]
    simp only [List.filter_cons, List.filter_nil, idOf_snoc_len]
    rw [hI.split X]
    by_cases h : r.id = X
    · subst h
      rw [hI.noPend r.id hd (by simp)]
      simp
    · simp [h]
  noPend := hI.noPend
  bound m hm := by
    rw [List.mem_append, List.mem_singleton] at hm
    rcases hm with hm | rfl
    · have := hI.bound m hm; simp; omega
    · simp

/-- A response received and buffered (its id not announced). -/
theorem sendInv_recv_pend {rcv : List mvcc.RespM} {S : List Nat} {pend : w64 → List Nat}
    {ids : w64 → Bool} {r : mvcc.RespM} (hI : SendInv rcv S pend ids none)
    (hd : ¬(ids r.id = true ∨ r.id = W64 (-1))) :
    SendInv (rcv ++ [r]) S (upd pend r.id (pend r.id ++ [rcv.length])) ids none where
  split X := by
    rw [idxOf_snoc, filter_snoc_bound rcv r X S hI.bound, hI.split X]
    unfold upd
    by_cases h : r.id = X
    · subst h; simp
    · simp [h, Ne.symm h]
  noPend X hX hne := by
    unfold upd
    by_cases h : X = r.id
    · subst h; exact absurd hX hd
    · simp only [h, ↓reduceIte]; exact hI.noPend X hX hne
  bound m hm := by have := hI.bound m hm; simp; omega

/-- A created response for `X` sent: `X` announced, its pending responses to flush. -/
theorem sendInv_created {rcv : List mvcc.RespM} {S : List Nat} {pend : w64 → List Nat}
    {ids : w64 → Bool} (X : w64) (hI : SendInv rcv S pend ids none) :
    SendInv rcv S pend (upd ids X true) (some X) where
  split := hI.split
  noPend Y hY hne := by
    unfold upd at hY
    by_cases h : Y = X
    · subst h; exact absurd rfl hne
    · simp only [h, ↓reduceIte] at hY; exact hI.noPend Y hY (by simp)
  bound := hI.bound

/-- One pending response of the flushed id sent. -/
theorem sendInv_flush {rcv : List mvcc.RespM} {S : List Nat} {pend : w64 → List Nat}
    {ids : w64 → Bool} {X : w64} {n : Nat} {P : List Nat} (hI : SendInv rcv S pend ids (some X))
    (hp : pend X = n :: P) : SendInv rcv (S ++ [n]) (upd pend X P) ids (some X) where
  split Y := by
    have hn : n ∈ idxOf rcv X := by rw [hI.split X, hp]; simp
    have hnX := (mem_idxOf hn).2
    rw [List.filter_append, hI.split Y]
    unfold upd
    by_cases h : Y = X
    · subst h; rw [hp]; simp [hnX]
    · have hnY : idOf rcv Y n = false := by
        cases hy : idOf rcv Y n
        · rfl
        · exact absurd (idOf_unique hy hnX) h
      simp [h, hnY]
  noPend Y hY hne := by
    unfold upd
    by_cases h : Y = X
    · subst h; exact absurd rfl hne
    · simp only [h, ↓reduceIte]; exact hI.noPend Y hY hne
  bound m hm := by
    rw [List.mem_append, List.mem_singleton] at hm
    rcases hm with hm | rfl
    · exact hI.bound m hm
    · have hn : m ∈ idxOf rcv X := by rw [hI.split X, hp]; simp
      exact (mem_idxOf hn).1

/-- The flush of `X` done (nothing pending for it). -/
theorem sendInv_flush_done {rcv : List mvcc.RespM} {S : List Nat} {pend : w64 → List Nat}
    {ids : w64 → Bool} {X : w64} (hI : SendInv rcv S pend ids (some X)) (hp : pend X = []) :
    SendInv rcv S pend ids none where
  split := hI.split
  noPend Y hY _ := by
    by_cases h : Y = X
    · subst h; exact hp
    · exact hI.noPend Y hY (by simp [Ne.symm h])
  bound := hI.bound

/-- The flush of `X` done, after the Go code's `delete(pending, X)`. -/
theorem sendInv_flush_done' {rcv : List mvcc.RespM} {S : List Nat} {pend : w64 → List Nat}
    {ids : w64 → Bool} {X : w64} (hI : SendInv rcv S pend ids (some X)) (hp : pend X = []) :
    SendInv rcv S (upd pend X []) ids none := by
  have heq : upd pend X [] = pend := by
    funext Y; unfold upd; by_cases h : Y = X
    · subst h; simp [hp]
    · simp [h]
  rw [heq]; exact sendInv_flush_done hI hp

/-- A canceled response for `X` sent: `X` no longer announced. -/
theorem sendInv_cancel {rcv : List mvcc.RespM} {S : List Nat} {pend : w64 → List Nat}
    {ids : w64 → Bool} (X : w64) (hI : SendInv rcv S pend ids none) :
    SendInv rcv S pend (upd ids X false) none where
  split := hI.split
  noPend Y hY hne := by
    unfold upd at hY
    by_cases h : Y = X
    · simp only [h, ↓reduceIte, Bool.false_eq_true, false_or] at hY
      exact hI.noPend Y (Or.inr (h ▸ hY)) hne
    · simp only [h, ↓reduceIte] at hY; exact hI.noPend Y hY hne
  bound := hI.bound

/-! ## The claim -/

/-- **What a send says of its watcher**: when the response `n` (`r`, with events) is sent after
the responses `S`, provided the responses of `S` with `r`'s id, then `n`, are a prefix of all
received with `r`'s id, and a watcher's responses with events all carry one id (`hsame`): `r`'s
watcher's responses with events sent before, then `r`, are its responses with events received up
to `n`. -/
theorem send_claim (rcv : List mvcc.RespM) (S : List Nat) (n : Nat) (r : mvcc.RespM)
    (hr : rcv[n]? = some r) (hpre : S.filter (idOf rcv r.id) ++ [n] <+: idxOf rcv r.id)
    (hev : r.evs ≠ [])
    (hsame : ∀ (m1 m2 : Nat) (x1 x2 : mvcc.RespM), rcv[m1]? = some x1 → rcv[m2]? = some x2 →
      x1.w = x2.w → x1.evs ≠ [] → x2.evs ≠ [] → x1.id = x2.id) :
    ((S.filterMap (fun m => rcv[m]?)).filter (fun x => decide (x.w = r.w ∧ x.evs ≠ []))) ++ [r] =
      ((rcv.take (n + 1)).filter (fun x => decide (x.w = r.w))).filter
        (fun x => decide (x.evs ≠ [])) := by
  have hn : n < rcv.length := by
    rcases Nat.lt_or_ge n rcv.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hr; cases hr
  let f : Nat → Option mvcc.RespM := fun m => rcv[m]?
  let p : mvcc.RespM → Bool := fun x => decide (x.w = r.w ∧ x.evs ≠ [])
  let q : Nat → Bool := fun m => (f m).any p
  have hq : ∀ m, q m = true → idOf rcv r.id m = true := by
    intro m hm
    simp only [q, f] at hm
    cases hfm : rcv[m]? with
    | none => rw [hfm] at hm; cases hm
    | some x =>
      rw [hfm] at hm
      have hx := of_decide_eq_true (by simpa [p] using hm)
      have := hsame m n x r hfm hr hx.1 hx.2 hev
      unfold idOf; rw [hfm]; simp [this]
  have hqn : q n = true := by simp [q, f, p, hr, hev]
  have hfilt : ∀ L : List Nat, L.filter q = (L.filter (idOf rcv r.id)).filter q := by
    intro L
    rw [List.filter_filter]
    apply List.filter_congr
    intro m _
    cases hqm : q m
    · simp
    · simp [hq m hqm]
  -- the received indices of `r`'s id up to `n`
  have hA : (List.range (n + 1)).filter (idOf rcv r.id) = S.filter (idOf rcv r.id) ++ [n] := by
    have hidn : idOf rcv r.id n = true := by unfold idOf; rw [hr]; simp
    have h1 : (List.range n).filter (idOf rcv r.id) ++ [n] <+: idxOf rcv r.id := by
      have := range_filter_prefix (idOf rcv r.id) (show n + 1 ≤ rcv.length by omega)
      rw [List.range_succ, List.filter_append] at this
      simp only [List.filter_cons, hidn, ↓reduceIte, List.filter_nil] at this
      exact this
    rw [List.range_succ, List.filter_append]
    simp only [List.filter_cons, hidn, ↓reduceIte, List.filter_nil]
    rw [prefix_last_eq (idxOf_nodup rcv r.id) h1 hpre]
  have hL : (S.filterMap f).filter p = ((S.filter (idOf rcv r.id)).filter q).filterMap f := by
    rw [filter_filterMap]; exact congrArg (List.filterMap f) (hfilt S)
  have hR : ((rcv.take (n + 1)).filter (fun x => decide (x.w = r.w))).filter
      (fun x => decide (x.evs ≠ [])) =
      ((S.filter (idOf rcv r.id) ++ [n]).filter q).filterMap f := by
    rw [List.filter_filter, take_eq_filterMap rcv (n + 1) (by omega)]
    rw [show (fun x : mvcc.RespM => decide (x.evs ≠ []) && decide (x.w = r.w)) = p by
      funext x; simp [p, Bool.and_comm]]
    rw [filter_filterMap]
    exact congrArg (List.filterMap f) ((hfilt _).trans (congrArg (List.filter q) hA))
  show (S.filterMap f).filter p ++ [r] = _
  rw [hL, hR, List.filter_append, List.filterMap_append]
  simp [hqn, f, hr]

/-- `send_claim` for a response sent at once on its receipt (`sendInv_recv_direct`). -/
theorem send_claim_direct {rcv : List mvcc.RespM} {S : List Nat} {pend : w64 → List Nat}
    {ids : w64 → Bool} {r : mvcc.RespM} (hI : SendInv rcv S pend ids none)
    (hd : ids r.id = true ∨ r.id = W64 (-1)) (hev : r.evs ≠ [])
    (hsame : ∀ (m1 m2 : Nat) (x1 x2 : mvcc.RespM), (rcv ++ [r])[m1]? = some x1 →
      (rcv ++ [r])[m2]? = some x2 → x1.w = x2.w → x1.evs ≠ [] → x2.evs ≠ [] → x1.id = x2.id) :
    ((S.filterMap (fun m => (rcv ++ [r])[m]?)).filter
        (fun x => decide (x.w = r.w ∧ x.evs ≠ []))) ++ [r] =
      ((rcv ++ [r]).filter (fun x => decide (x.w = r.w))).filter
        (fun x => decide (x.evs ≠ [])) := by
  have hr : (rcv ++ [r])[rcv.length]? = some r := by
    rw [List.getElem?_append_right (Nat.le_refl _)]; simp
  have hpre : S.filter (idOf (rcv ++ [r]) r.id) ++ [rcv.length] <+: idxOf (rcv ++ [r]) r.id := by
    rw [idxOf_snoc, filter_snoc_bound rcv r r.id S hI.bound, hI.split r.id,
      hI.noPend r.id hd (by simp)]
    simp
  have := send_claim (rcv ++ [r]) S rcv.length r hr hpre hev hsame
  rw [this, show rcv.length + 1 = (rcv ++ [r]).length by simp, List.take_length]

/-- `send_claim` for a pending response flushed (`sendInv_flush`). -/
theorem send_claim_flush {rcv : List mvcc.RespM} {S : List Nat} {pend : w64 → List Nat}
    {ids : w64 → Bool} {X : w64} {n : Nat} {P : List Nat} {r : mvcc.RespM}
    (hI : SendInv rcv S pend ids (some X)) (hp : pend X = n :: P) (hr : rcv[n]? = some r)
    (hev : r.evs ≠ [])
    (hsame : ∀ (m1 m2 : Nat) (x1 x2 : mvcc.RespM), rcv[m1]? = some x1 → rcv[m2]? = some x2 →
      x1.w = x2.w → x1.evs ≠ [] → x2.evs ≠ [] → x1.id = x2.id) :
    r.id = X ∧
    ((S.filterMap (fun m => rcv[m]?)).filter (fun x => decide (x.w = r.w ∧ x.evs ≠ []))) ++ [r] =
      ((rcv.take (n + 1)).filter (fun x => decide (x.w = r.w))).filter
        (fun x => decide (x.evs ≠ [])) := by
  have hn : n ∈ idxOf rcv X := by rw [hI.split X, hp]; simp
  obtain ⟨x, hx, hxX⟩ := idOf_eq_id (mem_idxOf hn).2
  rw [hr] at hx; cases hx
  refine ⟨hxX, send_claim rcv S n r hr ?_ hev hsame⟩
  rw [hxX, hI.split X, hp]
  exact ⟨P, by simp⟩

/-! ## Bookkeeping for the send loop's proof -/

@[simp] theorem upd_same {α : Type} (g : w64 → α) (X : w64) (a : α) : upd g X a X = a := by
  simp [upd]

theorem upd_ne {α : Type} (g : w64 → α) {X Y : w64} (a : α) (h : Y ≠ X) : upd g X a Y = g Y := by
  simp [upd, h]

@[simp] theorem upd_upd {α : Type} (g : w64 → α) (X : w64) (a b : α) :
    upd (upd g X a) X b = upd g X b := by
  funext Y; unfold upd; by_cases h : Y = X <;> simp [h]

theorem upd_self {α : Type} (g : w64 → α) (X : w64) : upd g X (g X) = g := by
  funext Y; unfold upd; by_cases h : Y = X
  · subst h; simp
  · simp [h]

/-- The last of a response's watcher's responses received up to it is the response. -/
theorem take_filter_getLast (rcv : List mvcc.RespM) {n : Nat} {x : mvcc.RespM}
    (h : rcv[n]? = some x) :
    ((rcv.take (n + 1)).filter (fun y => decide (y.w = x.w))).getLast? = some x := by
  have hn : n < rcv.length := by
    rcases Nat.lt_or_ge n rcv.length with hl | hl
    · exact hl
    · rw [List.getElem?_eq_none hl] at h; cases h
  rw [List.take_add_one, h]
  simp [List.filter_append, List.getLast?_append]

/-- Indices below the length read the same after a receipt. -/
theorem filterMap_snoc_bound (rcv : List mvcc.RespM) (r : mvcc.RespM) (S : List Nat)
    (hb : ∀ m ∈ S, m < rcv.length) :
    S.filterMap (fun m => (rcv ++ [r])[m]?) = S.filterMap (fun m => rcv[m]?) := by
  induction S with
  | nil => rfl
  | cons a S ih =>
    simp only [List.filterMap_cons]
    rw [List.getElem?_append_left (hb a List.mem_cons_self),
      ih (fun m hm => hb m (List.mem_cons_of_mem _ hm))]

/-- Buffered indices (all reading a response) read the same after a receipt. -/
theorem map_snoc_some {β : Type} (rcv : List mvcc.RespM) (r : mvcc.RespM) (P : List Nat)
    (xs : List β) (f : β → mvcc.RespM) (h : P.map (fun n => rcv[n]?) = xs.map (fun p => some (f p))) :
    P.map (fun n => (rcv ++ [r])[n]?) = xs.map (fun p => some (f p)) := by
  rw [← h]
  apply List.map_congr_left
  intro n hn
  have : rcv[n]?.isSome := by
    have hm : rcv[n]? ∈ P.map (fun n => rcv[n]?) := List.mem_map_of_mem hn
    rw [h] at hm
    obtain ⟨p, -, hp⟩ := List.mem_map.1 hm
    rw [← hp]; rfl
  rw [List.getElem?_append_left]
  rcases Nat.lt_or_ge n rcv.length with hl | hl
  · exact hl
  · rw [List.getElem?_eq_none hl] at this; cases this

/-- The `k`th buffered index reads the `k`th buffered response. -/
theorem map_some_get {β : Type} (rcv : List mvcc.RespM) (P : List Nat) (xs : List β)
    (f : β → mvcc.RespM) (h : P.map (fun n => rcv[n]?) = xs.map (fun p => some (f p)))
    {k n : Nat} {p : β} (hn : P[k]? = some n) (hp : xs[k]? = some p) : rcv[n]? = some (f p) := by
  have h1 : (P.map (fun n => rcv[n]?))[k]? = some rcv[n]? := by simp [hn]
  have h2 : (xs.map (fun p => some (f p)))[k]? = some (some (f p)) := by simp [hp]
  rw [h] at h1
  rw [h1] at h2
  exact Option.some.inj h2

/-- A copy loop's step: the `k`th element written over the zero fill. -/
theorem take_replicate_set {α : Type} (ps : List α) (z : α) {k : Nat} (hk : k < ps.length) :
    (ps.take k ++ List.replicate (ps.length - k) z).set k ps[k] =
      ps.take (k + 1) ++ List.replicate (ps.length - (k + 1)) z := by
  have hl : (ps.take k).length = k := by simp; omega
  rw [List.set_append_right _ _ (by omega), hl, Nat.sub_self]
  obtain ⟨m, hm⟩ : ∃ m, ps.length - k = m + 1 := ⟨ps.length - k - 1, by omega⟩
  rw [hm, List.replicate_succ, List.set_cons_zero, List.take_add_one]
  simp only [List.getElem?_eq_getElem hk, Option.toList_some, List.append_assoc,
    List.singleton_append]
  congr 2
  rw [show ps.length - (k + 1) = m by omega]

end v3rpc
end EtcdGrove
end Perennial
