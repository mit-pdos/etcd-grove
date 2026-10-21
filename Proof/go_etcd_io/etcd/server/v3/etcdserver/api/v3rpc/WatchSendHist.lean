/-
**The send loop's history** (the watch slice's unit W-K, K2e-7d; pure): what the order of the
responses the send loop sent says, beyond `WatchSendModel`'s per-id order, for the client's
completeness (`fwdEvs`, `fwdIdx`, `InvWatchStream.lean`).

* `SendHist rcv D S`: an index of an id that was announced when a response `y` was sent (`D`'s
  `i`th), not sent since, is after `y`'s. It holds from the start (`sendHist_nil`) and after a
  receipt (`sendHist_recv`), a control response (`sendHist_ctrl`), a send (`sendHist_send`: at
  once, `hnew_direct`; from the buffer, `hnew_flush`).
* `fwdEvs_direct`/`fwdEvs_flush`: when a response is sent, a watcher's responses with events
  sent are those received before it, for a live id it concerns (its own, or any for `-1`;
  `sentEvs_idx`); `fwdIdx_direct`/`fwdIdx_flush`: every
  response sent before it, while its id was live (any, for `-1`), was received before it.
Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.WatchSendModel
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvWatchStream

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace v3rpc

/-- **The send loop's history** (see the file header). -/
def SendHist (rcv : List mvcc.RespM) (D : List WatchRespM) (S : List Nat) : Prop :=
  ∀ (i : Nat) (m' : WatchRespM) (y : mvcc.RespM) (X : w64) (k : Nat), D[i]? = some m' →
    m'.src = some y → X ≠ W64 (-1) → idLive (D.take i) X → k ∈ idxOf rcv X → k ∉ S → y.idx < k

theorem sendHist_nil (rcv : List mvcc.RespM) (S : List Nat) : SendHist rcv [] S := by
  intro i m' _ _ _ hi; simp at hi

/-- The responses sent were received (each at its own index). -/
theorem sent_idx {rcv : List mvcc.RespM} {S : List Nat} {D : List WatchRespM}
    (hD : D.filterMap WatchRespM.src = S.filterMap (fun n => rcv[n]?))
    (hb : ∀ m ∈ S, m < rcv.length)
    (hidx : ∀ (i : Nat) (x : mvcc.RespM), rcv[i]? = some x → x.idx = i) :
    ∀ y ∈ D.filterMap WatchRespM.src, y.idx < rcv.length := by
  intro y hy
  rw [hD] at hy
  obtain ⟨m, hm, hmy⟩ := List.mem_filterMap.1 hy
  rw [hidx m y hmy]; exact hb m hm

theorem sendHist_recv {rcv : List mvcc.RespM} {D : List WatchRespM} {S : List Nat}
    (x : mvcc.RespM) (hsent : ∀ y ∈ D.filterMap WatchRespM.src, y.idx < rcv.length)
    (h : SendHist rcv D S) : SendHist (rcv ++ [x]) D S := by
  intro i m' y X k hi hs hX hl hk hkS
  rw [idxOf_snoc] at hk
  rcases List.mem_append.1 hk with hk | hk
  · exact h i m' y X k hi hs hX hl hk hkS
  · split at hk
    · rw [List.mem_singleton] at hk; subst hk
      exact hsent y (List.mem_filterMap.2 ⟨m', List.mem_of_getElem? hi, hs⟩)
    · cases hk

theorem sendHist_ctrl {rcv : List mvcc.RespM} {D : List WatchRespM} {S : List Nat}
    (c : WatchRespM) (hc : c.src = none) (h : SendHist rcv D S) : SendHist rcv (D ++ [c]) S := by
  intro i m' y X k hi hs hX hl hk hkS
  by_cases hlt : i < D.length
  · rw [List.getElem?_append_left hlt] at hi
    rw [List.take_append_of_le_length (by omega)] at hl
    exact h i m' y X k hi hs hX hl hk hkS
  · rcases Nat.lt_or_ge i (D.length + 1) with h' | h'
    · have : i = D.length := by omega
      subst this
      rw [List.getElem?_append_right (Nat.le_refl _)] at hi
      simp at hi; subst hi; rw [hc] at hs; cases hs
    · rw [List.getElem?_eq_none (by simp; omega)] at hi; cases hi

/-- **A response `x` sent** (its index `n`): `hnew`, what it says of the ids live then. -/
theorem sendHist_send {rcv : List mvcc.RespM} {D : List WatchRespM} {S : List Nat}
    (m : WatchRespM) (x : mvcc.RespM) (n : Nat) (hm : m.src = some x)
    (hnew : ∀ (X : w64) (k : Nat), X ≠ W64 (-1) → idLive D X → k ∈ idxOf rcv X → k ∉ S ++ [n] →
      x.idx < k)
    (h : SendHist rcv D S) : SendHist rcv (D ++ [m]) (S ++ [n]) := by
  intro i m' y X k hi hs hX hl hk hkS
  have hkS' : k ∉ S := fun h' => hkS (List.mem_append_left _ h')
  by_cases hlt : i < D.length
  · rw [List.getElem?_append_left hlt] at hi
    rw [List.take_append_of_le_length (by omega)] at hl
    exact h i m' y X k hi hs hX hl hk hkS'
  · rcases Nat.lt_or_ge i (D.length + 1) with h' | h'
    · have : i = D.length := by omega
      subst this
      rw [List.getElem?_append_right (Nat.le_refl _)] at hi
      simp at hi; subst hi
      rw [hm] at hs; cases hs
      rw [List.take_append_of_le_length (Nat.le_refl _), List.take_length] at hl
      exact hnew X k hX hl hk hkS
    · rw [List.getElem?_eq_none (by simp; omega)] at hi; cases hi

/-- The indices of a live id are all sent (no flush under way). -/
theorem live_sent {rcv : List mvcc.RespM} {S : List Nat} {pend : w64 → List Nat}
    {ids : w64 → Bool} {D : List WatchRespM} (hI : SendInv rcv S pend ids none)
    (hL : ∀ X, X ≠ W64 (-1) → (ids X = true ↔ idLive D X)) (X : w64) (hX : X ≠ W64 (-1))
    (hl : idLive D X) {k : Nat} (hk : k ∈ idxOf rcv X) : k ∈ S := by
  rw [hI.split X, hI.noPend X (Or.inl ((hL X hX).2 hl)) (by simp), List.append_nil] at hk
  exact (List.mem_filter.1 hk).1

/-- The indices of an id, in order. -/
theorem idxOf_sorted (rcv : List mvcc.RespM) (X : w64) : (idxOf rcv X).Pairwise (· < ·) := by
  unfold idxOf
  exact (List.pairwise_lt_range).filter _

/-- `sendHist_send`'s `hnew` for a buffered response `n` of `X0` flushed. -/
theorem hnew_flush {rcv : List mvcc.RespM} {S : List Nat} {pend : w64 → List Nat}
    {ids : w64 → Bool} {D : List WatchRespM} {X0 : w64} {n : Nat} {P : List Nat}
    (hI : SendInv rcv S pend ids (some X0)) (hp : pend X0 = n :: P)
    (hL : ∀ X, X ≠ W64 (-1) → (ids X = true ↔ idLive D X)) (x : mvcc.RespM) (hx : x.idx = n) :
    ∀ (X : w64) (k : Nat), X ≠ W64 (-1) → idLive D X → k ∈ idxOf rcv X → k ∉ S ++ [n] →
      x.idx < k := by
  intro X k hX hl hk hkS
  have hkS' : k ∉ S := fun h' => hkS (List.mem_append_left _ h')
  by_cases h : X = X0
  · subst h
    have hs := idxOf_sorted rcv X
    rw [hI.split X, hp] at hs hk
    rcases List.mem_append.1 hk with hk | hk
    · exact absurd (List.mem_filter.1 hk).1 hkS'
    · rcases List.mem_cons.1 hk with rfl | hk
      · exact absurd (List.mem_append_right _ (List.mem_singleton_self _)) hkS
      · rw [hx]
        have := List.pairwise_append.1 hs
        exact List.rel_of_pairwise_cons this.2.1 hk
  · rw [hI.split X, hI.noPend X (Or.inl ((hL X hX).2 hl)) (by simp [Ne.symm h]),
      List.append_nil] at hk
    exact absurd (List.mem_filter.1 hk).1 hkS'

/-- **A buffered index was not sent** (K1b): the indices of id `X` are those sent and those
buffered, without repetition. -/
theorem pend_not_sent {rcv : List mvcc.RespM} {S : List Nat} {pend : w64 → List Nat}
    {ids : w64 → Bool} {ex : Option w64} (hI : SendInv rcv S pend ids ex) {X : w64}
    {n : Nat} {t : List Nat} (hp : pend X = n :: t) : n ∉ S := by
  intro hn
  have hnd : (idxOf rcv X).Nodup := (List.nodup_range).filter _
  have hs := hI.split X
  have hm : n ∈ idxOf rcv X := by rw [hs, hp]; simp
  obtain ⟨-, hid⟩ := mem_idxOf hm
  rw [hs] at hnd
  have hf : n ∈ S.filter (idOf rcv X) := List.mem_filter.2 ⟨hn, hid⟩
  have hpm : n ∈ pend X := by rw [hp]; exact List.mem_cons_self
  have hd := (List.nodup_append.1 hnd).2.2
  first
  | exact hd hf hpm
  | exact hd n hf n hpm rfl
  | exact (hd hf hpm).elim
  | exact absurd rfl (hd n hf n hpm)

/-! ## What a send says of the order -/

/-- **The sent responses with events of a watcher of the id `X`, by index**: those of the sent
indices `S` whose indices of `X` are the first ones up to `n`. -/
theorem sentEvs_idx {rcv : List mvcc.RespM} {S : List Nat} {D : List WatchRespM}
    (hD : D.filterMap WatchRespM.src = S.filterMap (fun n => rcv[n]?)) (w : Loc) (X : w64)
    (hw : ∀ (k : Nat) (y : mvcc.RespM), rcv[k]? = some y → y.w = w → y.evs ≠ [] → y.id = X)
    (n : Nat) (hn : n ≤ rcv.length)
    (hS : S.filter (idOf rcv X) = (List.range n).filter (idOf rcv X)) :
    sentEvsOf D w =
      ((rcv.take n).filter (fun y => decide (y.w = w))).filter (fun y => decide (y.evs ≠ [])) := by
  let f : Nat → Option mvcc.RespM := fun m => rcv[m]?
  let p : mvcc.RespM → Bool := fun x => decide (x.w = w ∧ x.evs ≠ [])
  let q : Nat → Bool := fun m => (f m).any p
  have hq : ∀ m, q m = true → idOf rcv X m = true := by
    intro m hm
    simp only [q, f] at hm
    cases hfm : rcv[m]? with
    | none => rw [hfm] at hm; cases hm
    | some x =>
      rw [hfm] at hm
      have hx := of_decide_eq_true (by simpa [p] using hm)
      unfold idOf; rw [hfm]; simp [hw m x hfm hx.1 hx.2]
  have hfilt : ∀ L : List Nat, L.filter q = (L.filter (idOf rcv X)).filter q := by
    intro L
    rw [List.filter_filter]
    apply List.filter_congr
    intro m _
    cases hqm : q m
    · simp
    · simp [hq m hqm]
  unfold sentEvsOf
  rw [hD, List.filter_filter, take_eq_filterMap rcv n hn]
  rw [show (fun x : mvcc.RespM => decide (x.evs ≠ []) && decide (x.w = w)) = p by
    funext x; simp [p, Bool.and_comm]]
  show (S.filterMap f).filter p = ((List.range n).filterMap f).filter p
  rw [filter_filterMap, filter_filterMap]
  congr 1
  rw [hfilt S, hfilt (List.range n), hS]

/-- **`fwdEvs`, for a response sent at once on its receipt** (the received ones before it, `rcv`). -/
theorem fwdEvs_direct {rcv : List mvcc.RespM} {S : List Nat} {pend : w64 → List Nat}
    {ids : w64 → Bool} {D : List WatchRespM} (hI : SendInv rcv S pend ids none)
    (hL : ∀ X, X ≠ W64 (-1) → (ids X = true ↔ idLive D X))
    (hD : D.filterMap WatchRespM.src = S.filterMap (fun n => rcv[n]?)) (r : mvcc.RespM) (w : Loc)
    (X : w64)
    (hw : ∀ (k : Nat) (y : mvcc.RespM), rcv[k]? = some y → y.w = w → y.evs ≠ [] → y.id = X) :
    fwdEvs D rcv r w X := by
  intro hX hl _
  rw [← List.take_length (l := rcv)]
  refine sentEvs_idx hD w X hw rcv.length (Nat.le_refl _) ?_
  have := hI.split X
  rw [hI.noPend X (Or.inl ((hL X hX).2 hl)) (by simp), List.append_nil] at this
  rw [← this]; rfl

/-- **`fwdEvs`, for a buffered response `n` of `X0` flushed** (the received ones before it,
`rcv.take n`). -/
theorem fwdEvs_flush {rcv : List mvcc.RespM} {S : List Nat} {pend : w64 → List Nat}
    {ids : w64 → Bool} {D : List WatchRespM} {X0 : w64} {n : Nat} {P : List Nat}
    (hI : SendInv rcv S pend ids (some X0)) (hp : pend X0 = n :: P)
    (hD : D.filterMap WatchRespM.src = S.filterMap (fun n => rcv[n]?)) (r : mvcc.RespM)
    (hid : r.id = X0) (hX0 : X0 ≠ W64 (-1)) (w : Loc) (X : w64)
    (hw : ∀ (k : Nat) (y : mvcc.RespM), rcv[k]? = some y → y.w = w → y.evs ≠ [] → y.id = X) :
    fwdEvs D (rcv.take n) r w X := by
  intro _ _ hr
  have hXX : X = X0 := by
    rcases hr with h | h
    · rw [← h, hid]
    · rw [hid] at h; exact absurd h hX0
  subst hXX
  have hn : n ∈ idxOf rcv X := by rw [hI.split X, hp]; simp
  have hnl := (mem_idxOf hn).1
  refine sentEvs_idx hD w X hw n (by omega) ?_
  have hidn := (mem_idxOf hn).2
  have h1 : (List.range n).filter (idOf rcv X) ++ [n] <+: idxOf rcv X := by
    have := range_filter_prefix (idOf rcv X) (show n + 1 ≤ rcv.length by omega)
    rw [List.range_succ, List.filter_append] at this
    simp only [List.filter_cons, hidn, ↓reduceIte, List.filter_nil] at this
    exact this
  have h2 : S.filter (idOf rcv X) ++ [n] <+: idxOf rcv X := by
    rw [hI.split X, hp]; exact ⟨P, by simp⟩
  exact (prefix_last_eq (idxOf_nodup rcv X) h1 h2).symm

/-- **`fwdIdx`, for a response sent at once on its receipt** (its index `rcv.length`). -/
theorem fwdIdx_direct {rcv : List mvcc.RespM} {D : List WatchRespM} (r : mvcc.RespM)
    (hr : r.idx = rcv.length) (hsent : ∀ y ∈ D.filterMap WatchRespM.src, y.idx < rcv.length) :
    fwdIdx D r := by
  intro i m' y hi hs _
  rw [hr]
  exact hsent y (List.mem_filterMap.2 ⟨m', List.mem_of_getElem? hi, hs⟩)

/-- **`fwdIdx`, for a buffered response `n` of `X0 ≠ -1` flushed.** -/
theorem fwdIdx_flush {rcv : List mvcc.RespM} {S : List Nat} {pend : w64 → List Nat}
    {ids : w64 → Bool} {D : List WatchRespM} {X0 : w64} {n : Nat} {P : List Nat}
    (hI : SendInv rcv S pend ids (some X0)) (hp : pend X0 = n :: P) (hH : SendHist rcv D S)
    (r : mvcc.RespM) (hr : r.idx = n) (hid : r.id = X0) (hX0 : X0 ≠ W64 (-1)) :
    fwdIdx D r := by
  intro i m' y hi hs hl
  have hl' : idLive (D.take i) X0 := by
    rcases hl with h | h
    · rw [hid] at h; exact absurd h hX0
    · rw [hid] at h; exact h
  have hn : n ∈ idxOf rcv X0 := by rw [hI.split X0, hp]; simp
  have hnS : n ∉ S := pend_not_sent hI hp
  rw [hr]
  exact hH i m' y X0 n hi hs hX0 hl' hn hnS

end v3rpc
end EtcdGrove
end Perennial
