/-
**The send loop's bookkeeping, pure** (the mvcc API migration, 2026-11-05: moved out of
`serverWatchStream__sendLoop.lean`, so that it is checked without the server): the liveness of the
ids after a response is sent (`idLive_snoc_*`, `idsLive_*`), a buffered index's id (`pend_id`), a
source not yet sent (`src_fresh`), and every received `-1` sent (`neg1_sent`, `createdAfter`'s
last conjunct). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.WatchSendHist

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace v3rpc

/-- An mvcc response sent leaves every id's liveness as it was. -/
theorem idLive_snoc_src (D : List WatchRespM) (m : WatchRespM)
    (h : m.src ≠ none) (X : w64) : idLive (D ++ [m]) X ↔ idLive D X := by
  unfold idLive
  simp [List.filter_append, h]

/-- A control response sent decides its own id's liveness. -/
theorem idLive_snoc_ctrl (D : List WatchRespM) (m : WatchRespM)
    (h : m.src = none) (X : w64) :
    idLive (D ++ [m]) X ↔
      (if m.watchId = X then (m.created && !m.canceled) = true else idLive D X) := by
  unfold idLive
  by_cases hx : m.watchId = X
  · simp [List.filter_append, h, hx]
  · simp [List.filter_append, h, hx]

/-- The announced ids after a created response for `X` is sent (`ids[X]` set): live. -/
theorem idsLive_created (D : List WatchRespM) (m : WatchRespM)
    (IM : GMap w64 Unit) (X : w64) (hsrc : m.src = none) (hX : m.watchId = X)
    (hL : ∀ Y, Y ≠ W64 (-1) → ((IM !! Y).isSome = true ↔ idLive D Y))
    (hok : X ≠ W64 (-1) → (m.created && !m.canceled) = true) :
    ∀ Y, Y ≠ W64 (-1) → (((<[X := ()]> IM) !! Y).isSome = true ↔ idLive (D ++ [m]) Y) := by
  intro Y hY
  rw [idLive_snoc_ctrl _ _ hsrc]
  by_cases h : Y = X
  · subst h; simp [GMap.lookup_insert, hX, hok hY]
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm h)]
    simp only [hX, Ne.symm h, ↓reduceIte]
    exact hL Y hY

/-- The announced ids after a canceled response for `X ≠ -1` is sent (`ids[X]` deleted). -/
theorem idsLive_canceled (D : List WatchRespM) (m : WatchRespM)
    (IM : GMap w64 Unit) (X : w64) (hsrc : m.src = none) (hX : m.watchId = X)
    (hc : m.canceled = true)
    (hL : ∀ Y, Y ≠ W64 (-1) → ((IM !! Y).isSome = true ↔ idLive D Y)) :
    ∀ Y, Y ≠ W64 (-1) →
      (((GMap.delete X IM) !! Y).isSome = true ↔ idLive (D ++ [m]) Y) := by
  intro Y hY
  rw [idLive_snoc_ctrl _ _ hsrc]
  by_cases h : Y = X
  · subst h; simp [GMap.lookup_delete, hX, hc]
  · rw [GMap.lookup_delete_ne _ (Ne.symm h)]
    simp only [hX, Ne.symm h, ↓reduceIte]
    exact hL Y hY

/-- The announced ids after a control response for `-1` is sent: as they were. -/
theorem idsLive_neg1 (D : List WatchRespM) (m : WatchRespM)
    (IM : GMap w64 Unit) (hsrc : m.src = none) (hX : m.watchId = W64 (-1))
    (hL : ∀ Y, Y ≠ W64 (-1) → ((IM !! Y).isSome = true ↔ idLive D Y)) :
    ∀ Y, Y ≠ W64 (-1) → ((IM !! Y).isSome = true ↔ idLive (D ++ [m]) Y) := by
  intro Y hY
  rw [idLive_snoc_ctrl _ _ hsrc]
  have : m.watchId ≠ Y := by rw [hX]; exact Ne.symm hY
  simp only [this, ↓reduceIte]
  exact hL Y hY

/-- The announced ids after an mvcc response is sent: as they were. -/
theorem idsLive_src (D : List WatchRespM) (m : WatchRespM)
    (IM : GMap w64 Unit) (hsrc : m.src ≠ none)
    (hL : ∀ Y, Y ≠ W64 (-1) → ((IM !! Y).isSome = true ↔ idLive D Y)) :
    ∀ Y, Y ≠ W64 (-1) → ((IM !! Y).isSome = true ↔ idLive (D ++ [m]) Y) := by
  intro Y hY
  rw [idLive_snoc_src _ _ hsrc]
  exact hL Y hY

/-- A pending index of `X` names a response of id `X`. -/
theorem pend_id {rcv : List mvcc.api.WResp} {S : List Nat} {pend : w64 → List Nat}
    {ids : w64 → Bool} {ex : Option w64} (hI : SendInv rcv S pend ids ex) {X : w64}
    {n : Nat} {t : List Nat} (hp : pend X = n :: t) {x : mvcc.api.WResp} (hx : rcv[n]? = some x) :
    x.id = X := by
  have hs := hI.split X
  have hm : n ∈ idxOf rcv X := by rw [hs, hp]; simp
  obtain ⟨-, hid⟩ := mem_idxOf hm
  obtain ⟨y, hy, hyX⟩ := idOf_eq_id hid
  rw [hx] at hy; cases hy; exact hyX

/-- **No response sent so far came from a received index not yet sent** (K1b). -/
theorem src_fresh {rcv : List mvcc.api.WResp} {S : List Nat} {D : List WatchRespM}
    (hD : D.filterMap WatchRespM.src = srcOf rcv S) (n : Nat) (hn : n ∉ S) :
    ∀ m' ∈ D, ∀ y, m'.src ≠ some (n, y) := by
  intro m' hm' y hs
  have h1 : (n, y) ∈ D.filterMap WatchRespM.src := List.mem_filterMap.2 ⟨m', hm', hs⟩
  rw [hD] at h1
  obtain ⟨i, hi, hix⟩ := List.mem_filterMap.1 h1
  cases h : rcv[i]? with
  | none => rw [h] at hix; cases hix
  | some x =>
    rw [h] at hix
    cases hix
    exact hn hi

/-- **Every received response of id `-1` was sent** (unit W-K): the send loop never buffers one
(`SendInv.noPend` at `-1`), so it is among the sent ones (`hD`), with its index. -/
theorem neg1_sent {rcv : List mvcc.api.WResp} {S : List Nat} {pend : w64 → List Nat}
    {ids : w64 → Bool} {D : List WatchRespM} (hI : SendInv rcv S pend ids none)
    (hD : D.filterMap WatchRespM.src = srcOf rcv S) :
    ∀ (n : Nat) (x : mvcc.api.WResp), rcv[n]? = some x → x.id = W64 (-1) →
      ∃ m' ∈ D, m'.src = some (n, x) := by
  intro n x hnx hid
  have hn : n < rcv.length := (List.getElem?_eq_some_iff.1 hnx).1
  have hin : n ∈ idxOf rcv (W64 (-1)) := by
    unfold idxOf; rw [List.mem_filter]
    refine ⟨List.mem_range.2 hn, ?_⟩
    unfold idOf; simp [hnx, hid]
  have hp : pend (W64 (-1)) = [] := hI.noPend _ (Or.inr rfl) (by simp)
  rw [hI.split, hp, List.append_nil, List.mem_filter] at hin
  have hmem : (n, x) ∈ srcOf rcv S := by
    unfold srcOf
    exact List.mem_filterMap.2 ⟨n, hin.1, by simp [hnx]⟩
  rw [← hD] at hmem
  obtain ⟨m', hm', hsrc⟩ := List.mem_filterMap.1 hmem
  exact ⟨m', hm', hsrc⟩

/-- The responses sent after a receipt at its index (`n = rcv.length`), or a flushed one. -/
theorem srcOf_send (rcv : List mvcc.api.WResp) (S : List Nat) (n : Nat) (x : mvcc.api.WResp)
    (hx : rcv[n]? = some x) (D : List WatchRespM) (m : WatchRespM) (hm : m.src = some (n, x))
    (hD : D.filterMap WatchRespM.src = srcOf rcv S) :
    (D ++ [m]).filterMap WatchRespM.src = srcOf rcv (S ++ [n]) := by
  rw [List.filterMap_append, hD, srcOf_append rcv S n x hx]
  simp [hm]

/-- A control response sent leaves the sources as they were. -/
theorem srcOf_ctrl (rcv : List mvcc.api.WResp) (S : List Nat) (D : List WatchRespM)
    (m : WatchRespM) (hm : m.src = none) (hD : D.filterMap WatchRespM.src = srcOf rcv S) :
    (D ++ [m]).filterMap WatchRespM.src = srcOf rcv S := by
  rw [List.filterMap_append, hD]
  simp [hm]

end v3rpc
end EtcdGrove
end Perennial
