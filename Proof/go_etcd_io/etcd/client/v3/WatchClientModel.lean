/-
**`run`'s bookkeeping** (the watch slice's unit W-C, 2026-10-15; pure): what the gRPC watch stream's
main goroutine (`watchGRPCStream.run`, `client/v3/watch.go`) knows of the requests it sent, the
responses it received, its substreams and its maps, and the facts its proof keeps about them.
Lean-first, no Rocq counterpart.

* `WPh`: a substream's phase: `queued` (in `resuming`, its create sent at an up position or not),
  `reg X` (registered at the watch id `X`, in `substreams`), `closedRun X` (registered, its `recvc`
  closed by `run` on the server's cancel, in `closing`), `orphan` (its create refused: `recvc`
  closed, in no map).
* `RunSt`: the requests sent (`L`), the responses received (`Dm`), the pending create (`pend`),
  the answered positions (`ansd`), the registered ids (`regs`), `substreams` (`M`), `resuming`
  (`l`), `closing` (`CL`), `cancelSet` (`CS`).
* `phOk S ws ph`: a substream's phase agrees with the maps; `gOk S U`: the facts across them
  (`U`, the substreams `run` made and has not yet seen stop).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvWatchStream
public import Proof.go_etcd_io.etcd.client.v3.InvWatch

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace client

open v3rpc

/-! ## The model -/

/-- A substream's phase (see the file header). -/
inductive WPh where
  | queued (si : Option Nat)
  | reg (X : w64)
  | closedRun (X : w64)
  | orphan

/-- What `run` knows (see the file header). -/
structure RunSt where
  L : List WatchReqM
  Dm : List WatchRespM
  pend : Option Nat
  ansd : List Nat
  regs : List w64
  M : GMap w64 Loc
  l : List Loc
  CL : GMap Loc Unit
  CS : GMap w64 Unit

/-- **A substream's phase agrees with the maps.** -/
def phOk (S : RunSt) (ws : Loc) : WPh → Prop
  | .queued si => (∀ X, S.M !! X ≠ some ws) ∧ ws ∈ S.l ∧ S.CL !! ws = none ∧
      (∀ i, si = some i → S.pend = some i ∧ S.l.head? = some ws) ∧
      (si = none → S.l.head? = some ws → S.pend = none)
  | .reg X => S.M !! X = some ws ∧ ws ∉ S.l ∧ S.CL !! ws = none ∧ X ∈ S.regs ∧
      X ≠ W64 (-1) ∧
      (S.CS !! X = none → ∀ i, S.L[i]? = some (WatchReqM.cancel X) → i ∈ S.ansd) ∧
      (∀ i i', S.L[i]? = some (WatchReqM.cancel X) → S.L[i']? = some (WatchReqM.cancel X) → i ∉ S.ansd →
        i' ∉ S.ansd → i = i')
  | .closedRun X => S.M !! X = some ws ∧ ws ∉ S.l ∧ S.CL !! ws = some () ∧ X ∈ S.regs ∧
      X ≠ W64 (-1) ∧ ¬ idLive S.Dm X ∧ (∀ i, S.L[i]? = some (WatchReqM.cancel X) → i ∈ S.ansd)
  | .orphan => (∀ X, S.M !! X ≠ some ws) ∧ ws ∉ S.l ∧ S.CL !! ws = none

/-- **The facts across the maps and the stream** (`U`: the substreams `run` made, not yet seen
stop). -/
def gOk (S : RunSt) (U : GMap Loc Unit) : Prop :=
  (∀ X ws, S.M !! X = some ws → U !! ws = some ()) ∧
  (∀ X Y ws, S.M !! X = some ws → S.M !! Y = some ws → X = Y) ∧
  (∀ ws ∈ S.l, ws ≠ null → U !! ws = some ()) ∧
  (S.l.filter (fun x => decide (x ≠ null))).Nodup ∧
  (∀ ws, S.CL !! ws = some () → U !! ws = some ()) ∧
  U !! null = none ∧
  (∀ x ∈ S.L, (∃ c, x = WatchReqM.create c) ∨ (∃ id, x = WatchReqM.cancel id)) ∧
  (∀ (i : Nat) c, S.L[i]? = some (WatchReqM.create c) → i ∈ S.ansd ∨ S.pend = some i) ∧
  (∀ (i : Nat) (id : w64), S.L[i]? = some (WatchReqM.cancel id) → id ∈ S.regs) ∧
  (∀ i, S.pend = some i → i ∉ S.ansd ∧ (∃ c, S.L[i]? = some (WatchReqM.create c)) ∧ S.l ≠ []) ∧
  (∀ i ∈ S.ansd, i < S.L.length) ∧
  (∀ j m ρ, S.Dm[j]? = some m → m.src = some ρ →
    ρ.id ≠ W64 (-1) ∧ idLive (S.Dm.take j) ρ.id) ∧
  (∀ m ∈ S.Dm, m.src = none → m.created = true → m.canceled = false → m.watchId ∈ S.regs)

/-- The model at `run`'s start: nothing sent, received or made. -/
def RunSt.init : RunSt :=
  { L := [], Dm := [], pend := none, ansd := [], regs := [], M := ∅, l := [], CL := ∅, CS := ∅ }

theorem gOk_init : gOk RunSt.init ∅ := by
  unfold gOk RunSt.init
  simp [GMap.lookup_empty]

/-! ## Watch ids -/

/-- The control responses of the id `X`. -/
abbrev ctrlOf (L : List WatchRespM) (X : w64) : List WatchRespM :=
  L.filter (fun m => decide (m.src = none ∧ m.watchId = X))

/-- **`idLive` one response on**: a control response of the id decides; any other leaves it. -/
theorem idLive_snoc (L : List WatchRespM) (m : WatchRespM) (X : w64) :
    idLive (L ++ [m]) X =
      if m.src = none ∧ m.watchId = X then (m.created && !m.canceled) = true else idLive L X := by
  unfold idLive
  rw [List.filter_append]
  by_cases h : m.src = none ∧ m.watchId = X
  · rw [if_pos h]
    have : List.filter (fun m => decide (m.src = none ∧ m.watchId = X)) [m] = [m] := by
      simp [h]
    rw [this, List.getLast?_append]
    simp
  · rw [if_neg h]
    have : List.filter (fun m => decide (m.src = none ∧ m.watchId = X)) [m] = [] := by
      simp [h]
    rw [this, List.append_nil]

/-- A live id was announced: some control response of the id is a created, not canceled, one. -/
theorem idLive_exists {L : List WatchRespM} {X : w64} (h : idLive L X) :
    ∃ m ∈ L, m.src = none ∧ m.watchId = X ∧ m.created = true ∧ m.canceled = false := by
  unfold idLive at h
  cases hl : (L.filter (fun m => decide (m.src = none ∧ m.watchId = X))).getLast? with
  | none => rw [hl] at h; cases h
  | some m =>
    rw [hl] at h
    simp only [Option.map_some, Option.some.injEq, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
      Bool.not_true] at h
    have hm := List.mem_of_getLast? hl
    rw [List.mem_filter] at hm
    simp only [decide_eq_true_eq] at hm
    exact ⟨m, hm.1, hm.2.1, hm.2.2, h.1, h.2⟩

/-- The responses with events of the watcher `w`, by their mvcc response. -/
theorem sentEvsOf_snoc (L : List WatchRespM) (m : WatchRespM) (w : Loc) :
    sentEvsOf (L ++ [m]) w =
      sentEvsOf L w ++ (match m.src with
        | some ρ => if ρ.w = w ∧ ρ.evs ≠ [] then [ρ] else []
        | none => []) := by
  unfold sentEvsOf
  rw [List.filterMap_append, List.filter_append]
  congr 1
  cases h : m.src with
  | none => simp [h]
  | some ρ =>
    by_cases hc : ρ.w = w ∧ ρ.evs ≠ []
    · simp [h, hc]
    · simp only [List.filterMap_cons, h, List.filterMap_nil, if_neg hc]
      simp only [List.filter_eq_nil_iff, List.mem_singleton, forall_eq, decide_eq_true_eq]
      exact hc

/-- The events of a list of responses, those without events left out. -/
theorem flatten_evs_filter (rs : List mvcc.RespM) :
    ((rs.filter (fun x => decide (x.evs ≠ []))).map mvcc.RespM.evs).flatten =
      (rs.map mvcc.RespM.evs).flatten := by
  induction rs with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : x.evs = []
    · rw [List.filter_cons_of_neg (by simp [h])]
      simp only [List.map_cons, List.flatten_cons, h, List.nil_append]
      exact ih
    · rw [List.filter_cons_of_pos (by simp [h])]
      simp only [List.map_cons, List.flatten_cons]
      rw [ih]

/-! ## `resuming`'s `nilOut` and the transitions -/

/-- `nilOut` replaces the first `ws` by `null` (if any). -/
theorem nilOut_cases (l : List Loc) (ws : Loc) :
    (ws ∉ l ∧ nilOut l ws = l) ∨
      ∃ i, l[i]? = some ws ∧ (∀ j < i, l[j]? ≠ some ws) ∧ nilOut l ws = l.set i null := by
  unfold nilOut
  cases h : l.findIdx? (· = ws) with
  | none =>
    left
    refine ⟨fun hm => ?_, rfl⟩
    rw [List.findIdx?_eq_none_iff] at h
    have := h ws hm
    simp at this
  | some i =>
    right
    obtain ⟨hi, hp, hlt⟩ := List.findIdx?_eq_some_iff_getElem.1 h
    refine ⟨i, ?_, ?_, rfl⟩
    · rw [List.getElem?_eq_getElem hi]; simpa using hp
    · intro j hj hjw
      have hjl : j < l.length := by omega
      have := hlt j hj
      rw [List.getElem?_eq_getElem hjl] at hjw
      simp at hjw
      simp [hjw] at this

theorem nilOut_length (l : List Loc) (ws : Loc) : (nilOut l ws).length = l.length := by
  rcases nilOut_cases l ws with ⟨-, h⟩ | ⟨i, -, -, h⟩ <;> rw [h]; simp

theorem mem_nilOut {l : List Loc} {ws x : Loc} (h : x ∈ nilOut l ws) (hx : x ≠ null) : x ∈ l := by
  rcases nilOut_cases l ws with ⟨-, he⟩ | ⟨i, -, -, he⟩
  · rw [he] at h; exact h
  · rw [he] at h
    obtain ⟨j, hj, hjx⟩ := List.getElem_of_mem h
    rw [List.getElem_set] at hjx
    split at hjx
    · exact absurd hjx.symm hx
    · rw [← hjx]; exact List.getElem_mem _

theorem mem_nilOut_of {l : List Loc} {ws x : Loc} (h : x ∈ l) (hx : x ≠ ws) : x ∈ nilOut l ws := by
  rcases nilOut_cases l ws with ⟨-, he⟩ | ⟨i, hi, -, he⟩
  · rw [he]; exact h
  · rw [he]
    obtain ⟨j, hj, hjx⟩ := List.getElem_of_mem h
    have hij : i ≠ j := by
      intro e; subst e
      rw [List.getElem?_eq_getElem hj] at hi
      simp at hi; exact hx (hjx.symm.trans hi)
    have hj' : j < (l.set i null).length := by simp; exact hj
    have : (l.set i null)[j]'hj' = x := by
      rw [List.getElem_set_ne hij]; exact hjx
    rw [← this]; exact List.getElem_mem _

/-- Two occurrences of an element the filter keeps break its distinctness. -/
theorem two_occ_not_nodup {l : List Loc} {a : Loc} {i j : Nat} (hij : i < j) (hi : l[i]? = some a)
    (hj : l[j]? = some a) (ha : a ≠ null) : ¬ (l.filter (fun x => decide (x ≠ null))).Nodup := by
  intro hnd
  have hjl : j < l.length := (List.getElem?_eq_some_iff.1 hj).1
  have hsplit : l = l.take j ++ l.drop j := (List.take_append_drop _ _).symm
  have h1 : List.Sublist [a] (l.take j) := by
    rw [List.singleton_sublist]
    have : (l.take j)[i]? = some a := by rw [List.getElem?_take_of_lt hij]; exact hi
    exact List.mem_of_getElem? this
  have h2 : List.Sublist [a] (l.drop j) := by
    rw [List.singleton_sublist]
    have : (l.drop j)[0]? = some a := by rw [List.getElem?_drop]; simpa using hj
    exact List.mem_of_getElem? this
  have hs : List.Sublist [a, a] l := by
    have := h1.append h2
    rw [← hsplit] at this
    simpa using this
  have hs' := hs.filter (fun x => decide (x ≠ null))
  have hf : [a, a].filter (fun x => decide (x ≠ null)) = [a, a] := by simp [ha]
  rw [hf] at hs'
  have := hnd.sublist hs'
  simp at this

/-- With `ws` (non-null) at most once, it is gone after `nilOut`. -/
theorem not_mem_nilOut {l : List Loc} {ws : Loc} (hws : ws ≠ null)
    (hnd : (l.filter (fun x => decide (x ≠ null))).Nodup) : ws ∉ nilOut l ws := by
  rcases nilOut_cases l ws with ⟨hn, he⟩ | ⟨i, hi, -, he⟩
  · rw [he]; exact hn
  · rw [he]
    intro hm
    obtain ⟨j, hj, hjx⟩ := List.getElem_of_mem hm
    have hjl : j < l.length := by simpa using hj
    by_cases hij : i = j
    · subst hij
      rw [List.getElem_set_self] at hjx
      exact hws hjx.symm
    · rw [List.getElem_set_ne hij] at hjx
      have hj' : l[j]? = some ws := by rw [List.getElem?_eq_getElem hjl, hjx]
      rcases Nat.lt_or_gt_of_ne hij with h | h
      · exact two_occ_not_nodup h hi hj' hws hnd
      · exact two_occ_not_nodup h hj' hi hws hnd

/-- The first entry after `nilOut`: `null` if it was `ws`, else unchanged. -/
theorem nilOut_head? (l : List Loc) (ws : Loc) (h : l.head? ≠ some ws) :
    (nilOut l ws).head? = l.head? := by
  rcases nilOut_cases l ws with ⟨-, he⟩ | ⟨i, hi, -, he⟩
  · rw [he]
  · rw [he]
    cases i with
    | zero =>
      exfalso; apply h
      rw [List.head?_eq_getElem?]; exact hi
    | succ k =>
      cases l with
      | nil => rfl
      | cons x xs => simp [List.set_cons_succ]

theorem nilOut_head?_self (l : List Loc) (ws : Loc) (h : l.head? = some ws) :
    (nilOut l ws).head? = some null := by
  rcases nilOut_cases l ws with ⟨hn, -⟩ | ⟨i, -, hfirst, he⟩
  · exact absurd (List.mem_of_mem_head? h) hn
  · rw [he]
    cases i with
    | zero => cases l with
      | nil => simp at h
      | cons x xs => simp [List.set_cons_zero]
    | succ k =>
      exfalso
      apply hfirst 0 (by omega)
      rw [← List.head?_eq_getElem?]; exact h

theorem filter_set_null_sublist (l : List Loc) (i : Nat) :
    List.Sublist ((l.set i null).filter (fun x => decide (x ≠ null)))
      (l.filter (fun x => decide (x ≠ null))) := by
  induction l generalizing i with
  | nil => simp
  | cons x xs ih =>
    cases i with
    | zero =>
      simp only [List.set_cons_zero, List.filter_cons]
      by_cases hx : x = null
      · simp [hx]
      · simp [hx]
    | succ k =>
      simp only [List.set_cons_succ, List.filter_cons]
      split
      · exact (ih k).cons₂ _
      · exact ih k

theorem nilOut_nodup {l : List Loc} {ws : Loc}
    (hnd : (l.filter (fun x => decide (x ≠ null))).Nodup) :
    ((nilOut l ws).filter (fun x => decide (x ≠ null))).Nodup := by
  rcases nilOut_cases l ws with ⟨-, he⟩ | ⟨i, -, -, he⟩
  · rw [he]; exact hnd
  · rw [he]
    exact hnd.sublist (filter_set_null_sublist l i)


/-- The watch id field's value in a phase. -/
def WPh.id : WPh → w64
  | .reg X => X
  | .closedRun X => X
  | _ => W64 (-1)

/-- The model after `closeSubstream(ws)` of a substream of id `id` and `closing`'s `delete`. -/
def RunSt.closeWs (S : RunSt) (ws : Loc) (id : w64) : RunSt :=
  { S with M := if id = W64 (-1) then S.M else GMap.delete id S.M,
           l := if id = W64 (-1) then nilOut S.l ws else S.l,
           CL := GMap.delete ws S.CL }

theorem phOk_id_neg {S : RunSt} {ws : Loc} {ph : WPh} (h : phOk S ws ph) (hid : ph.id = W64 (-1)) :
    ∀ X, S.M !! X ≠ some ws := by
  cases ph with
  | queued si => exact h.1
  | reg X => simp only [WPh.id] at hid; exact absurd hid h.2.2.2.2.1
  | closedRun X => simp only [WPh.id] at hid; exact absurd hid h.2.2.2.2.1
  | orphan => exact h.1

theorem phOk_id_pos {S : RunSt} {ws : Loc} {ph : WPh} (h : phOk S ws ph) (hid : ph.id ≠ W64 (-1)) :
    S.M !! ph.id = some ws ∧ ws ∉ S.l := by
  cases ph with
  | queued si => exact absurd rfl hid
  | reg X => exact ⟨h.1, h.2.1⟩
  | closedRun X => exact ⟨h.1, h.2.1⟩
  | orphan => exact absurd rfl hid

theorem closeWs_ok {S : RunSt} {U : GMap Loc Unit} {ws : Loc} {ph : WPh} (hg : gOk S U)
    (hU : U !! ws = some ()) (hph : phOk S ws ph) :
    gOk (S.closeWs ws ph.id) (GMap.delete ws U) ∧
      ∀ ws' ph', ws' ≠ ws → U !! ws' = some () → phOk S ws' ph' →
        phOk (S.closeWs ws ph.id) ws' ph' := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13⟩ := hg
  have hwsn : ws ≠ null := fun e => by rw [e, g6] at hU; cases hU
  -- the lookups of the new `substreams`
  have hM : ∀ X ws', (S.closeWs ws ph.id).M !! X = some ws' → S.M !! X = some ws' ∧ ws' ≠ ws := by
    intro X ws' h
    unfold RunSt.closeWs at h
    simp only at h
    by_cases hid : ph.id = W64 (-1)
    · rw [if_pos hid] at h
      refine ⟨h, fun e => ?_⟩
      subst e; exact phOk_id_neg hph hid X h
    · rw [if_neg hid] at h
      by_cases hX : ph.id = X
      · subst hX; rw [GMap.lookup_delete] at h; cases h
      · rw [GMap.lookup_delete_ne _ hX] at h
        refine ⟨h, fun e => ?_⟩
        subst e
        exact hX (g2 _ _ _ (phOk_id_pos hph hid).1 h)
  have hMr : ∀ X ws', ws' ≠ ws → S.M !! X = some ws' → (S.closeWs ws ph.id).M !! X = some ws' := by
    intro X ws' hne h
    unfold RunSt.closeWs
    simp only
    by_cases hid : ph.id = W64 (-1)
    · rw [if_pos hid]; exact h
    · rw [if_neg hid]
      have hX : ph.id ≠ X := by
        intro e; subst e
        rw [(phOk_id_pos hph hid).1] at h; cases h; exact hne rfl
      rw [GMap.lookup_delete_ne _ hX]; exact h
  have hl : ∀ x, x ≠ ws → x ≠ null → (x ∈ (S.closeWs ws ph.id).l ↔ x ∈ S.l) := by
    intro x hx hxn
    unfold RunSt.closeWs
    simp only
    split
    · exact ⟨fun hm => mem_nilOut hm hxn, fun hm => mem_nilOut_of hm hx⟩
    · exact Iff.rfl
  have hlen : (S.closeWs ws ph.id).l.length = S.l.length := by
    unfold RunSt.closeWs; simp only; split
    · exact nilOut_length _ _
    · rfl
  -- the first entry: unchanged, or `null` where it was `ws`
  have hhead : ∀ x, x ≠ null → (S.closeWs ws ph.id).l.head? = some x → S.l.head? = some x := by
    intro x hxn h
    unfold RunSt.closeWs at h; simp only at h
    split at h
    · by_cases hh : S.l.head? = some ws
      · rw [nilOut_head?_self _ _ hh] at h; cases h; exact absurd rfl hxn
      · rw [nilOut_head? _ _ hh] at h; exact h
    · exact h
  have hhead' : ∀ x, x ≠ ws → S.l.head? = some x → (S.closeWs ws ph.id).l.head? = some x := by
    intro x hx h
    unfold RunSt.closeWs; simp only; split
    · rw [nilOut_head? _ _ (by rw [h]; intro e; cases e; exact hx rfl)]; exact h
    · exact h
  have hCL : ∀ x, x ≠ ws → (S.closeWs ws ph.id).CL !! x = S.CL !! x := by
    intro x hx; unfold RunSt.closeWs; simp only; exact GMap.lookup_delete_ne _ (Ne.symm hx)
  have hUd : ∀ x, x ≠ ws → (GMap.delete ws U) !! x = U !! x := fun x hx =>
    GMap.lookup_delete_ne _ (Ne.symm hx)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, g7, g8, g9, ?_, g11, g12, g13⟩, ?_⟩
  · intro X ws' h
    obtain ⟨h1, h2⟩ := hM X ws' h
    rw [hUd ws' h2]; exact g1 X ws' h1
  · intro X Y ws' h1 h2
    exact g2 X Y ws' (hM X ws' h1).1 (hM Y ws' h2).1
  · intro x hx hxn
    by_cases hxw : x = ws
    · exfalso
      subst hxw
      by_cases hid : ph.id = W64 (-1)
      · unfold RunSt.closeWs at hx; simp only [if_pos hid] at hx
        exact not_mem_nilOut hwsn g4 hx
      · unfold RunSt.closeWs at hx; simp only [if_neg hid] at hx
        exact (phOk_id_pos hph hid).2 hx
    · rw [hUd x hxw]; exact g3 x ((hl x hxw hxn).1 hx) hxn
  · unfold RunSt.closeWs; simp only; split
    · exact nilOut_nodup g4
    · exact g4
  · intro x hx
    by_cases hxw : x = ws
    · subst hxw; unfold RunSt.closeWs at hx; simp only at hx
      rw [GMap.lookup_delete] at hx; cases hx
    · rw [hCL x hxw] at hx; rw [hUd x hxw]; exact g5 x hx
  · rw [hUd null (Ne.symm hwsn)]; exact g6
  · intro i hi
    obtain ⟨h1, h2, h3⟩ := g10 i hi
    refine ⟨h1, h2, ?_⟩
    intro e; rw [← List.length_eq_zero_iff, hlen, List.length_eq_zero_iff] at e; exact h3 e
  · intro ws' ph' hne hU' hph'
    have hn' : ws' ≠ null := fun e => by rw [e, g6] at hU'; cases hU'
    cases ph' with
    | queued si =>
      obtain ⟨q1, q2, q3, q4, q5⟩ := hph'
      refine ⟨fun X h => q1 X (hM X ws' h).1, (hl ws' hne hn').2 q2, by rw [hCL ws' hne]; exact q3,
        fun i hi => ⟨(q4 i hi).1, hhead' ws' hne (q4 i hi).2⟩, fun hs hh => q5 hs (hhead ws' hn' hh)⟩
    | reg X =>
      obtain ⟨r1, r2, r3, r4⟩ := hph'
      exact ⟨hMr X ws' hne r1, fun h => r2 ((hl ws' hne hn').1 h), by rw [hCL ws' hne]; exact r3, r4⟩
    | closedRun X =>
      obtain ⟨r1, r2, r3, r4⟩ := hph'
      exact ⟨hMr X ws' hne r1, fun h => r2 ((hl ws' hne hn').1 h), by rw [hCL ws' hne]; exact r3, r4⟩
    | orphan =>
      obtain ⟨o1, o2, o3⟩ := hph'
      exact ⟨fun X h => o1 X (hM X ws' h).1, fun h => o2 ((hl ws' hne hn').1 h),
        by rw [hCL ws' hne]; exact o3⟩

/-- The model after `cancelSet[X] = {}` and a cancel request `Send` (sent or not: `L'`). -/
def RunSt.sentCancel (S : RunSt) (X : w64) (L' : List v3rpc.WatchReqM) : RunSt :=
  { S with CS := GMap.insert X () S.CS, L := L' }

theorem getElem?_snoc_cases {α : Type} {L : List α} {a b : α} {i : Nat} (h : (L ++ [a])[i]? = some b) :
    (i < L.length ∧ L[i]? = some b) ∨ (i = L.length ∧ b = a) := by
  by_cases hi : i < L.length
  · left; rw [List.getElem?_append_left hi] at h; exact ⟨hi, h⟩
  · right
    rw [List.getElem?_append_right (by omega)] at h
    have : i - L.length = 0 := by
      cases hk : i - L.length with
      | zero => rfl
      | succ k => rw [hk] at h; simp at h
    rw [this] at h; simp at h
    exact ⟨by omega, h.symm⟩

theorem cancel_ok {S : RunSt} {U : GMap Loc Unit} {X : w64} {L' : List v3rpc.WatchReqM}
    (hg : gOk S U) (hX : X ∈ S.regs) (hL : L' = S.L ∨ L' = S.L ++ [.cancel X]) :
    gOk (S.sentCancel X L') U ∧
      ∀ ws ph, phOk S ws ph → (∀ X', ph = .closedRun X' → X' ≠ X) →
        (ph = .reg X → S.CS !! X = none) → phOk (S.sentCancel X L') ws ph := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13⟩ := hg
  -- a position of the new list: an old one, or the new cancel
  have hpos : ∀ i r, L'[i]? = some r → (i < S.L.length ∧ S.L[i]? = some r) ∨
      (i = S.L.length ∧ r = .cancel X ∧ L' = S.L ++ [.cancel X]) := by
    intro i r h
    rcases hL with rfl | rfl
    · left; exact ⟨(List.getElem?_eq_some_iff.1 h).1, h⟩
    · rcases getElem?_snoc_cases h with h | h
      · left; exact h
      · right; exact ⟨h.1, h.2, rfl⟩
  have hold : ∀ i, i < S.L.length → L'[i]? = S.L[i]? := by
    intro i hi; rcases hL with rfl | rfl
    · rfl
    · rw [List.getElem?_append_left hi]
  have hlen : S.L.length ≤ L'.length := by rcases hL with rfl | rfl <;> simp
  refine ⟨⟨g1, g2, g3, g4, g5, g6, ?_, ?_, ?_, ?_, ?_, g12, g13⟩, ?_⟩
  · intro x hx
    rcases hL with rfl | rfl
    · exact g7 x hx
    · rcases List.mem_append.1 hx with h | h
      · exact g7 x h
      · simp at h; subst h; right; exact ⟨X, rfl⟩
  · intro i c h
    rcases hpos i _ h with ⟨-, h⟩ | ⟨-, h, -⟩
    · exact g8 i c h
    · cases h
  · intro i id h
    rcases hpos i _ h with ⟨-, h⟩ | ⟨-, h, -⟩
    · exact g9 i id h
    · cases h; exact hX
  · intro i hi
    obtain ⟨h1, ⟨c, h2⟩, h3⟩ := g10 i hi
    refine ⟨h1, ⟨c, ?_⟩, h3⟩
    show L'[i]? = _
    rw [hold i (List.getElem?_eq_some_iff.1 h2).1]; exact h2
  · intro i hi; exact Nat.lt_of_lt_of_le (g11 i hi) hlen
  · intro ws ph hph hcr hreg
    cases ph with
    | queued si => exact hph
    | orphan => exact hph
    | reg X' =>
      obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := hph
      refine ⟨r1, r2, r3, r4, r5, ?_, ?_⟩
      · intro hCS i hi
        unfold RunSt.sentCancel at hCS; simp only at hCS
        have hXX : X ≠ X' := by
          intro e; subst e; rw [GMap.lookup_insert] at hCS; cases hCS
        rw [GMap.lookup_insert_ne _ _ hXX] at hCS
        rcases hpos i _ hi with ⟨-, h⟩ | ⟨-, h, -⟩
        · exact r6 hCS i h
        · cases h; exact absurd rfl hXX
      · intro i i' hi hi' hn hn'
        rcases hpos i _ hi with ⟨hil, h⟩ | ⟨hil, h, -⟩ <;>
          rcases hpos i' _ hi' with ⟨hil', h'⟩ | ⟨hil', h', -⟩
        · exact r7 i i' h h' hn hn'
        · cases h'
          exact absurd (r6 (hreg rfl) i h) hn
        · cases h
          exact absurd (r6 (hreg rfl) i' h') hn'
        · omega
    | closedRun X' =>
      obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hph
      refine ⟨c1, c2, c3, c4, c5, c6, ?_⟩
      intro i hi
      rcases hpos i _ hi with ⟨-, h⟩ | ⟨-, h, -⟩
      · exact c7 i h
      · cases h; exact absurd rfl (hcr X rfl)



/-- The model after a new substream `ws` is appended to `resuming` (and its create sent if it is
the only one: `L'`, `pend'`). -/
def RunSt.addWs (S : RunSt) (ws : Loc) (L' : List v3rpc.WatchReqM) (pend' : Option Nat) : RunSt :=
  { S with l := S.l ++ [ws], L := L', pend := pend' }

/-- The ways `run`'s `reqc` case ends: another substream heads `resuming` (nothing sent); or it is
the only one and its create was not sent, or sent at the up list's end. -/
def addCase (S : RunSt) (L' : List v3rpc.WatchReqM) (pend' : Option Nat) (si : Option Nat) : Prop :=
  (S.l ≠ [] ∧ L' = S.L ∧ pend' = S.pend ∧ si = none) ∨
  (S.l = [] ∧ L' = S.L ∧ pend' = none ∧ si = none) ∨
  (S.l = [] ∧ (∃ c, L' = S.L ++ [.create c]) ∧ pend' = some S.L.length ∧ si = some S.L.length)

theorem addWs_ok {S : RunSt} {U : GMap Loc Unit} {ws : Loc} {L' : List v3rpc.WatchReqM}
    {pend' si : Option Nat} (hg : gOk S U) (hws : ws ≠ null) (hU : U !! ws = none)
    (hc : addCase S L' pend' si) :
    gOk (S.addWs ws L' pend') (GMap.insert ws () U) ∧
      (∀ ws' ph, ws' ≠ ws → phOk S ws' ph → phOk (S.addWs ws L' pend') ws' ph) ∧
      phOk (S.addWs ws L' pend') ws (.queued si) := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13⟩ := hg
  have hwsl : ws ∉ S.l := fun h => by rw [g3 ws h hws] at hU; cases hU
  have hM : ∀ X, S.M !! X ≠ some ws := fun X h => by rw [g1 X ws h] at hU; cases hU
  have hCL : S.CL !! ws = none := by
    cases h : S.CL !! ws with
    | none => rfl
    | some u => cases u; rw [g5 ws h] at hU; cases hU
  -- the old positions keep their requests
  have hpos : ∀ i r, L'[i]? = some r → (i < S.L.length ∧ S.L[i]? = some r) ∨
      (i = S.L.length ∧ (∃ c, r = .create c) ∧ pend' = some S.L.length) := by
    intro i r h
    rcases hc with ⟨-, rfl, -, -⟩ | ⟨-, rfl, -, -⟩ | ⟨-, ⟨c, rfl⟩, hp, -⟩
    · left; exact ⟨(List.getElem?_eq_some_iff.1 h).1, h⟩
    · left; exact ⟨(List.getElem?_eq_some_iff.1 h).1, h⟩
    · rcases getElem?_snoc_cases h with h | h
      · left; exact h
      · right; exact ⟨h.1, ⟨c, h.2⟩, hp⟩
  have hold : ∀ i, i < S.L.length → L'[i]? = S.L[i]? := by
    intro i hi
    rcases hc with ⟨-, rfl, -, -⟩ | ⟨-, rfl, -, -⟩ | ⟨-, ⟨c, rfl⟩, -, -⟩
    · rfl
    · rfl
    · rw [List.getElem?_append_left hi]
  have hlen : S.L.length ≤ L'.length := by
    rcases hc with ⟨-, rfl, -, -⟩ | ⟨-, rfl, -, -⟩ | ⟨-, ⟨c, rfl⟩, -, -⟩ <;> simp
  -- with an empty `resuming`, nothing is pending
  have hnp : S.l = [] → S.pend = none := by
    intro hl
    cases h : S.pend with
    | none => rfl
    | some i => exact absurd hl (g10 i h).2.2
  have hUi : ∀ x, x ≠ ws → (GMap.insert ws () U) !! x = U !! x := fun x hx =>
    GMap.lookup_insert_ne _ _ (Ne.symm hx)
  refine ⟨⟨?_, g2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, g12, g13⟩, ?_, ?_⟩
  · intro X x h
    have hx : x ≠ ws := fun e => hM X (e ▸ h)
    rw [hUi x hx]; exact g1 X x h
  · intro x hx hxn
    show (GMap.insert ws () U) !! x = some ()
    by_cases e : x = ws
    · subst e; exact GMap.lookup_insert _ _ _
    · rw [hUi x e]
      have : x ∈ S.l := by
        have hx' : x ∈ S.l ++ [ws] := hx
        rcases List.mem_append.1 hx' with h | h
        · exact h
        · simp at h; exact absurd h e
      exact g3 x this hxn
  · show ((S.l ++ [ws]).filter _).Nodup
    rw [List.filter_append, List.nodup_append]
    refine ⟨g4, by simp [hws], ?_⟩
    intro a ha b hb e
    subst e
    have hb' : a = ws := by simpa [hws] using hb
    subst hb'
    exact hwsl (List.mem_filter.1 ha).1
  · intro x hx
    change S.CL !! x = some () at hx
    have hx' : x ≠ ws := fun e => by subst e; rw [hCL] at hx; cases hx
    rw [hUi x hx']; exact g5 x hx
  · rw [hUi null (Ne.symm hws)]; exact g6
  · intro x hx
    change x ∈ L' at hx
    obtain ⟨i, hi, hix⟩ := List.getElem_of_mem hx
    have hxi : L'[i]? = some x := by rw [List.getElem?_eq_getElem hi, hix]
    rcases hpos i x hxi with ⟨-, h⟩ | ⟨-, ⟨c, rfl⟩, -⟩
    · exact g7 x (List.mem_of_getElem? h)
    · left; exact ⟨c, rfl⟩
  · intro i c h
    rcases hpos i _ h with ⟨-, h⟩ | ⟨hi, -, hp⟩
    · rcases g8 i c h with h' | h'
      · left; exact h'
      · right
        rcases hc with ⟨-, -, rfl, -⟩ | ⟨hl, -, -, -⟩ | ⟨hl, -, -, -⟩
        · exact h'
        · rw [hnp hl] at h'; cases h'
        · rw [hnp hl] at h'; cases h'
    · right; subst hi; exact hp
  · intro i id h
    rcases hpos i _ h with ⟨-, h⟩ | ⟨-, ⟨c, hc'⟩, -⟩
    · exact g9 i id h
    · cases hc'
  · intro i hi
    rcases hc with ⟨hl, -, rfl, -⟩ | ⟨-, -, rfl, -⟩ | ⟨-, ⟨c, rfl⟩, rfl, -⟩
    · obtain ⟨h1, ⟨c, h2⟩, h3⟩ := g10 i hi
      refine ⟨h1, ⟨c, ?_⟩, by show S.l ++ [ws] ≠ []; simp⟩
      show L'[i]? = _
      rw [hold i (List.getElem?_eq_some_iff.1 h2).1]; exact h2
    · cases hi
    · cases hi
      refine ⟨fun h => Nat.lt_irrefl _ (g11 _ h), ⟨c, by simp [RunSt.addWs]⟩,
        by show S.l ++ [ws] ≠ []; simp⟩
  · intro i hi; exact Nat.lt_of_lt_of_le (g11 i hi) hlen
  · intro ws' ph hne hph
    cases ph with
    | queued si' =>
      obtain ⟨q1, q2, q3, q4, q5⟩ := hph
      have hl : S.l ≠ [] := fun e => by rw [e] at q2; cases q2
      have hcA : L' = S.L ∧ pend' = S.pend := by
        rcases hc with ⟨-, h1, h2, -⟩ | ⟨e, -⟩ | ⟨e, -⟩
        · exact ⟨h1, h2⟩
        · exact absurd e hl
        · exact absurd e hl
      have hhead : (S.l ++ [ws]).head? = S.l.head? := by
        cases h : S.l with
        | nil => exact absurd h hl
        | cons a t => rfl
      refine ⟨q1, List.mem_append_left _ q2, q3, fun i hi => ?_, fun hs hh => ?_⟩
      · obtain ⟨h1, h2⟩ := q4 i hi
        exact ⟨hcA.2 ▸ h1, by show (S.l ++ [ws]).head? = _; rw [hhead]; exact h2⟩
      · have := q5 hs (by rw [← hhead]; exact hh)
        exact hcA.2 ▸ this
    | reg X =>
      obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := hph
      refine ⟨r1, ?_, r3, r4, r5, ?_, ?_⟩
      · intro h
        rcases List.mem_append.1 h with h | h
        · exact r2 h
        · simp at h; exact hne h
      · intro hCS i hi
        rcases hpos i _ hi with ⟨-, h⟩ | ⟨-, ⟨c, hc'⟩, -⟩
        · exact r6 hCS i h
        · cases hc'
      · intro i i' hi hi' hn hn'
        rcases hpos i _ hi with ⟨-, h⟩ | ⟨-, ⟨c, hc'⟩, -⟩
        · rcases hpos i' _ hi' with ⟨-, h'⟩ | ⟨-, ⟨c', hc''⟩, -⟩
          · exact r7 i i' h h' hn hn'
          · cases hc''
        · cases hc'
    | closedRun X =>
      obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hph
      refine ⟨c1, ?_, c3, c4, c5, c6, ?_⟩
      · intro h
        rcases List.mem_append.1 h with h | h
        · exact c2 h
        · simp at h; exact hne h
      · intro i hi
        rcases hpos i _ hi with ⟨-, h⟩ | ⟨-, ⟨c, hc'⟩, -⟩
        · exact c7 i h
        · cases hc'
    | orphan =>
      obtain ⟨o1, o2, o3⟩ := hph
      refine ⟨o1, ?_, o3⟩
      intro h
      rcases List.mem_append.1 h with h | h
      · exact o2 h
      · simp at h; exact hne h
  · refine ⟨hM, List.mem_append_right _ (by simp), hCL, fun i hi => ?_, fun hs hh => ?_⟩
    · rcases hc with ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ | ⟨hl, -, hp, h⟩
      · rw [h] at hi; cases hi
      · rw [h] at hi; cases hi
      · rw [h] at hi; cases hi
        exact ⟨hp, by show (S.l ++ [ws]).head? = _; rw [hl]; rfl⟩
    · rcases hc with ⟨hl, -, -, -⟩ | ⟨-, -, hp, -⟩ | ⟨-, -, -, h⟩
      · exfalso
        have : (S.l ++ [ws]).head? = S.l.head? := by
          cases h : S.l with
          | nil => exact absurd h hl
          | cons a t => rfl
        have hh' : S.l.head? = some ws := by rw [← this]; exact hh
        exact hwsl (List.mem_of_mem_head? hh')
      · exact hp
      · rw [h] at hs; cases hs




/-- The model after a created response `m` (id `X`) answering the pending create at `i`, whose
substream `h` (the head of `resuming`, `null` if it was closed) is registered (`reg`) or not. -/
def RunSt.answer (S : RunSt) (m : WatchRespM) (i : Nat) (X : w64) (h : Loc) (reg : Bool) : RunSt :=
  { S with Dm := S.Dm ++ [m], ansd := S.ansd ++ [i],
           regs := if m.canceled then S.regs else S.regs ++ [X], pend := none,
           M := if reg then GMap.insert X h S.M else S.M,
           l := if h = null then S.l else S.l.set 0 null }

/-- A head entry, set to `null`, is gone (non-null entries distinct). -/
theorem not_mem_set0 {l : List Loc} {h : Loc} (hh : l.head? = some h) (hn : h ≠ null)
    (hnd : (l.filter (fun x => decide (x ≠ null))).Nodup) : h ∉ l.set 0 null := by
  cases l with
  | nil => simp at hh
  | cons x xs =>
    simp at hh; subst hh
    simp only [List.set_cons_zero, List.mem_cons]
    rintro (e | e)
    · exact hn e
    · rw [List.filter_cons, if_pos (by simpa using hn)] at hnd
      exact (List.nodup_cons.1 hnd).1 (List.mem_filter.2 ⟨e, by simpa using hn⟩)

theorem mem_set0 {l : List Loc} {x h : Loc} (hh : l.head? = some h) (hx : x ≠ h) (hm : x ∈ l) :
    x ∈ l.set 0 null := by
  cases l with
  | nil => simp at hm
  | cons y ys =>
    simp at hh; subst hh
    simp only [List.set_cons_zero, List.mem_cons] at hm ⊢
    rcases hm with e | e
    · exact absurd e hx
    · exact Or.inr e

theorem mem_of_set0 {l : List Loc} {x : Loc} (hm : x ∈ l.set 0 null) (hx : x ≠ null) : x ∈ l := by
  cases l with
  | nil => simp at hm
  | cons y ys =>
    simp only [List.set_cons_zero, List.mem_cons] at hm ⊢
    rcases hm with e | e
    · exact absurd e hx
    · exact Or.inr e

theorem answer_ok {S : RunSt} {U : GMap Loc Unit} {m : WatchRespM} {i : Nat} {X : w64} {h : Loc}
    {reg : Bool} (hg : gOk S U) (hp : S.pend = some i) (hhead : S.l.head? = some h)
    (hsrc : m.src = none) (hcr : m.created = true) (hid : m.watchId = X)
    (hX : m.canceled = false → X ∉ S.regs) (hMX : reg = true → S.M !! X = none)
    (hreg : reg = true → h ≠ null ∧ X ≠ W64 (-1) ∧ m.canceled = false)
    (hph : h ≠ null → phOk S h (.queued (some i))) :
    gOk (S.answer m i X h reg) U ∧
      (∀ ws ph, ws ≠ h → U !! ws = some () → phOk S ws ph → phOk (S.answer m i X h reg) ws ph) ∧
      (h ≠ null → phOk (S.answer m i X h reg) h (if reg then .reg X else .orphan)) := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13⟩ := hg
  obtain ⟨hi1, ⟨c, hic⟩, hl⟩ := g10 i hp
  have hilen : i < S.L.length := (List.getElem?_eq_some_iff.1 hic).1
  -- the new `substreams`
  have hM1 : ∀ Y w, (S.answer m i X h reg).M !! Y = some w → S.M !! Y = some w ∨ (reg = true ∧ Y = X ∧ w = h) := by
    intro Y w hY
    unfold RunSt.answer at hY; simp only at hY
    split at hY
    · rename_i hr
      by_cases e : X = Y
      · subst e; rw [GMap.lookup_insert] at hY; cases hY; exact Or.inr ⟨hr, rfl, rfl⟩
      · rw [GMap.lookup_insert_ne _ _ e] at hY; exact Or.inl hY
    · exact Or.inl hY
  have hM2 : ∀ Y w, S.M !! Y = some w → (S.answer m i X h reg).M !! Y = some w := by
    intro Y w hY
    unfold RunSt.answer; simp only
    split
    · rename_i hr
      have : X ≠ Y := fun e => by subst e; rw [hMX hr] at hY; cases hY
      rw [GMap.lookup_insert_ne _ _ this]; exact hY
    · exact hY
  have hhn : h ≠ null → h ∈ S.l := fun hn => List.mem_of_mem_head? hhead
  have hl1 : ∀ x, x ≠ null → x ∈ (S.answer m i X h reg).l → x ∈ S.l := by
    intro x hx hm
    unfold RunSt.answer at hm; simp only at hm
    split at hm
    · exact hm
    · exact mem_of_set0 hm hx
  have hl2 : ∀ x, x ≠ h → x ∈ S.l → x ∈ (S.answer m i X h reg).l := by
    intro x hx hm
    unfold RunSt.answer; simp only
    split
    · exact hm
    · exact mem_set0 hhead hx hm
  have hhl : h ≠ null → h ∉ (S.answer m i X h reg).l := by
    intro hn
    unfold RunSt.answer; simp only [if_neg hn]
    exact not_mem_set0 hhead hn g4
  -- regs grow
  have hregs : ∀ Y, Y ∈ S.regs → Y ∈ (S.answer m i X h reg).regs := by
    intro Y hY; unfold RunSt.answer; simp only; split
    · exact hY
    · exact List.mem_append_left _ hY
  have hans : ∀ j, j ∈ S.ansd → j ∈ (S.answer m i X h reg).ansd := fun j hj =>
    List.mem_append_left _ hj
  have hlive : ∀ Y, Y ∈ S.regs → ¬ idLive S.Dm Y → ¬ idLive (S.answer m i X h reg).Dm Y := by
    intro Y hY hn
    show ¬ idLive (S.Dm ++ [m]) Y
    rw [idLive_snoc]
    split
    · rename_i hc
      rw [hcr]
      cases hca : m.canceled
      · exfalso; rw [hid] at hc; rw [← hc.2] at hY; exact hX hca hY
      · simp
    · exact hn
  refine ⟨⟨?_, ?_, ?_, ?_, g5, g6, g7, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro Y w hY
    rcases hM1 Y w hY with h1 | ⟨hr, -, e⟩
    · exact g1 Y w h1
    · subst e; exact g3 _ (hhn (hreg hr).1) (hreg hr).1
  · intro Y Z w hY hZ
    rcases hM1 Y w hY with h1 | ⟨hr, e1, e2⟩ <;> rcases hM1 Z w hZ with h2 | ⟨hr', e3, e4⟩
    · exact g2 Y Z w h1 h2
    · subst e4; exact absurd h1 ((hph (hreg hr').1).1 Y)
    · subst e2; exact absurd h2 ((hph (hreg hr).1).1 Z)
    · rw [e1, e3]
  · intro x hx hxn; exact g3 x (hl1 x hxn hx) hxn
  · unfold RunSt.answer; simp only; split
    · exact g4
    · exact g4.sublist (filter_set_null_sublist S.l 0)
  · intro j c' hj
    rcases g8 j c' hj with h1 | h1
    · exact Or.inl (hans j h1)
    · rw [hp] at h1; cases h1; exact Or.inl (List.mem_append_right _ (by simp))
  · intro j id hj; exact hregs id (g9 j id hj)
  · intro j hj; cases hj
  · intro j hj
    rcases List.mem_append.1 hj with h1 | h1
    · exact g11 j h1
    · simp at h1; subst h1; exact hilen
  · intro j m' ρ hj hs
    show ρ.id ≠ W64 (-1) ∧ idLive ((S.Dm ++ [m]).take j) ρ.id
    rcases getElem?_snoc_cases hj with ⟨hjl, hj'⟩ | ⟨-, rfl⟩
    · rw [List.take_append_of_le_length (by omega)]; exact g12 j m' ρ hj' hs
    · rw [hsrc] at hs; cases hs
  · intro m' hm hs hc hca
    rcases List.mem_append.1 hm with h1 | h1
    · exact hregs _ (g13 m' h1 hs hc hca)
    · simp at h1; subst h1
      show m'.watchId ∈ (if m'.canceled then S.regs else S.regs ++ [X])
      rw [hca, hid]; simp
  · intro ws ph hne hU hph'
    have hwn : ws ≠ null := fun e => by rw [e, g6] at hU; cases hU
    cases ph with
    | queued si =>
      obtain ⟨q1, q2, q3, q4, q5⟩ := hph'
      refine ⟨fun Y hY => ?_, hl2 ws hne q2, q3, fun j hj => ?_, fun _ _ => rfl⟩
      · rcases hM1 Y ws hY with h1 | ⟨-, -, e⟩
        · exact q1 Y h1
        · exact hne e
      · obtain ⟨-, h2⟩ := q4 j hj
        rw [hhead] at h2; cases h2; exact absurd rfl hne
    | reg Y =>
      obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := hph'
      exact ⟨hM2 Y ws r1, fun hm => r2 (hl1 ws hwn hm), r3, hregs Y r4, r5,
        fun hCS j hj => hans j (r6 hCS j hj),
        fun j j' hj hj' hn hn' => r7 j j' hj hj' (fun e => hn (hans j e)) (fun e => hn' (hans j' e))⟩
    | closedRun Y =>
      obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hph'
      exact ⟨hM2 Y ws c1, fun hm => c2 (hl1 ws hwn hm), c3, hregs Y c4, c5, hlive Y c4 c6,
        fun j hj => hans j (c7 j hj)⟩
    | orphan =>
      obtain ⟨o1, o2, o3⟩ := hph'
      refine ⟨fun Y hY => ?_, fun hm => o2 (hl1 ws hwn hm), o3⟩
      rcases hM1 Y ws hY with h1 | ⟨-, -, e⟩
      · exact o1 Y h1
      · exact hne e
  · intro hn
    obtain ⟨q1, q2, q3, -, -⟩ := hph hn
    by_cases hr : reg = true
    · rw [if_pos hr]
      obtain ⟨-, hXn, hca⟩ := hreg hr
      refine ⟨?_, hhl hn, q3, ?_, hXn, ?_, ?_⟩
      · show (if reg = true then GMap.insert X h S.M else S.M) !! X = some h
        rw [if_pos hr]; exact GMap.lookup_insert _ _ _
      · show X ∈ (if m.canceled = true then S.regs else S.regs ++ [X])
        rw [hca]; simp
      · intro _ j hj
        exact absurd (g9 j X hj) (hX hca)
      · intro j j' hj; exact absurd (g9 j X hj) (hX hca)
    · rw [if_neg hr]
      refine ⟨fun Y hY => ?_, hhl hn, q3⟩
      rcases hM1 Y h hY with h1 | ⟨hr', -, -⟩
      · exact q1 Y h1
      · exact absurd hr' hr

theorem mem_dropNull {l : List Loc} {x : Loc} (hx : x ≠ null) :
    x ∈ l.dropWhile (fun y => decide (y = null)) ↔ x ∈ l := by
  induction l with
  | nil => simp
  | cons y ys ih =>
    rw [List.dropWhile_cons]
    by_cases hy : y = null
    · simp only [hy, decide_true, ↓reduceIte, List.mem_cons]
      rw [ih]; constructor
      · exact Or.inr
      · rintro (e | e)
        · exact absurd e hx
        · exact e
    · simp [hy]

theorem dropNull_head {l : List Loc} {x : Loc} (h : (l.dropWhile (fun y => decide (y = null))).head? = some x) :
    x ≠ null := by
  induction l with
  | nil => simp at h
  | cons y ys ih =>
    rw [List.dropWhile_cons] at h
    by_cases hy : y = null
    · simp only [hy, decide_true, ↓reduceIte] at h; exact ih h
    · simp [hy] at h
      rw [← h]; exact hy

theorem dropNull_sublist (l : List Loc) : List.Sublist (l.dropWhile (fun y => decide (y = null))) l :=
  (List.dropWhile_suffix _).sublist

/-- The model after `nextResume` and, for its head, a create sent (`L'`, `pend'`) or not. -/
def RunSt.resume (S : RunSt) (L' : List WatchReqM) (pend' : Option Nat) : RunSt :=
  { S with l := S.l.dropWhile (fun y => decide (y = null)), L := L', pend := pend' }

theorem resume_ok {S : RunSt} {U : GMap Loc Unit} {L' : List WatchReqM} {pend' si : Option Nat}
    (hg : gOk S U) (hp : S.pend = none)
    (hc : (L' = S.L ∧ pend' = none ∧ si = none) ∨
      ((∃ c, L' = S.L ++ [.create c]) ∧ pend' = some S.L.length ∧ si = some S.L.length ∧
        S.l.dropWhile (fun y => decide (y = null)) ≠ [])) :
    gOk (S.resume L' pend') U ∧
      (∀ ws ph, U !! ws = some () →
        (S.l.dropWhile (fun y => decide (y = null))).head? ≠ some ws →
        phOk S ws ph → phOk (S.resume L' pend') ws ph) ∧
      (∀ h2, (S.l.dropWhile (fun y => decide (y = null))).head? = some h2 → U !! h2 = some () →
        (∀ ph, phOk S h2 ph → phOk (S.resume L' pend') h2 (.queued si))) := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13⟩ := hg
  have hpos : ∀ i r, L'[i]? = some r → (i < S.L.length ∧ S.L[i]? = some r) ∨
      (i = S.L.length ∧ (∃ c, r = .create c) ∧ pend' = some S.L.length) := by
    intro i r h
    rcases hc with ⟨rfl, -, -⟩ | ⟨⟨c, rfl⟩, hp', -, -⟩
    · left; exact ⟨(List.getElem?_eq_some_iff.1 h).1, h⟩
    · rcases getElem?_snoc_cases h with h | h
      · left; exact h
      · right; exact ⟨h.1, ⟨c, h.2⟩, hp'⟩
  have hlen : S.L.length ≤ L'.length := by
    rcases hc with ⟨rfl, -, -⟩ | ⟨⟨c, rfl⟩, -, -⟩ <;> simp
  have hl : ∀ x, x ≠ null → (x ∈ (S.resume L' pend').l ↔ x ∈ S.l) := fun x hx => mem_dropNull hx
  refine ⟨⟨g1, g2, fun x hx hxn => g3 x ((hl x hxn).1 hx) hxn, ?_, g5, g6, ?_, ?_, ?_, ?_, ?_, g12, g13⟩,
    ?_, ?_⟩
  · exact g4.sublist ((dropNull_sublist S.l).filter _)
  · intro x hx
    change x ∈ L' at hx
    obtain ⟨i, hi, hix⟩ := List.getElem_of_mem hx
    have hxi : L'[i]? = some x := by rw [List.getElem?_eq_getElem hi, hix]
    rcases hpos i x hxi with ⟨-, h⟩ | ⟨-, ⟨c, rfl⟩, -⟩
    · exact g7 x (List.mem_of_getElem? h)
    · left; exact ⟨c, rfl⟩
  · intro i c h
    rcases hpos i _ h with ⟨-, h⟩ | ⟨hi, -, hp'⟩
    · rcases g8 i c h with h' | h'
      · exact Or.inl h'
      · rw [hp] at h'; cases h'
    · right; subst hi; exact hp'
  · intro i id h
    rcases hpos i _ h with ⟨-, h⟩ | ⟨-, ⟨c, hc'⟩, -⟩
    · exact g9 i id h
    · cases hc'
  · intro i hi
    rcases hc with ⟨-, hp', -⟩ | ⟨⟨c, rfl⟩, hp', -, hne⟩
    · change pend' = some i at hi; rw [hp'] at hi; cases hi
    · change pend' = some i at hi; rw [hp'] at hi; cases hi
      refine ⟨fun h => Nat.lt_irrefl _ (g11 _ h), ⟨c, by simp [RunSt.resume]⟩, hne⟩
  · intro i hi; exact Nat.lt_of_lt_of_le (g11 i hi) hlen
  · intro ws ph hU hhd hph
    have hwn : ws ≠ null := fun e => by rw [e, g6] at hU; cases hU
    cases ph with
    | queued si' =>
      obtain ⟨q1, q2, q3, q4, q5⟩ := hph
      refine ⟨q1, (hl ws hwn).2 q2, q3, fun j hj => ?_, fun _ hh => absurd hh hhd⟩
      obtain ⟨h1, -⟩ := q4 j hj; rw [hp] at h1; cases h1
    | reg Y =>
      obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := hph
      refine ⟨r1, fun h => r2 ((hl ws hwn).1 h), r3, r4, r5, ?_, ?_⟩
      · intro hCS i hi
        rcases hpos i _ hi with ⟨-, h⟩ | ⟨-, ⟨c, hc'⟩, -⟩
        · exact r6 hCS i h
        · cases hc'
      · intro i i' hi hi' hn hn'
        rcases hpos i _ hi with ⟨-, h⟩ | ⟨-, ⟨c, hc'⟩, -⟩
        · rcases hpos i' _ hi' with ⟨-, h'⟩ | ⟨-, ⟨c', hc''⟩, -⟩
          · exact r7 i i' h h' hn hn'
          · cases hc''
        · cases hc'
    | closedRun Y =>
      obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hph
      refine ⟨c1, fun h => c2 ((hl ws hwn).1 h), c3, c4, c5, c6, ?_⟩
      intro i hi
      rcases hpos i _ hi with ⟨-, h⟩ | ⟨-, ⟨c, hc'⟩, -⟩
      · exact c7 i h
      · cases hc'
    | orphan =>
      obtain ⟨o1, o2, o3⟩ := hph
      exact ⟨o1, fun h => o2 ((hl ws hwn).1 h), o3⟩
  · intro h2 hh hU ph hph
    have hwn : h2 ≠ null := dropNull_head hh
    have hm2 : h2 ∈ S.l := (mem_dropNull hwn).1 (List.mem_of_mem_head? hh)
    cases ph with
    | queued si' =>
      obtain ⟨q1, q2, q3, -, -⟩ := hph
      refine ⟨q1, (hl h2 hwn).2 q2, q3, fun j hj => ?_, fun hs _ => ?_⟩
      · rcases hc with ⟨-, -, hs⟩ | ⟨-, hp', hs, -⟩
        · rw [hs] at hj; cases hj
        · rw [hs] at hj; cases hj; exact ⟨hp', hh⟩
      · rcases hc with ⟨-, hp', -⟩ | ⟨-, -, hs', -⟩
        · exact hp'
        · rw [hs'] at hs; cases hs
    | reg Y => exact absurd hm2 hph.2.1
    | closedRun Y => exact absurd hm2 hph.2.1
    | orphan => exact absurd hm2 hph.2.1

/-- The model after the answer `m` (at the up position `i`) to a cancel of `X`: `cancelSet`
forgets `X`; the substream registered at `X`, if any (`fw`), joins `closing`. -/
def RunSt.cancelAns (S : RunSt) (m : WatchRespM) (i : Nat) (X : w64) (fw : Option Loc) : RunSt :=
  { S with Dm := S.Dm ++ [m], ansd := S.ansd ++ [i], CS := GMap.delete X S.CS,
           CL := match fw with | some ws => GMap.insert ws () S.CL | none => S.CL }

theorem cancelAns_ok {S : RunSt} {U : GMap Loc Unit} {m : WatchRespM} {i : Nat} {X : w64}
    {fw : Option Loc} (hg : gOk S U) (hi : S.L[i]? = some (.cancel X)) (hia : i ∉ S.ansd)
    (hsrc : m.src = none) (hcr : m.created = false) (hid : m.watchId = X)
    (hfw : fw = S.M !! X) :
    gOk (S.cancelAns m i X fw) U ∧
      (∀ ws ph, U !! ws = some () → fw ≠ some ws → phOk S ws ph →
        phOk (S.cancelAns m i X fw) ws ph) ∧
      (∀ ws ph, fw = some ws → phOk S ws ph → phOk (S.cancelAns m i X fw) ws (.closedRun X)) := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13⟩ := hg
  have hans : ∀ j, j ∈ S.ansd → j ∈ (S.cancelAns m i X fw).ansd := fun j hj =>
    List.mem_append_left _ hj
  have hCL : ∀ ws, fw ≠ some ws → (S.cancelAns m i X fw).CL !! ws = S.CL !! ws := by
    intro ws hne
    unfold RunSt.cancelAns; simp only
    cases hf : fw with
    | none => rfl
    | some w =>
      have : w ≠ ws := fun e => hne (by rw [hf, e])
      exact GMap.lookup_insert_ne _ _ this
  have hlive : ∀ Y, Y ≠ X → (idLive (S.cancelAns m i X fw).Dm Y ↔ idLive S.Dm Y) := by
    intro Y hY
    show idLive (S.Dm ++ [m]) Y ↔ _
    rw [idLive_snoc, if_neg (fun h => hY (h.2.symm.trans hid))]
  refine ⟨⟨g1, g2, g3, g4, ?_, g6, g7, ?_, g9, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro ws h
    unfold RunSt.cancelAns at h; simp only at h
    cases hf : fw with
    | none => rw [hf] at h; exact g5 ws h
    | some w =>
      rw [hf] at h
      by_cases e : w = ws
      · subst e; rw [hf] at hfw; exact g1 X w hfw.symm
      · rw [GMap.lookup_insert_ne _ _ e] at h; exact g5 ws h
  · intro j c hj
    rcases g8 j c hj with h | h
    · exact Or.inl (hans j h)
    · exact Or.inr h
  · intro j hj
    obtain ⟨h1, h2, h3⟩ := g10 j hj
    refine ⟨?_, h2, h3⟩
    intro h
    rcases List.mem_append.1 h with h | h
    · exact h1 h
    · simp at h; subst h; obtain ⟨c, hc⟩ := h2; rw [hc] at hi; cases hi
  · intro j hj
    rcases List.mem_append.1 hj with h | h
    · exact g11 j h
    · simp at h; subst h; exact (List.getElem?_eq_some_iff.1 hi).1
  · intro j m' ρ hj hs
    show ρ.id ≠ W64 (-1) ∧ idLive ((S.Dm ++ [m]).take j) ρ.id
    rcases getElem?_snoc_cases hj with ⟨hjl, hj'⟩ | ⟨-, rfl⟩
    · rw [List.take_append_of_le_length (by omega)]; exact g12 j m' ρ hj' hs
    · rw [hsrc] at hs; cases hs
  · intro m' hm hs hc hca
    rcases List.mem_append.1 hm with h | h
    · exact g13 m' h hs hc hca
    · simp at h; subst h; rw [hcr] at hc; cases hc
  · intro ws ph hU hne hph
    cases ph with
    | queued si =>
      obtain ⟨q1, q2, q3, q4, q5⟩ := hph
      exact ⟨q1, q2, by rw [hCL ws hne]; exact q3, q4, q5⟩
    | reg Y =>
      obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := hph
      have hYX : Y ≠ X := fun e => by subst e; rw [← hfw] at r1; exact hne r1
      refine ⟨r1, r2, by rw [hCL ws hne]; exact r3, r4, r5, ?_, ?_⟩
      · intro hCS j hj
        unfold RunSt.cancelAns at hCS; simp only at hCS
        rw [GMap.lookup_delete_ne _ (Ne.symm hYX)] at hCS
        exact hans j (r6 hCS j hj)
      · intro j j' hj hj' hn hn'
        exact r7 j j' hj hj' (fun e => hn (hans j e)) (fun e => hn' (hans j' e))
    | closedRun Y =>
      obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hph
      have hYX : Y ≠ X := fun e => by subst e; rw [← hfw] at c1; exact hne c1
      exact ⟨c1, c2, by rw [hCL ws hne]; exact c3, c4, c5, fun h => c6 ((hlive Y hYX).1 h),
        fun j hj => hans j (c7 j hj)⟩
    | orphan =>
      obtain ⟨o1, o2, o3⟩ := hph
      exact ⟨o1, o2, by rw [hCL ws hne]; exact o3⟩
  · intro ws ph hf hph
    rw [hf] at hfw
    have hMX := hfw.symm
    cases ph with
    | queued si => exact absurd hMX (hph.1 X)
    | orphan => exact absurd hMX (hph.1 X)
    | closedRun Y =>
      have hY : Y = X := g2 Y X ws hph.1 hMX
      subst hY
      exact absurd (hph.2.2.2.2.2.2 i hi) hia
    | reg Y =>
      have hY : Y = X := g2 Y X ws hph.1 hMX
      subst hY
      obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := hph
      refine ⟨r1, r2, ?_, r4, r5, ?_, ?_⟩
      · unfold RunSt.cancelAns; simp only [hf]; exact GMap.lookup_insert _ _ _
      · show ¬ idLive (S.Dm ++ [m]) Y
        rw [idLive_snoc, if_pos ⟨hsrc, hid⟩, hcr]; simp
      · intro j hj
        by_cases e : j = i
        · subst e; exact List.mem_append_right _ (by simp)
        · exact hans j (Classical.byContradiction fun hn => e (r7 j i hj hi hn hia))

/-- The model after an mvcc response `m` of a live id. -/
def RunSt.recvMvcc (S : RunSt) (m : WatchRespM) : RunSt := { S with Dm := S.Dm ++ [m] }

theorem recvMvcc_ok {S : RunSt} {U : GMap Loc Unit} {m : WatchRespM} {ρ : mvcc.RespM}
    (hg : gOk S U) (hsrc : m.src = some ρ) (hid : ρ.id ≠ W64 (-1)) (hl : idLive S.Dm ρ.id) :
    gOk (S.recvMvcc m) U ∧ ∀ ws ph, phOk S ws ph → phOk (S.recvMvcc m) ws ph := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13⟩ := hg
  have hlive : ∀ Y, (idLive (S.recvMvcc m).Dm Y ↔ idLive S.Dm Y) := by
    intro Y
    show idLive (S.Dm ++ [m]) Y ↔ _
    rw [idLive_snoc, if_neg (fun h => by rw [hsrc] at h; cases h.1)]
  refine ⟨⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, ?_, ?_⟩, ?_⟩
  · intro j m' ρ' hj hs
    show ρ'.id ≠ W64 (-1) ∧ idLive ((S.Dm ++ [m]).take j) ρ'.id
    rcases getElem?_snoc_cases hj with ⟨hjl, hj'⟩ | ⟨hj2, hm'⟩
    · rw [List.take_append_of_le_length (by omega)]; exact g12 j m' ρ' hj' hs
    · subst hm'
      rw [hsrc] at hs; cases hs
      subst hj2
      rw [List.take_left]; exact ⟨hid, hl⟩
  · intro m' hm hs hc hca
    rcases List.mem_append.1 hm with h | h
    · exact g13 m' h hs hc hca
    · simp at h; subst h; rw [hsrc] at hs; cases hs
  · intro ws ph hph
    cases ph with
    | closedRun Y =>
      obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hph
      exact ⟨c1, c2, c3, c4, c5, fun h => c6 ((hlive Y).1 h), c7⟩
    | queued si => exact hph
    | reg Y => exact hph
    | orphan => exact hph


end client
end EtcdGrove
end Perennial
