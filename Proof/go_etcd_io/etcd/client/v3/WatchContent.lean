/-
**The content of a dispatched watch response** (the watch slice's unit W-C, 2026-10-15): from an
mvcc watch response the client's gRPC watch stream received to the contract's facts `run` hands a
substream with it (`recvElem`, `InvWatch.lean`). Lean-first, no Rocq counterpart.

The pure part:
* `findKey_applyChanges_other`: changes of other keys leave a key's record alone.
* `evsOfRevM_state`: an event of revision `x` is at `x`; a put's key-value is in the state at `x`,
  a delete's key absent from it (a revision writes each key once, `NoDupKeysPerRev`).
* `covers_inRange`: a key the registered range covers is in the request's range.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.WatchStep
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvWatchStream

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace client

open mvcc txn

/-! ## A revision's events and the state -/

/-- Changes of other keys leave a key's record alone (on a sorted state). -/
theorem findKey_applyChanges_other (r : w64) (k : GoString) :
    ∀ (cs : List Change) (s : List EtcdKv), s.Pairwise etcdKvLess → k ∉ cs.map Change.key →
      findKey k (applyChanges r s cs) = findKey k s
  | [], _, _, _ => rfl
  | c :: cs, s, hs, hk => by
    rw [applyChanges_cons]
    have hk1 : c.key ≠ k := fun h => hk (by simp [h])
    have hk2 : k ∉ cs.map Change.key := fun h => hk (List.mem_cons_of_mem _ h)
    rw [findKey_applyChanges_other r k cs _ (applyChange_sorted hs r c) hk2]
    cases c with
    | put k' v l => exact findKey_putKv_other hs r k k' v l hk1
    | del k' =>
      simp only [applyChange]
      rw [findKey_filter_ne]
      simp only [Change.key] at hk1
      simp [hk1]

/-- In a list with distinct elements, the element at `i` is not after `i`. -/
theorem nodup_not_mem_drop {α : Type} {l : List α} (hnd : l.Nodup) {i : Nat} {a : α}
    (h : l[i]? = some a) : a ∉ l.drop (i + 1) := by
  intro hm
  have hl := List.take_append_drop (i + 1) l
  rw [List.take_add_one, h] at hl
  rw [← hl] at hnd
  simp only [Option.toList_some] at hnd
  rw [List.nodup_append] at hnd
  exact hnd.2.2 a (by simp) a hm rfl

/-- The keys a list of changes puts are among its keys. -/
theorem putKeysOf_sub (cs : List Change) {k : GoString} (h : k ∈ putKeysOf cs) :
    k ∈ cs.map Change.key := by
  unfold putKeysOf at h
  rw [List.mem_filterMap] at h
  obtain ⟨c, hc, hck⟩ := h
  cases c with
  | put k' _ _ => simp only [Option.some.injEq] at hck; subst hck; exact List.mem_map_of_mem hc
  | del _ => cases hck

/-- **An event of revision `x`** (of a well-formed log whose revisions write each key once): it
is at `x`, without a previous key-value; a put's key-value is in the state at `x`; a delete's key
is absent from it. -/
theorem evsOfRevM_state (L : Log) (hwf : LogWf' L) (hlen : L.length < 2 ^ 63)
    (hnd : NoDupKeysPerRev L) (x : Nat) (hx1 : 1 ≤ x) (hx : x < L.length) (ev : EvM)
    (hev : ev ∈ evsOfRevM x (stateAt L (x - 1)) (L.getD x [])) :
    ev.kv.modRev = W64 x ∧ ev.prevKv = none ∧ (ev.del = false → ev.kv ∈ stateAt L x) ∧
      (ev.del = true → ∀ v ∈ stateAt L x, v.key ≠ ev.kv.key) := by
  have hb := stateAt_sorted L (x - 1)
  have hmod := evsOfRevM_modRev_sm x _ hb _ ev hev
  have hst : stateAt L x = applyChanges (W64 (x : Int)) (stateAt L (x - 1)) L[x] := by
    obtain ⟨j, rfl⟩ : ∃ j, x = j + 1 := ⟨x - 1, by omega⟩
    rw [stateAt_succ L j hx, show j + 1 - 1 = j by omega]
  have hgd : L.getD x [] = L[x] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hx]; rfl
  rw [hgd] at hev
  have hndx : (L[x].map Change.key).Nodup := hnd _ (List.getElem_mem hx)
  unfold evsOfRevM at hev
  rw [List.mem_filterMap] at hev
  obtain ⟨i, -, hi⟩ := hev
  cases hk : changeKv (W64 (x : Int)) (stateAt L (x - 1)) L[x] i with
  | none => rw [hk] at hi; cases hi
  | some kv =>
    rw [hk] at hi
    simp only [Option.map_some, Option.some.injEq] at hi
    subst hi
    refine ⟨hmod, by unfold evOfKv; split <;> rfl, ?_⟩
    have hsplit : L[x] = L[x].take (i + 1) ++ L[x].drop (i + 1) := (List.take_append_drop _ _).symm
    rcases changeKv_cases _ _ hb _ i kv hk with ⟨k, hci, rfl⟩ | ⟨k, v, l, hci, hkm, hkc⟩
    · -- a delete
      have hkd : k ∉ (L[x].drop (i + 1)).map Change.key := by
        rw [List.map_drop]
        exact nodup_not_mem_drop hndx (by rw [List.getElem?_map, hci]; rfl)
      have hev' : evOfKv x (zeroKv k) = ⟨true, { zeroKv k with modRev := W64 x }, none⟩ := by
        unfold evOfKv; simp [zeroKv]
      rw [hev']
      refine ⟨fun h => by simp at h, fun _ => ?_⟩
      simp only [zeroKv]
      rw [hst, hsplit, applyChanges_append, List.take_add_one, hci, Option.toList_some,
        applyChanges_append_singleton]
      refine absent_applyChanges _ _ ?_ (fun h => hkd (putKeysOf_sub _ h))
      intro w hw
      exact (mem_applyChange_del hw).2
    · -- a put
      have hkd : k ∉ (L[x].drop (i + 1)).map Change.key := by
        rw [List.map_drop]
        exact nodup_not_mem_drop hndx (by rw [List.getElem?_map, hci]; rfl)
      have hcr : kv.createRev ≠ W64 0 := by
        rw [hkc]
        cases hf : findKey k (applyChanges (W64 (x : Int)) (stateAt L (x - 1)) (L[x].take i)) with
        | none =>
          simp only [Option.map_none, Option.getD_none]
          intro h
          have : sint.Z (W64 (x : Int)) = sint.Z (W64 0) := by rw [h]
          have h1 : sint.Z (W64 (x : Int)) = x := by word
          rw [h1] at this; simp at this; omega
        | some w =>
          simp only [Option.map_some, Option.getD_some]
          have hw : w ∈ applyChanges (W64 (x : Int)) (stateAt L (x - 1)) (L[x].take i) := by
            unfold findKey at hf; exact List.mem_of_find?_eq_some hf
          by_cases hwr : w.createRev = W64 (x : Int)
          · rw [hwr]; intro h
            have : sint.Z (W64 (x : Int)) = sint.Z (W64 0) := by rw [h]
            have h1 : sint.Z (W64 (x : Int)) = x := by word
            rw [h1] at this; simp at this; omega
          · obtain ⟨u, hu, -, huc⟩ := mem_applyChanges_createRev _ _ w hw hwr
            have hne : L ≠ [] := by intro h; subst h; simp at hx
            have hpos := stateAt_createRev_pos L (hwf.1 hne) hlen (x - 1) (by omega) u hu
            rw [← huc]
            intro h; rw [h] at hpos; simp at hpos
      have hev' : evOfKv x kv = ⟨false, kv, none⟩ := by
        unfold evOfKv; rw [if_neg hcr]
      rw [hev']
      refine ⟨fun _ => ?_, fun h => by simp at h⟩
      simp only
      have hf : findKey k (applyChanges (W64 (x : Int)) (stateAt L (x - 1)) (L[x].take (i + 1))) =
          some kv := by
        unfold changeKv at hk; rw [hci] at hk; exact hk
      have hf2 : findKey k (stateAt L x) = some kv := by
        rw [hst, hsplit, applyChanges_append,
          findKey_applyChanges_other _ k _ _ (applyChanges_sorted _ _ hb) hkd, hf]
      unfold findKey at hf2
      exact List.mem_of_find?_eq_some hf2


/-! ## The order of a watcher's events -/

theorem pairwise_of_const {α : Type} (g : α → Int) (c : Int) :
    ∀ l : List α, (∀ x ∈ l, g x = c) → l.Pairwise (fun a b => g a ≤ g b)
  | [], _ => List.Pairwise.nil
  | x :: xs, h => by
    refine List.Pairwise.cons (fun y hy => ?_) (pairwise_of_const g c xs (fun y hy => h y (by simp [hy])))
    rw [h x (by simp), h y (by simp [hy])]; exact Int.le_refl _

/-- **A watcher's events are in revision order** (of a log shorter than `2 ^ 63`). -/
theorem watchEvents_sorted (L : Log) (hlen : L.length < 2 ^ 63) (r : WatchRange) (a b : Nat) :
    (watchEvents L r a b).Pairwise (fun e f => sint.Z e.kv.modRev ≤ sint.Z f.kv.modRev) := by
  unfold watchEvents
  refine List.Pairwise.filter _ ?_
  unfold logEvents
  rw [List.pairwise_flatten, List.pairwise_map]
  refine ⟨fun l hl => ?_, ?_⟩
  · obtain ⟨m, -, rfl⟩ := List.mem_map.1 hl
    exact pairwise_of_const (fun e : EvM => sint.Z e.kv.modRev) (sint.Z (W64 (m : Int))) _
      (fun x hx => by rw [evsOfRevM_modRev_sm m _ (stateAt_sorted _ _) _ x hx])
  · refine List.Pairwise.imp_of_mem ?_ (List.pairwise_lt_range' (s := a) (n := b - a))
    intro m1 m2 _ _ hlt x hx y hy
    have hy2 : m2 < L.length := by
      refine Classical.byContradiction fun hc => ?_
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hy
      simp [evsOfRevM_nil] at hy
    rw [evsOfRevM_modRev_sm m1 _ (stateAt_sorted _ _) _ x hx,
      evsOfRevM_modRev_sm m2 _ (stateAt_sorted _ _) _ y hy]
    have h1 : sint.Z (W64 (m1 : Int)) = m1 := by word
    have h2 : sint.Z (W64 (m2 : Int)) = m2 := by word
    omega

/-- **The cut of a watcher's events, one response on** (pure): the events `E` dispatched so far
(none, or a watcher's events of the revisions `[lo, d1)` of a log `L1`), then the response's
events `evs` (not none), are the watcher's events of `[lo, d2)` of a log `L2` comparable with
`L1`: then `d2` is within `L2`, and `evs` are the events of `[a, d2)` for an `a ≥ lo` above
every revision of `E`. -/
theorem cut_step (L1 L2 : Log) (hc : L1 <+: L2 ∨ L2 <+: L1) (r : WatchRange) (lo d1 d2 : Nat)
    (E evs : List EvM)
    (h1 : E = [] ∨ (E = watchEvents L1 r lo d1 ∧ lo ≤ d1 ∧ d1 ≤ L1.length))
    (h2 : E ++ evs = watchEvents L2 r lo d2) (h2l : d2 ≤ L2.length ∨ d2 ≤ lo) (hne : evs ≠ []) :
    d2 ≤ L2.length ∧ lo ≤ d2 ∧ ∃ a, lo ≤ a ∧ (∀ e ∈ E, ∃ j, j < a ∧ e.kv.modRev = W64 (j : Int)) ∧
      evs = watchEvents L2 r a d2 := by
  have hlo : lo < d2 := by
    refine Classical.byContradiction fun hc' => ?_
    rw [watchEvents_empty L2 r (show d2 ≤ lo by omega)] at h2
    exact hne (List.append_eq_nil_iff.1 h2).2
  have hd2 : d2 ≤ L2.length := h2l.resolve_right (by omega)
  refine ⟨hd2, by omega, ?_⟩
  rcases h1 with rfl | ⟨rfl, hl1, hd1⟩
  · exact ⟨lo, Nat.le_refl _, fun e he => by simp at he, by simpa using h2⟩
  · obtain ⟨L, p1, p2, -⟩ := v3rpc.longer_log hc
    have e1 := watchEvents_prefix p1 r (lo := lo) hd1
    have e2 := watchEvents_prefix p2 r (lo := lo) hd2
    rw [e1, e2] at h2
    rcases v3rpc.watchEvents_mid L r lo d1 d2 evs hl1 h2 with h | ⟨hle, hev⟩
    · exact absurd h hne
    · refine ⟨d1, hl1, fun e he => ?_, ?_⟩
      · obtain ⟨j, -, hj, hm⟩ := v3rpc.watchEvents_mem_rev L1 r lo d1 e he
        exact ⟨j, hj, hm⟩
      · rw [hev, watchEvents_prefix p2 r (lo := d1) hd2]

/-! ## The range -/

/-- **A key the registered range covers is in the request's range**: the range registered for a
create request (`createRangeOk`) of a non-empty key covers only keys of the request's range. -/
theorem covers_inRange (c : v3rpc.CreateReqM) (id : w64) (r : WatchRange) (k : GoString)
    (hc : v3rpc.createRangeOk c id r) (hkey : c.key ≠ []) (hcov : r.covers k = true) :
    inRange c.key c.rangeEnd k = true := by
  obtain ⟨hk, -, -, he⟩ := hc
  rw [if_neg hkey] at hk
  unfold WatchRange.covers at hcov
  unfold inRange
  by_cases h0 : c.rangeEnd = []
  · rw [if_pos h0] at he
    rw [he] at hcov
    simp only [decide_eq_true_eq] at hcov
    simp [h0, hcov, hk]
  · rw [if_neg h0] at he
    by_cases h1 : c.rangeEnd = [W8 0]
    · rw [if_pos h1] at he
      simp only [if_neg h0, if_pos h1, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
      rcases he with he | he
      · rw [he] at hcov
        simp only [decide_eq_true_eq] at hcov
        obtain ⟨hge, hlt⟩ := hcov
        rw [adt.affCmp_nonneg_iff, hk] at hge
        intro hl
        apply hge
        refine ⟨?_, Or.inr hl⟩
        intro hk0
        rw [adt.affCmp_neg_iff] at hlt
        exact hlt.1 hk0
      · rw [he] at hcov
        simp only [decide_eq_true_eq] at hcov
        rw [hcov, ← hk]
        exact adt.strLt_irrefl _
    · rw [if_neg h1] at he
      rw [he] at hcov
      simp only [decide_eq_true_eq] at hcov
      obtain ⟨hge, hlt⟩ := hcov
      rw [adt.affCmp_nonneg_iff, hk] at hge
      rw [adt.affCmp_neg_iff] at hlt
      simp only [if_neg h0, if_neg h1, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
        decide_eq_false_iff_not, decide_eq_true_eq]
      refine ⟨fun hl => hge ⟨hlt.1, Or.inr hl⟩, ?_⟩
      rcases hlt.2 with h | h
      · exact absurd h h0
      · exact h

end client
end EtcdGrove
end Perennial
