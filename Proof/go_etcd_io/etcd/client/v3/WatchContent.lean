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
public import Proof.go_etcd_io.etcd.client.v3.WatchClientModel
public import Proof.go_etcd_io.etcd.client.v3.WatchBridges

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

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
      rw [he] at hcov
      simp only [decide_eq_true_eq] at hcov
      obtain ⟨hge, hlt⟩ := hcov
      rw [adt.affCmp_nonneg_iff, hk] at hge
      intro hl
      apply hge
      refine ⟨?_, Or.inr hl⟩
      intro hk0
      rw [adt.affCmp_neg_iff] at hlt
      exact hlt.1 hk0
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

/-! ## The dispatch's content (Iris) -/

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3

section content
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- A key-value, read-only, as the contract reads it. -/
theorem kvPtrFixed_facts (p : Loc) (kv : EtcdKv) :
    mvcc.kvPtrFixed (GF := GF) p kv ⊢
      kvValAt p kv ∗ delKvAt p ∗
      ∃ ks : GoSlice, structFieldRef mvccpb.KeyValue go!"Key" p ↦□ ks ∗ ks ↦*□ kv.key ∗
        structFieldRef mvccpb.KeyValue go!"ModRevision" p ↦□ kv.modRev := by
  iintro H
  unfold mvcc.kvPtrFixed
  icases H with ⟨%ks, %vs, %st, %uf, %sc, #Hks, #Hvs, #Hp⟩
  iStructNamed Hp
  unfold kvValAt delKvAt
  isplitl []
  · iexists ks, vs
    iframe #
  isplitl []
  · iexists vs, kv.value, kv.lease
    iframe #
  iexists ks
  iframe #

/-- An mvcc event's fields but `PrevKv`, read-only, as the contract reads them (k8s 7f-3b: the
send loop may have written `PrevKv`). -/
theorem evIs_facts (e : Loc) (ev : mvcc.EvM) :
    mvcc.evRd (GF := GF) e ev ⊢ ∃ kv : Loc, eventAt e (evModelOf ev kv) ∗ mvcc.kvPtrFixed kv ev.kv := by
  iintro #H
  unfold mvcc.evRd
  icases H with ⟨%p, %st, %uf, %sc, %Hn, -, #Type', #Kv, -, -, #Hkv⟩
  ihave ⟨-, -, %ks, #Hk, #Hks, #Hmr⟩ := kvPtrFixed_facts p ev.kv $$ Hkv
  iexists p
  iframe Hkv
  unfold eventAt evModelOf
  iexists ks
  iframe #

/-- mvcc events, as their fields but `PrevKv`. -/
theorem evIss_evRds (ps : List Loc) (evs : List mvcc.EvM) :
    ([∗list] y ∈ ps.zip evs, mvcc.evIs (GF := GF) y.1 y.2) ⊢
      [∗list] y ∈ ps.zip evs, mvcc.evRd y.1 y.2 :=
  BigSepL.bigSepL_mono fun _ => mvcc.evIs_evRd _ _

/-- **The events of a sent response, as mvcc's** (k8s 7f-3b): events that agree with `evs0` but for
their previous key-values (`v3rpc.evsSentOk_rd`) read as `evs0`'s fields but `PrevKv`. -/
theorem evIs_evRd_transfer : ∀ (ps : List Loc) (evs evs0 : List mvcc.EvM),
    (□ ∀ (k : Nat) (ev ev0 : mvcc.EvM), ⌜evs[k]? = some ev⌝ -∗ ⌜evs0[k]? = some ev0⌝ -∗
        ⌜ev.del = ev0.del ∧ ev.kv = ev0.kv⌝) ∗ ⌜evs.length = evs0.length⌝ ∗
      ([∗list] y ∈ ps.zip evs, mvcc.evIs (GF := GF) y.1 y.2) ⊢
      [∗list] y ∈ ps.zip evs0, mvcc.evRd y.1 y.2
  | [], _, _ => by iintro -; simp only [List.zip_nil_left]; iapply BigSepL.bigSepL_nil.2; iempintro
  | _ :: _, [], [] => by iintro -; simp only [List.zip_nil_right]; iapply BigSepL.bigSepL_nil.2; iempintro
  | _ :: _, [], _ :: _ => by iintro ⟨-, %h, -⟩; simp at h
  | _ :: _, _ :: _, [] => by iintro ⟨-, %h, -⟩; simp at h
  | p :: ps, ev :: evs, ev0 :: evs0 => by
    iintro ⟨#H, %hl, Hl⟩
    simp only [List.zip_cons_cons]
    icases (BigSepL.bigSepL_cons).1 $$ Hl with ⟨#Hev, Hl⟩
    ihave %h0 := H $$ %0 %ev %ev0 %rfl %rfl
    iapply (BigSepL.bigSepL_cons).2
    isplitr
    · ihave #Hr := mvcc.evIs_evRd p ev $$ Hev
      have hrd : mvcc.evRd (GF := GF) p ev ⊢ mvcc.evRd p ev0 := by
        unfold mvcc.evRd mvcc.evType; rw [h0.1, h0.2]
      iapply hrd $$ Hr
    iapply evIs_evRd_transfer ps evs evs0
    iframe Hl
    isplitr
    · iintro !> %k %e %e0 %h %h'
      iapply H $$ %(k + 1) %e %e0 %h %h'
    ipureintro; simpa using hl

theorem evs_facts_aux : ∀ (ps : List Loc) (evs : List mvcc.EvM), ps.length = evs.length →
    ([∗list] x ∈ ps.zip evs, mvcc.evRd (GF := GF) x.1 x.2) ⊢
      ∃ kvs : List Loc, ⌜kvs.length = evs.length⌝ ∗
        □ (∀ (k : Nat) (p : Loc) (ev : mvcc.EvM) (kv : Loc), ⌜ps[k]? = some p⌝ → ⌜evs[k]? = some ev⌝ →
          ⌜kvs[k]? = some kv⌝ → eventAt p (evModelOf ev kv) ∗ mvcc.kvPtrFixed kv ev.kv)
  | [], [], _ => by
    iintro -
    iexists []
    isplitr
    · ipureintro; rfl
    imodintro
    iintro %k %p %ev %kv %h
    simp at h
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | p :: ps, ev :: evs, h => by
    iintro H
    simp only [List.zip_cons_cons]
    icases (BigSepL.bigSepL_cons).1 $$ H with ⟨#Hev, H⟩
    ihave ⟨%kvs, %Hl, #Hr⟩ := evs_facts_aux ps evs (by simpa using h) $$ H
    ihave ⟨%kv, #Ha, #Hk⟩ := evIs_facts p ev $$ Hev
    iexists kv :: kvs
    isplitr
    · ipureintro; simp [Hl]
    imodintro
    iintro %k %p' %ev' %kv' %hp %he %hk
    cases k with
    | zero =>
      simp at hp he hk
      subst hp he hk
      iframe #
    | succ k =>
      simp at hp he hk
      iapply Hr $$ %k %p' %ev' %kv' %hp %he %hk

/-- **The events of a received response**, as the contract reads them. -/
theorem evs_eventsAt (sl : GoSlice) (ps : List Loc) (evs : List mvcc.EvM)
    (h : ps.length = evs.length) :
    sl ↦*□ ps ∗ ([∗list] x ∈ ps.zip evs, mvcc.evRd (GF := GF) x.1 x.2) ⊢
      ∃ kvs : List Loc, ⌜kvs.length = evs.length⌝ ∗
        eventsAt sl (List.zipWith evModelOf evs kvs) ∗
        □ (∀ (k : Nat) (ev : mvcc.EvM) (kv : Loc), ⌜evs[k]? = some ev⌝ → ⌜kvs[k]? = some kv⌝ →
          mvcc.kvPtrFixed kv ev.kv) := by
  iintro ⟨#Hsl, H⟩
  ihave ⟨%kvs, %Hl, #Hr⟩ := evs_facts_aux ps evs h $$ H
  iexists kvs
  isplitr
  · ipureintro; exact Hl
  isplitl
  · unfold eventsAt
    iexists ps
    iframe Hsl
    isplitr
    · ipureintro; simp [h, Hl]
    imodintro
    iintro %k %p %e %hp %he
    rw [List.getElem?_zipWith] at he
    cases hev : evs[k]? with
    | none => rw [hev] at he; simp at he
    | some ev =>
      cases hkv : kvs[k]? with
      | none => rw [hev, hkv] at he; simp at he
      | some kv =>
        rw [hev, hkv] at he
        simp at he; subst he
        ihave ⟨H1, -⟩ := Hr $$ %k %p %ev %kv %hp %hev %hkv
        iexact H1
  imodintro
  iintro %k %ev %kv %he %hk
  have : ∃ p, ps[k]? = some p := by
    have hk' : k < ps.length := by
      have := (List.getElem?_eq_some_iff.1 he).1; omega
    exact ⟨_, List.getElem?_eq_getElem hk'⟩
  obtain ⟨p, hp⟩ := this
  ihave ⟨-, H2⟩ := Hr $$ %k %p %ev %kv %hp %he %hk
  iexact H2

/-! ## The events' previous key-values (k8s 7f-3c) -/

/-- An event of a log's range events is at a revision of the log with changes, without a previous
key-value. -/
theorem rangeLogEvents_mem (L : mvcc.Log) (o : OpFull) (lo hi : Nat) (ev : mvcc.EvM)
    (h : ev ∈ rangeLogEvents L o lo hi) :
    ∃ j, lo ≤ j ∧ j < hi ∧ j < L.length ∧ ev.kv.modRev = W64 (j : Int) ∧ ev.prevKv = none ∧
      L.getD j [] ≠ [] := by
  unfold rangeLogEvents at h
  obtain ⟨j, h1, h2, hj⟩ := (mem_logEvents L lo hi ev).1 (List.mem_filter.1 h).1
  have hne : L.getD j [] ≠ [] := by
    intro he; rw [he, evsOfRevM_nil] at hj; simp at hj
  have hjl : j < L.length := by
    refine Classical.byContradiction fun hc => hne ?_
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
  refine ⟨j, h1, h2, hjl, evsOfRevM_modRev_sm j _ (stateAt_sorted _ _) _ ev hj, ?_, hne⟩
  unfold evsOfRevM at hj
  obtain ⟨i, -, hi⟩ := List.mem_filterMap.1 hj
  cases hk : changeKv (W64 (j : Int)) (stateAt L (j - 1)) (L.getD j []) i with
  | none => rw [hk] at hi; cases hi
  | some kv =>
    rw [hk] at hi
    simp only [Option.map_some, Option.some.injEq] at hi
    subst hi
    unfold evOfKv; split <;> rfl

theorem getD_prefix {A B : mvcc.Log} (h : A <+: B) (i : Nat) (hi : i < A.length) :
    A.getD i [] = B.getD i [] := by
  obtain ⟨t, rfl⟩ := h
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

/-- **A sent event's `PrevKv` pointer `q`, at the server's level** (persistent; k8s 7f-3c): for
mvcc's event `ev0` of the watcher `id`, the send loop sent `ev0`, or `ev0` with a previous
key-value written (`v3rpc.pkWritten`), and `q` is the sent event's (`mvcc.prevKvIs`). -/
def pkSent (r : v3rpc.WRun GF) (id : w64) (ev0 : mvcc.EvM) (q : Loc) : IProp GF :=
  iprop(∃ ev : mvcc.EvM, v3rpc.pkWritten r id ev0 ev ∗ mvcc.prevKvIs q ev.prevKv)

instance pkSent_persistent (r : v3rpc.WRun GF) (id : w64) (ev0 : mvcc.EvM) (q : Loc) :
    Persistent (pkSent (GF := GF) r id ev0 q) := by
  unfold pkSent; infer_instance

/-- **A sent event's pointer, as the client's contract reads it** (k8s 7f-3c): for mvcc's event
`ev0` of the watcher `X` at the revision `j ≥ 1` of a certified log `L` (a revision with changes),
the pointer is `prevKvLogOk` at `L`. Without `WithPrevKV` the watcher asked for none (`pkIs`
agreement with the created response's, `ctrlWatcher`): the send loop wrote none. A written one is
the key's record at `j - 1` of a certified log `L'`, comparable with `L`, so `L`'s (`stateAt` of a
prefix); `j ≠ 1`, as `L'`'s revision `1`, which is `L`'s, is empty. -/
theorem pkSent_logOk (r : v3rpc.WRun GF) (X : w64) (o : OpFull) (L : mvcc.Log) (ev0 : mvcc.EvM)
    (q : Loc) (j : Nat) (hj1 : 1 ≤ j) (hj : j < L.length) (hm : ev0.kv.modRev = W64 (j : Int))
    (hp : ev0.prevKv = none) (hne : L.getD j [] ≠ []) :
    srvWLaws r.W ∗ □ r.W.histLb L ∗ v3rpc.pkIs r.γpk X o.base.prevKV ∗ pkSent r X ev0 q ⊢
      prevKvLogOk o L ev0 q := by
  iintro ⟨#Hl, #HL, #Hpk, #Hs⟩
  iunfold pkSent at Hs
  icases Hs with ⟨%ev, #Hw, #Hq⟩
  iunfold v3rpc.pkWritten at Hw
  icases Hw with (%Heq | ⟨%kv, %L', %H, #HL', #Hpk'⟩)
  · subst Heq
    rw [hp]
    iunfold mvcc.prevKvIs at Hq
    icases Hq with %Hq
    unfold prevKvLogOk
    split
    · ileft; ipureintro; exact Hq
    · ipureintro; exact Hq
  obtain ⟨hev, hnc, h1L', hL1, hlt, hfind⟩ := H
  ihave %Hb := v3rpc.pkIs_agree r.γpk X o.base.prevKV true $$ [$Hpk $Hpk']
  ihave %Hwl := srvWLaws_model r.W L $$ [$Hl $HL]
  have hL63 := Hwl.2.1
  iunfold srvWLaws at Hl
  icases Hl with ⟨-, #Hcmp, -⟩
  ihave %Hc := Hcmp $$ %L %L' HL HL'
  have hjz : sint.Z ev0.kv.modRev = j := by rw [hm]; word
  have hjn : sint.nat ev0.kv.modRev = j := by
    show (sint.Z ev0.kv.modRev).toNat = j; rw [hjz]; simp
  -- revision `1` is empty in both
  have hj2 : 2 ≤ j := by
    refine Classical.byContradiction fun hc => hne ?_
    have hj1' : j = 1 := by omega
    subst hj1'
    rcases Hc with hc | hc
    · rw [getD_prefix hc 1 hj]; exact hL1
    · rw [← getD_prefix hc 1 h1L']; exact hL1
  have hst : mvcc.stateAt L (j - 1) = mvcc.stateAt L' (j - 1) := by
    rcases Hc with hc | hc
    · exact v3rpc.stateAt_prefix hc (by omega)
    · exact (v3rpc.stateAt_prefix hc (by omega)).symm
  rw [hev]
  iunfold mvcc.prevKvIs at Hq
  unfold prevKvLogOk
  rw [if_pos Hb]
  iright
  iexists kv
  iframe Hq
  ipureintro
  refine ⟨hnc, ?_⟩
  rw [hjn, hst, ← hjn]
  exact hfind (by omega)

/-- An mvcc event's `PrevKv` field, read-only, and its pointer the event's previous key-value. -/
theorem evIs_pk (e : Loc) (ev : mvcc.EvM) :
    mvcc.evIs (GF := GF) e ev ⊢
      ∃ q : Loc, structFieldRef mvccpb.Event go!"PrevKv" e ↦□ q ∗ mvcc.prevKvIs q ev.prevKv := by
  iintro #H
  iunfold mvcc.evIs at H
  icases H with ⟨%p, %q, %st, %uf, %sc, -, #Hev, -, #Hq⟩
  icases typedPointsto_split _ _ _ $$ Hev with Hev
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hev
  iexists q
  iframe PrevKv
  unfold mvcc.prevKvIs
  iexact Hq

/-- The slice `sl` of `*mvccpb.Event` (read-only) holds events whose `PrevKv` fields are `qs`. -/
def pkQAt (sl : GoSlice) (qs : List Loc) : IProp GF :=
  iprop(∃ ls : List Loc, sl ↦*□ ls ∗ ⌜ls.length = qs.length⌝ ∗
    □ (∀ (i : Nat) (p q : Loc), ⌜ls[i]? = some p⌝ -∗ ⌜qs[i]? = some q⌝ -∗
      structFieldRef mvccpb.Event go!"PrevKv" p ↦□ q))

instance pkQAt_persistent (sl : GoSlice) (qs : List Loc) : Persistent (pkQAt (GF := GF) sl qs) := by
  unfold pkQAt; infer_instance

/-- The pointers `qs`, as the events' with them. -/
theorem pkQAt_at (sl : GoSlice) (qs : List Loc) (es : List EvModel) (h : qs.length = es.length) :
    pkQAt (GF := GF) sl qs ⊢ eventsPkAt sl (withPk es qs) := by
  iintro #H0
  iunfold pkQAt at H0
  icases H0 with ⟨%ls, #Hsl, %Hl, #H⟩
  unfold eventsPkAt
  iexists ls
  iframe Hsl
  isplitr
  · ipureintro; rw [withPk_length es qs h]; omega
  iintro !> %i %p %e %hp %he
  rw [withPk_getElem?] at he
  cases hes : es[i]? with
  | none => rw [hes] at he; simp at he
  | some e0 =>
    cases hqs : qs[i]? with
    | none => rw [hes, hqs] at he; simp at he
    | some q =>
      rw [hes, hqs] at he
      simp only [Option.some.injEq] at he
      subst he
      iapply H $$ %i %p %q %hp %hqs

theorem evs_pk_aux : ∀ (ps : List Loc) (evs : List mvcc.EvM), ps.length = evs.length →
    ([∗list] x ∈ ps.zip evs, mvcc.evIs (GF := GF) x.1 x.2) ⊢
      ∃ qs : List Loc, ⌜qs.length = evs.length⌝ ∗
        □ (∀ (k : Nat) (p : Loc) (ev : mvcc.EvM) (q : Loc), ⌜ps[k]? = some p⌝ → ⌜evs[k]? = some ev⌝ →
          ⌜qs[k]? = some q⌝ →
          structFieldRef mvccpb.Event go!"PrevKv" p ↦□ q ∗ mvcc.prevKvIs q ev.prevKv)
  | [], [], _ => by
    iintro -
    iexists []
    isplitr
    · ipureintro; rfl
    iintro !> %k %p %ev %q %h
    simp at h
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | p :: ps, ev :: evs, h => by
    iintro H
    simp only [List.zip_cons_cons]
    icases (BigSepL.bigSepL_cons).1 $$ H with ⟨#Hev, H⟩
    ihave ⟨%qs, %Hl, #Hr⟩ := evs_pk_aux ps evs (by simpa using h) $$ H
    ihave ⟨%q, #Hf, #Hq⟩ := evIs_pk p ev $$ Hev
    iexists q :: qs
    isplitr
    · ipureintro; simp [Hl]
    iintro !> %k %p' %ev' %q' %hp %he %hq
    cases k with
    | zero =>
      simp at hp he hq
      subst hp he hq
      iframe #
    | succ k =>
      simp at hp he hq
      iapply Hr $$ %k %p' %ev' %q' %hp %he %hq

/-- **The `PrevKv` pointers of a received response** (k8s 7f-3c): the events `evs` the send loop
sent for mvcc's response `x` (`v3rpc.evsSentOk`), read through their `PrevKv` fields, give pointers
`qs`, one per event of `x`, each `pkSent`. -/
theorem evs_pkSent (r : v3rpc.WRun GF) (x : mvcc.api.WResp) (evs : List mvcc.EvM) (sl : GoSlice)
    (ps : List Loc) (h : ps.length = evs.length) :
    sl ↦*□ ps ∗ ([∗list] y ∈ ps.zip evs, mvcc.evIs (GF := GF) y.1 y.2) ∗ v3rpc.evsSentOk r x evs ⊢
      ∃ qs : List Loc, ⌜qs.length = x.evs.length⌝ ∗ pkQAt sl qs ∗
        □ (∀ (k : Nat) (ev0 : mvcc.EvM) (q : Loc), ⌜x.evs[k]? = some ev0⌝ → ⌜qs[k]? = some q⌝ →
          pkSent r x.id ev0 q) := by
  iintro ⟨#Hsl, H, #Hs⟩
  ihave ⟨%qs, %Hl, #Hr⟩ := evs_pk_aux ps evs h $$ H
  iunfold v3rpc.evsSentOk at Hs
  icases Hs with ⟨%Hsl', #Hs⟩
  iexists qs
  isplitr
  · ipureintro; omega
  isplitr
  · unfold pkQAt
    iexists ps
    iframe Hsl
    isplitr
    · ipureintro; omega
    iintro !> %i %p %q %hp %hq
    have hi : i < evs.length := by have := (List.getElem?_eq_some_iff.1 hq).1; omega
    ihave ⟨Hf, -⟩ := Hr $$ %i %p %(evs[i]) %q %hp %(List.getElem?_eq_getElem hi) %hq
    iexact Hf
  iintro !> %k %ev0 %q %h0 %hq
  have hi : k < evs.length := by have := (List.getElem?_eq_some_iff.1 hq).1; omega
  have hpi : k < ps.length := by omega
  ihave ⟨-, #Hq⟩ := Hr $$ %k %(ps[k]) %(evs[k]) %q %(List.getElem?_eq_getElem hpi)
    %(List.getElem?_eq_getElem hi) %hq
  ihave #Hw := Hs $$ %k %ev0 %(evs[k]) %h0 %(List.getElem?_eq_getElem hi)
  unfold pkSent
  iexists evs[k]
  iframe Hw Hq

/-- The events with pointers, as `eventsAt` reads them (it reads no pointer). -/
theorem eventsAt_withPk (sl : GoSlice) (es : List EvModel) (qs : List Loc)
    (h : qs.length = es.length) :
    eventsAt (GF := GF) sl es ⊢ eventsAt sl (withPk es qs) := by
  iintro #H0
  iunfold eventsAt at H0
  icases H0 with ⟨%ls, #Hsl, %Hl, #H⟩
  unfold eventsAt
  iexists ls
  iframe Hsl
  isplitr
  · ipureintro; rw [withPk_length es qs h]; exact Hl
  iintro !> %i %p %e %hp %he
  rw [withPk_getElem?] at he
  cases hes : es[i]? with
  | none => rw [hes] at he; simp at he
  | some e0 =>
    cases hqs : qs[i]? with
    | none => rw [hes, hqs] at he; simp at he
    | some q =>
      rw [hes, hqs] at he
      simp only [Option.some.injEq] at he
      subst he
      ihave #Ha := H $$ %i %p %e0 %hp %hes
      iunfold eventAt at Ha
      unfold eventAt
      iexact Ha

/-- No events, no pointers. -/
theorem eventsPkAt_nil (sl : GoSlice) : eventsAt (GF := GF) sl [] ⊢ eventsPkAt sl [] := by
  iintro #H
  iunfold eventsAt at H
  icases H with ⟨%ls, #Hsl, %Hl, -⟩
  unfold eventsPkAt
  iexists ls
  iframe Hsl
  isplitr
  · ipureintro; exact Hl
  iintro !> %i %p %e %_ %he
  simp at he

theorem keyRangeUnder_key_ne {pfx key re : GoString} (h : KeyRangeUnder pfx key re)
    (hp : pfx ≠ []) : key ≠ [] := by
  intro hk
  subst hk
  apply hp
  have hin : inRange [] re [] = true := by
    unfold inRange
    by_cases h0 : re = []
    · simp [h0]
    · by_cases h1 : re = [W8 0]
      · simp only [h0, h1, ↓reduceIte]
        simp [go.GoStringLt]
      · simp only [h0, h1, ↓reduceIte]
        obtain ⟨b, bs, rfl⟩ : ∃ b bs, re = b :: bs := by
          cases re with
          | nil => exact absurd rfl h0
          | cons b bs => exact ⟨b, bs, rfl⟩
        simp [go.GoStringLt, List.Lex.nil]
  exact List.prefix_nil.1 (h [] hin)

/-- The events received so far of the watch id `X` (strict M1: by id). -/
abbrev evsOf (Dm : List v3rpc.WatchRespM) (X : w64) : List mvcc.EvM :=
  ((v3rpc.sentEvsOf Dm X).map mvcc.api.WResp.evs).flatten

/-- **The watcher's events received for it, then the new response's** (strict M1: the received
list's, `recvEvs`, from `mvccOk`'s forwarding fact). -/
theorem evs_after (Dm : List v3rpc.WatchRespM) (X : w64) (pre : List mvcc.api.WResp)
    (x : mvcc.api.WResp)
    (hfilt : v3rpc.sentEvsOf Dm X ++ [x] =
      ((pre ++ [x]).filter (fun y => decide (y.id = X))).filter (fun y => decide (y.evs ≠ []))) :
    mvcc.api.recvEvs (pre ++ [x]) X = evsOf Dm X ++ x.evs := by
  unfold mvcc.api.recvEvs evsOf
  rw [← flatten_evs_filter, ← hfilt]
  simp

/-- **The pure core of a dispatch**: the cut one response on. -/
theorem content_cut (L L1 : mvcc.Log) (rg : mvcc.WatchRange) (lo d d1 : Nat)
    (E evs : List mvcc.EvM) (hcmp : L1 <+: L ∨ L <+: L1)
    (hflat : E ++ evs = mvcc.watchEvents L rg lo d) (hdL : d ≤ L.length ∨ d ≤ lo) (hne : evs ≠ [])
    (hcut : E = [] ∨ (E = mvcc.watchEvents L1 rg lo d1 ∧ lo ≤ d1 ∧ d1 ≤ L1.length)) :
    d ≤ L.length ∧ lo ≤ d ∧ ∃ a, lo ≤ a ∧ (∀ e ∈ E, ∃ j, j < a ∧ e.kv.modRev = W64 (j : Int)) ∧
      evs = mvcc.watchEvents L rg a d :=
  cut_step L1 L hcmp rg lo d1 d E evs hcut hflat hdL hne

theorem zipWith_evModel_rev (evs : List mvcc.EvM) (kvs : List Loc) (h : kvs.length = evs.length) :
    (List.zipWith evModelOf evs kvs).map EvModel.rev = evs.map (fun e => e.kv.modRev) := by
  induction evs generalizing kvs with
  | nil => simp
  | cons e es ih =>
    cases kvs with
    | nil => simp at h
    | cons k ks =>
      simp only [List.zipWith_cons_cons, List.map_cons]
      rw [ih ks (by simpa using h)]; rfl

theorem mem_zipWith_evModel {evs : List mvcc.EvM} {kvs : List Loc} {e : EvModel}
    (h : e ∈ List.zipWith evModelOf evs kvs) : ∃ ev ∈ evs, e.rev = ev.kv.modRev := by
  obtain ⟨i, hi, he⟩ := List.getElem_of_mem h
  rw [List.getElem_zipWith] at he
  exact ⟨_, List.getElem_mem _, by rw [← he]; rfl⟩

/-- **The content of a dispatched mvcc response** (`recvElem`'s, `run`'s default case): its events,
as the contract reads them, satisfy the contract from the dispatch cursor `hi`, and the cursor
moves to the last one's revision, the events so far still a cut of the watcher's. Strict M1: the
response `x` (the `n`-th received) of the watch id `X` registered with the range `rg` and first
revision `lo`; for one with events, its id's received events up to it the range's of `[lo, d)` of a
certified log `L` (`recvEvents`), the events so far a cut of a certified log's (`□ V.W.histLb`, in
place of mvcc's `idxSealed`), its id's responses with events sent before it, then `x`, those
received (`mvccOk`'s, `hfilt`). -/
theorem dispatch_content (V : WEnv GF) (P : WsPrm GF) (rr : w64) (srr : Bool) (hb : w64)
    (Dm : List v3rpc.WatchRespM) (m : v3rpc.WatchRespM) (n : Nat) (x : mvcc.api.WResp)
    (pre : List mvcc.api.WResp) (X : w64) (rg : mvcc.WatchRange) (lo : Nat) (hi : w64)
    (sl : GoSlice) (ps : List Loc) (hdr : w64) (L : mvcc.Log) (d : Nat)
    (hsrc : m.src = some (n, x)) (hxX : x.evs ≠ [] → x.id = X)
    (hfilt : x.evs ≠ [] → v3rpc.sentEvsOf Dm X ++ [x] =
      ((pre ++ [x]).filter (fun y => decide (y.id = X))).filter (fun y => decide (y.evs ≠ [])))
    (hrecv : x.evs ≠ [] → mvcc.api.recvEvs (pre ++ [x]) X = mvcc.watchEvents L rg lo d ∧
      d ≤ L.length)
    (hps : ps.length = x.evs.length) (hok : wsReqOk V.pfx P) (hpfx : V.pfx ≠ [])
    (hcr : v3rpc.createRangeOk (createOf P.key P.ed rr P.pn srr P.bd P.o.base.prevKV) X rg)
    (hrr : P.rev = W64 0 ∨ sint.Z P.rev ≤ sint.Z rr) (hlor : sint.Z rr ≤ (lo : Int))
    (hhb : sint.Z hb < sint.Z rr ∨ sint.Z hb < 0)
    (hhi : (evsOf Dm X = [] ∧ hi = hb) ∨
      ∃ e, (evsOf Dm X).getLast? = some e ∧ hi = e.kv.modRev)
    (r : v3rpc.WRun GF) (qs : List Loc) (hqs : qs.length = x.evs.length) :
    pkQAt sl qs ∗ □ (∀ (k : Nat) (ev0 : mvcc.EvM) (q : Loc), ⌜x.evs[k]? = some ev0⌝ →
      ⌜qs[k]? = some q⌝ → pkSent r x.id ev0 q) ∗
    srvWLaws V.W ∗ (⌜x.evs ≠ []⌝ -∗ □ V.W.histLb L) ∗
      (⌜evsOf Dm X = []⌝ ∨ ∃ (L1 : mvcc.Log) (d1 : Nat), □ V.W.histLb L1 ∗
        ⌜evsOf Dm X = mvcc.watchEvents L1 rg lo d1 ∧ lo ≤ d1 ∧ d1 ≤ L1.length⌝) ∗
      sl ↦*□ ps ∗ ([∗list] y ∈ ps.zip x.evs, mvcc.evRd (GF := GF) y.1 y.2) ⊢
    |={⊤}=> ∃ es : List EvModel, eventsAt sl es ∗ ⌜es.length = x.evs.length⌝ ∗
      ⌜dispOk P.rev hi ((es.getLast?.map EvModel.rev).getD hi) ⟨es, W64 0, false, false, hdr⟩⌝ ∗
      ⌜(evsOf (Dm ++ [m]) X = [] ∧ (es.getLast?.map EvModel.rev).getD hi = hb) ∨
        ∃ e, (evsOf (Dm ++ [m]) X).getLast? = some e ∧
          (es.getLast?.map EvModel.rev).getD hi = e.kv.modRev⌝ ∗
      (⌜evsOf (Dm ++ [m]) X = []⌝ ∨ ∃ (L1 : mvcc.Log) (d1 : Nat), □ V.W.histLb L1 ∗
        ⌜evsOf (Dm ++ [m]) X = mvcc.watchEvents L1 rg lo d1 ∧ lo ≤ d1 ∧ d1 ≤ L1.length⌝) ∗
      (∃ kvs : List Loc, ⌜es.map EvModel.erasePk = List.zipWith evModelOf x.evs kvs ∧
          kvs.length = x.evs.length⌝ ∗
        □ (∀ (k : Nat) (ev : mvcc.EvM) (kv : Loc), ⌜x.evs[k]? = some ev⌝ → ⌜kvs[k]? = some kv⌝ →
          mvcc.kvPtrFixed kv ev.kv)) ∗
      eventsPkAt sl es ∗
      □ (∀ (k : Nat) (ev0 : mvcc.EvM) (e : EvModel), ⌜x.evs[k]? = some ev0⌝ → ⌜es[k]? = some e⌝ →
        pkSent r x.id ev0 e.prevKv) := by
  iintro ⟨#Hpq, #Hpks, #Hlaws, HLw, #Hcut, #Hsl, #Hevs⟩
  ihave ⟨%kvs, %Hkvl, #Hea0, #Hkv⟩ := evs_eventsAt sl ps x.evs hps $$ [Hsl Hevs]
  · iframe #
  have hqe : qs.length = (List.zipWith evModelOf x.evs kvs).length := by simp [Hkvl, hqs]
  ihave #Hea := eventsAt_withPk sl (List.zipWith evModelOf x.evs kvs) qs hqe $$ Hea0
  ihave #Hpka := pkQAt_at sl qs (List.zipWith evModelOf x.evs kvs) hqe $$ Hpq
  ihave #Hpke : □ (∀ (k : Nat) (ev0 : mvcc.EvM) (e : EvModel), ⌜x.evs[k]? = some ev0⌝ →
      ⌜(withPk (List.zipWith evModelOf x.evs kvs) qs)[k]? = some e⌝ → pkSent r x.id ev0 e.prevKv) $$ []
  · iintro !> %k %ev0 %e %h0 %he
    rw [withPk_getElem?] at he
    cases hz : (List.zipWith evModelOf x.evs kvs)[k]? with
    | none => rw [hz] at he; simp at he
    | some e0 =>
      cases hq : qs[k]? with
      | none => rw [hz, hq] at he; simp at he
      | some q =>
        rw [hz, hq] at he
        simp only [Option.some.injEq] at he
        subst he
        iapply Hpks $$ %k %ev0 %q %h0 %hq
  have herase : (withPk (List.zipWith evModelOf x.evs kvs) qs).map EvModel.erasePk =
      List.zipWith evModelOf x.evs kvs := by
    rw [withPk_erase _ _ hqe, zipWith_evModelOf_erase]
  have hrevs : (withPk (List.zipWith evModelOf x.evs kvs) qs).map EvModel.rev =
      (List.zipWith evModelOf x.evs kvs).map EvModel.rev := withPk_revs _ _ hqe
  have hlastW : (withPk (List.zipWith evModelOf x.evs kvs) qs).getLast?.map EvModel.rev =
      (List.zipWith evModelOf x.evs kvs).getLast?.map EvModel.rev := by
    rw [← List.getLast?_map, hrevs, List.getLast?_map]
  have hmemW : ∀ e ∈ withPk (List.zipWith evModelOf x.evs kvs) qs,
      ∃ e' ∈ List.zipWith evModelOf x.evs kvs, e.rev = e'.rev := by
    intro e he
    have : e.rev ∈ (List.zipWith evModelOf x.evs kvs).map EvModel.rev := by
      rw [← hrevs]; exact List.mem_map_of_mem he
    obtain ⟨e', h1, h2⟩ := List.mem_map.1 this
    exact ⟨e', h1, h2.symm⟩
  have hsortW : EvRevSorted (List.zipWith evModelOf x.evs kvs) →
      EvRevSorted (withPk (List.zipWith evModelOf x.evs kvs) qs) := by
    unfold EvRevSorted; intro h
    have h' := (List.pairwise_map (f := EvModel.rev) (R := fun a b => sint.Z a ≤ sint.Z b)).2 h
    rw [← hrevs] at h'
    exact (List.pairwise_map (f := EvModel.rev) (R := fun a b => sint.Z a ≤ sint.Z b)).1 h'
  have hsnoc : evsOf (Dm ++ [m]) X = evsOf Dm X ++ (if x.evs ≠ [] then x.evs else []) := by
    unfold evsOf
    rw [sentEvsOf_snoc, hsrc]
    by_cases hne : x.evs ≠ []
    · simp [hxX hne, hne]
    · simp only [ne_eq, Decidable.not_not] at hne
      simp [hne]
  iexists withPk (List.zipWith evModelOf x.evs kvs) qs
  iframe Hea
  isplitr
  · ipureintro; rw [withPk_length _ _ hqe]; simp [Hkvl]
  by_cases hne : x.evs = []
  · -- no events: the cursor stands still
    imodintro
    have hes : withPk (List.zipWith evModelOf x.evs kvs) qs = [] := by
      rw [← List.length_eq_zero_iff, withPk_length _ _ hqe]; simp [hne]
    rw [hes]
    have hsn : evsOf (Dm ++ [m]) X = evsOf Dm X := by rw [hsnoc, if_neg (by simp [hne])]; simp
    rw [hsn]
    simp only [List.getLast?_nil, Option.map_none, Option.getD_none]
    isplitr
    · ipureintro; simp [dispOk, EvRevSorted]
    isplitr
    · ipureintro; exact hhi
    isplitr
    · iexact Hcut
    iframe Hpka Hpke
    iexists kvs
    iframe Hkv
    have herase' := herase
    rw [hes] at herase'
    ipureintro; exact ⟨herase', Hkvl⟩
  -- events: the certified log's
  ihave #HL := HLw $$ %hne
  obtain ⟨hflat, hdL⟩ := hrecv hne
  rw [evs_after Dm X pre x (hfilt hne)] at hflat
  have hflat' : evsOf Dm X ++ x.evs = mvcc.watchEvents L rg lo d := hflat
  ihave %HLw := srvWLaws_model V.W L $$ [$Hlaws $HL]
  imodintro
  have Hlo : sint.Z P.rev ≤ (lo : Int) := by
    rcases hrr with h | h
    · rw [h]; simp
    · omega
  -- the cut
  ihave %Hcc : ⌜d ≤ L.length ∧ lo ≤ d ∧ ∃ a, lo ≤ a ∧
      (∀ e ∈ evsOf Dm X, ∃ j, j < a ∧ e.kv.modRev = W64 (j : Int)) ∧
      x.evs = mvcc.watchEvents L rg a d⌝ $$ []
  · icases Hcut with (%HE | ⟨%L1, %d1, #HL1, %HE1⟩)
    · ipureintro
      exact content_cut L L rg lo d 0 (evsOf Dm X) x.evs (Or.inl (List.prefix_refl _)) hflat'
        (Or.inl hdL) hne (Or.inl HE)
    · ihave #Hl' := Hlaws
      iunfold srvWLaws at Hl'
      icases Hl' with ⟨-, #Hcmp, -⟩
      ihave %Hc := Hcmp $$ %L1 %L HL1 HL
      ipureintro
      exact content_cut L L1 rg lo d d1 (evsOf Dm X) x.evs Hc hflat' (Or.inl hdL) hne (Or.inr HE1)
  obtain ⟨hdd, hlod, a, hla, hEj, hevs⟩ := Hcc
  have hLlen : L.length < 2 ^ 63 := HLw.2.1
  have hmemrev : ∀ ev ∈ x.evs, ∃ j, a ≤ j ∧ j < d ∧ ev.kv.modRev = W64 (j : Int) := by
    intro ev hev; rw [hevs] at hev; exact v3rpc.watchEvents_mem_rev L rg a d ev hev
  have hsorted : EvRevSorted (List.zipWith evModelOf x.evs kvs) := by
    unfold EvRevSorted
    have h1 := watchEvents_sorted L hLlen rg a d
    rw [← hevs] at h1
    have h2 : ((List.zipWith evModelOf x.evs kvs).map EvModel.rev).Pairwise
        (fun x y => sint.Z x ≤ sint.Z y) := by
      rw [zipWith_evModel_rev _ _ Hkvl, List.pairwise_map]; exact h1
    exact (List.pairwise_map (f := EvModel.rev) (R := fun x y => sint.Z x ≤ sint.Z y)).1 h2
  have hgt : ∀ e ∈ List.zipWith evModelOf x.evs kvs, sint.Z hi < sint.Z e.rev := by
    intro e he
    obtain ⟨ev, hev, hre⟩ := mem_zipWith_evModel he
    obtain ⟨j, hj1, hj2, hj3⟩ := hmemrev ev hev
    rw [hre, hj3]
    have hjz : sint.Z (W64 (j : Int)) = j := by word
    rw [hjz]
    rcases hhi with ⟨-, rfl⟩ | ⟨e0, he0, rfl⟩
    · rcases hhb with h | h <;> omega
    · obtain ⟨j', hj'1, hj'2⟩ := hEj e0 (List.mem_of_getLast? he0)
      rw [hj'2]
      have : sint.Z (W64 (j' : Int)) = j' := by word
      rw [this]; omega
  have hlast : (List.zipWith evModelOf x.evs kvs).getLast?.map EvModel.rev =
      x.evs.getLast?.map (fun e => e.kv.modRev) := by
    rw [← List.getLast?_map, zipWith_evModel_rev _ _ Hkvl, List.getLast?_map]
  obtain ⟨elast, helast⟩ : ∃ e, x.evs.getLast? = some e := by
    cases h : x.evs.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.1 h) hne
    | some e => exact ⟨e, rfl⟩
  have hsn : evsOf (Dm ++ [m]) X = evsOf Dm X ++ x.evs := by
    rw [hsnoc, if_pos hne]
  isplitr
  · ipureintro
    refine ⟨hsortW hsorted, fun e he => ?_, rfl⟩
    obtain ⟨e', he', hee⟩ := hmemW e he
    rw [hee]
    refine ⟨hgt e' he', ?_⟩
    obtain ⟨ev, hev, hre⟩ := mem_zipWith_evModel he'
    obtain ⟨j, hj1, hj2, hj3⟩ := hmemrev ev hev
    rw [hre, hj3]
    have hjz : sint.Z (W64 (j : Int)) = j := by word
    rw [hjz]
    constructor <;> omega
  isplitr
  · ipureintro
    right
    refine ⟨elast, ?_, ?_⟩
    · rw [hsn, List.getLast?_append, helast]; rfl
    · rw [hlastW, hlast, helast]; rfl
  isplitr
  · iright
    iexists L, d
    iframe HL
    ipureintro
    exact ⟨hsn.trans hflat', hlod, hdd⟩
  iframe Hpka Hpke
  iexists kvs
  iframe Hkv
  ipureintro; exact ⟨herase, Hkvl⟩

end content


end client
end EtcdGrove
end Perennial
