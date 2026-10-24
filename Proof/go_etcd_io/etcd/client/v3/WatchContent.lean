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
        exact go.goStringLt_irrefl _
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- The client's model of an mvcc event at `ev` whose key-value is at `kv`. -/
def evModelOf (ev : mvcc.EvM) (kv : Loc) : EvModel :=
  { typ := mvcc.evType ev, key := ev.kv.key, kv := kv, rev := ev.kv.modRev }

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

/-- An mvcc event, read-only, as the contract reads it. -/
theorem evIs_facts (e : Loc) (ev : mvcc.EvM) :
    mvcc.evIs (GF := GF) e ev ⊢ ∃ kv : Loc, eventAt e (evModelOf ev kv) ∗ mvcc.kvPtrFixed kv ev.kv := by
  iintro #H
  unfold mvcc.evIs
  icases H with ⟨%p, %q, %st, %uf, %sc, %Hn, #He, #Hkv, -⟩
  iStructNamed He
  ihave ⟨-, -, %ks, #Hk, #Hks, #Hmr⟩ := kvPtrFixed_facts p ev.kv $$ Hkv
  iexists p
  iframe Hkv
  unfold eventAt evModelOf
  iexists ks
  iframe #

theorem evs_facts_aux : ∀ (ps : List Loc) (evs : List mvcc.EvM), ps.length = evs.length →
    ([∗list] x ∈ ps.zip evs, mvcc.evIs (GF := GF) x.1 x.2) ⊢
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
    sl ↦*□ ps ∗ ([∗list] x ∈ ps.zip evs, mvcc.evIs (GF := GF) x.1 x.2) ⊢
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

/-- **One event of a dispatched response satisfies the contract**: an event of the registered
range's watch events of revisions `[a, d)` of a watched log (`mvcc.evLog`: sealed and certified;
`d` within it, `a` at or above the watch's start revision), whose key-value is at `kv`; the
event's revision is reached because the log is certified (`etcdReached_of_certOk`: S4, a theorem
since unit W-M3). -/
theorem ev_ok (V : WEnv GF) (P : WsPrm GF) (rr : w64) (srr : Bool) (L2 : mvcc.Log)
    (rg : mvcc.WatchRange) (X : w64) (a d : Nat) (ev : mvcc.EvM) (kv : Loc)
    (hok : wsReqOk V.pfx P) (hpfx : V.pfx ≠ []) (hcr : v3rpc.createRangeOk (createOf P.key P.ed rr P.pn srr) X rg)
    (hmem : ev ∈ mvcc.watchEvents L2 rg a d) (hd : d ≤ L2.length) (hlo : sint.Z P.rev ≤ (a : Int))
    (hst : V.R.γ.st = V.R.E.γ) (hnd : txn.NoDupKeysPerRev L2) :
    mvcc.evLog V.R.γ.st L2 ∗ srvLogsSmall V.R ∗ mvcc.kvPtrFixed kv ev.kv ∗
      □ V.WL L2 ∗ watchLaws V ⊢
      rangeWatchEvOk (EM := V.WM) V.pfx P.o P.rev (evModelOf ev kv) := by
  iintro ⟨#Hce, #Hsm, #Hkv, #HWL, #Hlaws⟩
  ihave #Hc := mvcc.evLog_sealed _ _ $$ Hce
  ihave #Hok := mvcc.evLog_certOk _ _ $$ Hce
  ihave %Hw := v3rpc.sealed_pure _ L2 $$ Hc
  obtain ⟨hwf, hlen⟩ := Hw
  unfold mvcc.watchEvents at hmem
  obtain ⟨hlog, hcov⟩ := List.mem_filter.1 hmem
  obtain ⟨j, hj1, hj2, hev⟩ := (mvcc.mem_logEvents L2 a d ev).1 hlog
  have hjl : j < L2.length := by omega
  have hj0 : 1 ≤ j := by
    refine Classical.byContradiction fun hc => ?_
    have : j = 0 := by omega
    subst this
    have hne : L2 ≠ [] := by intro e; subst e; simp at hjl
    have h0 := hwf.1 hne
    rw [List.getD_eq_getElem?_getD, h0] at hev
    simp [mvcc.evsOfRevM_nil] at hev
  obtain ⟨hmod, -, hput, hdel⟩ := evsOfRevM_state L2 hwf hlen hnd j hj0 hjl ev hev
  have hjz : sint.Z (W64 (j : Int)) = j := by word
  -- the key is in the request's range, under the prefix
  obtain ⟨hrw, -, -, hku, hkey, hed, -, -⟩ := hok
  have hkne : (createOf P.key P.ed rr P.pn srr).key ≠ [] := by
    show P.key ≠ []; rw [hkey]; exact keyRangeUnder_key_ne hku hpfx
  have hin0 := covers_inRange (createOf P.key P.ed rr P.pn srr) X rg ev.kv.key hcr hkne (by simpa using hcov)
  have hin : inRange P.o.key P.o.base.rangeEnd ev.kv.key = true := by
    have : (createOf P.key P.ed rr P.pn srr).key = P.o.key := hkey
    have h2 : (createOf P.key P.ed rr P.pn srr).rangeEnd = P.o.base.rangeEnd := hed
    rw [this, h2] at hin0; exact hin0
  have hpk : V.pfx <+: ev.kv.key := hku _ hin
  -- the store's facts at the event's revision
  have hjr : sint.Z (W64 (j : Int)) < (L2.length : Int) := by rw [hjz]; omega
  iunfold srvLogsSmall at Hsm
  irevert Hc Hsm Hok
  rw [hst]
  iintro #Hc #Hsm #Hok
  -- (W3) the contract's model's facts, from the watched log's (`watchLaws`)
  iunfold watchLaws at Hlaws
  icases Hlaws with ⟨#Hlr, #Hls, -, -⟩
  ihave #Hreach := Hlr $$ %L2 %(W64 (j : Int)) HWL %hjr
  have hjr2 : 0 ≤ sint.Z (W64 (j : Int)) ∧ sint.Z (W64 (j : Int)) < (L2.length : Int) :=
    ⟨by rw [hjz]; omega, hjr⟩
  ihave #Hst := Hls $$ %L2 %(W64 (j : Int)) %V.pfx HWL %hjr2
  have Hwfs := v3rpc.underPfx_wf L2 (sint.Z (W64 (j : Int))).toNat V.pfx
  ihave ⟨#Hval, #Hdel, -⟩ := kvPtrFixed_facts kv ev.kv $$ Hkv
  rw [show (sint.Z (W64 (j : Int))).toNat = j by rw [hjz]; simp] at Hwfs
  irevert Hst; rw [show (sint.Z (W64 (j : Int))).toNat = j by rw [hjz]; simp]; iintro #Hst
  unfold rangeWatchEvOk evModelOf
  simp only
  rw [hmod]
  isplitr
  · ipureintro
    refine ⟨hin, by rw [hjz]; omega, by rw [hjz]; omega, ?_⟩
    unfold mvcc.evType; split <;> simp
  iframe Hreach
  isplitl []
  · iintro %ht
    have hdl : ev.del = true := by
      unfold mvcc.evType at ht; split at ht
      · assumption
      · simp at ht
    iframe Hdel
    unfold etcdAbsent
    iexists _
    iframe Hst
    ipureintro
    intro v hv
    exact hdel hdl v (txn.mem_underPfx.1 hv).1
  · iintro %ht
    have hdl : ev.del = false := by
      unfold mvcc.evType at ht; split at ht
      · simp at ht
      · simpa using ‹¬ev.del = true›
    iexists ev.kv
    iframe Hval
    isplitr
    · ipureintro; exact ⟨rfl, hmod⟩
    iexists _
    iframe Hst
    ipureintro
    exact ⟨txn.mem_underPfx.2 ⟨hput hdl, hpk⟩, Hwfs⟩

/-- The watcher's events received for it, then the new response's. -/
theorem evs_after (Dm : List v3rpc.WatchRespM) (w : Loc) (rs : List mvcc.RespM) (ρ : mvcc.RespM)
    (hfilt : v3rpc.sentEvsOf Dm w ++ [ρ] = rs.filter (fun x => decide (x.evs ≠ []))) :
    (rs.map mvcc.RespM.evs).flatten = ((v3rpc.sentEvsOf Dm w).map mvcc.RespM.evs).flatten ++ ρ.evs := by
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

/-- **A watcher with no filters**: what a client received for it, concatenated, are its range's
events of revisions `[lo, d)` of a watched log (`mvcc.evLog`). -/
theorem recv_unfiltered (γ : mvcc.WsNames) (w : Loc) (rs : List mvcc.RespM) (rg : mvcc.WatchRange)
    (fcs : GoSlice) (lo : Nat) :
    mvcc.watchRecvOk (GF := GF) γ w rs ∗ mvcc.watcherIs γ w rg fcs lo ∗ fcs ↦*□ ([] : List GoFunc) ⊢
      ∃ (L : mvcc.Log) (d : Nat), mvcc.evLog γ.st L ∗ mvcc.relLb γ L.length ∗
        ⌜(rs.map mvcc.RespM.evs).flatten = mvcc.watchEvents L rg lo d ∧ (d ≤ L.length ∨ d ≤ lo)⌝ := by
  iintro ⟨#Hc, #Hw, #Hfcs⟩
  unfold mvcc.watchRecvOk
  icases Hc with ⟨%γw, %r, %fcs', %L, %D, %d, #Hm, #Hf, -, #HL, #Hrl, %HD, #HDf, -⟩
  unfold mvcc.watcherIs
  icases Hw with ⟨%γw0, %C, #Hm0, #Hf0, -, -, %Hlo⟩
  ihave %Hag : iprop(⌜rg = r ∧ fcs = fcs'⌝) $$ []
  · iapply mvcc.watcherFixed_agree
    isplit
    · iexact Hf0
    · iexact Hf
  obtain ⟨rfl, rfl⟩ := Hag
  iunfold mvcc.watcherMeta at Hm
  iunfold mvcc.watcherMeta at Hm0
  ihave %Hmeq := ghostMapElem_agree _ _ _ _ _ _ $$ Hm Hm0
  subst Hmeq
  ihave %Hkeep : ⌜∀ dl ∈ D, dl.2 = dl.1⌝ $$ []
  · iintro %dl %hdl
    icases HDf $$ %dl %hdl with ⟨%fs, Hfi, %Hdl⟩
    iunfold mvcc.filtersImpl at Hfi
    icases Hfi with ⟨%fps, #Hfps, %Hlen, -⟩
    ihave %Heq := ownSlice_agree _ _ _ _ _ $$ Hfps Hfcs
    subst Heq
    have hfs : fs = [] := List.eq_nil_of_length_eq_zero (by simpa using Hlen.symm)
    subst hfs
    ipureintro
    rw [Hdl]
    unfold mvcc.filtered
    simp
  iexists L, d
  iframe HL Hrl
  ipureintro
  obtain ⟨h1, h2, h3, -⟩ := HD
  rw [← Hlo.1]
  refine ⟨?_, h3⟩
  rw [h1, ← h2]
  have hall : D.filter mvcc.Deliv.sent = D := by
    rw [List.filter_eq_self]
    intro dl hdl
    simp only [mvcc.Deliv.sent, Hkeep dl hdl, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
    cases dl.1 <;> simp
  rw [hall]
  congr 1
  exact List.map_congr_left Hkeep

/-- The events received so far of the watcher `w`. -/
abbrev evsOf (Dm : List v3rpc.WatchRespM) (w : Loc) : List mvcc.EvM :=
  ((v3rpc.sentEvsOf Dm w).map mvcc.RespM.evs).flatten

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
moves to the last one's revision, the events so far still a cut of the watcher's. -/
theorem dispatch_content (V : WEnv GF) (P : WsPrm GF) (rr : w64) (srr : Bool) (hb : w64)
    (Dm : List v3rpc.WatchRespM)
    (m : v3rpc.WatchRespM) (ρ : mvcc.RespM) (rs : List mvcc.RespM) (X : w64) (w : Loc)
    (rg : mvcc.WatchRange) (fcs : GoSlice) (lo : Nat) (hi : w64) (sl : GoSlice) (ps : List Loc)
    (hdr : w64)
    (hsrc : m.src = some ρ) (hρw : ρ.evs ≠ [] → ρ.w = w)
    (hfilt : ρ.evs ≠ [] → v3rpc.sentEvsOf Dm w ++ [ρ] = rs.filter (fun x => decide (x.evs ≠ [])))
    (hps : ps.length = ρ.evs.length) (hok : wsReqOk V.pfx P) (hpfx : V.pfx ≠ [])
    (hst : V.R.γ.st = V.R.E.γ) (hcr : v3rpc.createRangeOk (createOf P.key P.ed rr P.pn srr) X rg)
    (hrr : P.rev = W64 0 ∨ sint.Z P.rev ≤ sint.Z rr)
    (hhb : sint.Z hb < sint.Z rr ∨ sint.Z hb < 0)
    (hhi : (evsOf Dm w = [] ∧ hi = hb) ∨
      ∃ e, (evsOf Dm w).getLast? = some e ∧ hi = e.kv.modRev) :
    srvLogsSmall V.R ∗ srvNoDupKeys V.R ∗ watchLaws V ∗ mvcc.watchRecvOk V.R.γ ρ.w rs ∗
      mvcc.watcherIs V.R.γ w rg fcs lo ∗ fcs ↦*□ ([] : List GoFunc) ∗
      (⌜evsOf Dm w = []⌝ ∨ ∃ (L1 : mvcc.Log) (d1 : Nat), mvcc.idxSealed V.R.γ.st.idx L1 ∗
        ⌜evsOf Dm w = mvcc.watchEvents L1 rg lo d1 ∧ lo ≤ d1 ∧ d1 ≤ L1.length⌝) ∗
      sl ↦*□ ps ∗ ([∗list] x ∈ ps.zip ρ.evs, mvcc.evIs (GF := GF) x.1 x.2) ⊢
    |={⊤}=> ∃ es : List EvModel, eventsAt sl es ∗ ⌜es.length = ρ.evs.length⌝ ∗
      rangeWatchRespOk (EM := V.WM) V.pfx P.o P.rev hi ((es.getLast?.map EvModel.rev).getD hi)
        ⟨es, W64 0, false, false, hdr⟩ ∗
      ⌜(evsOf (Dm ++ [m]) w = [] ∧ (es.getLast?.map EvModel.rev).getD hi = hb) ∨
        ∃ e, (evsOf (Dm ++ [m]) w).getLast? = some e ∧
          (es.getLast?.map EvModel.rev).getD hi = e.kv.modRev⌝ ∗
      (⌜evsOf (Dm ++ [m]) w = []⌝ ∨ ∃ (L1 : mvcc.Log) (d1 : Nat), mvcc.idxSealed V.R.γ.st.idx L1 ∗
        ⌜evsOf (Dm ++ [m]) w = mvcc.watchEvents L1 rg lo d1 ∧ lo ≤ d1 ∧ d1 ≤ L1.length⌝) ∗
      (∃ kvs : List Loc, ⌜es = List.zipWith evModelOf ρ.evs kvs ∧ kvs.length = ρ.evs.length⌝ ∗
        □ (∀ (k : Nat) (ev : mvcc.EvM) (kv : Loc), ⌜ρ.evs[k]? = some ev⌝ → ⌜kvs[k]? = some kv⌝ →
          mvcc.kvPtrFixed kv ev.kv)) := by
  iintro ⟨#Hsm, #Hnd, #Hlaws, #Hrecv, #Hwi, #Hfcs, #Hcut, #Hsl, #Hevs⟩
  ihave ⟨%kvs, %Hkvl, #Hea, #Hkv⟩ := evs_eventsAt sl ps ρ.evs hps $$ [Hsl Hevs]
  · iframe #
  have hsnoc : evsOf (Dm ++ [m]) w = evsOf Dm w ++ (if ρ.evs ≠ [] then ρ.evs else []) := by
    unfold evsOf
    rw [sentEvsOf_snoc, hsrc]
    by_cases hne : ρ.evs ≠ []
    · simp [hρw hne, hne]
    · simp only [ne_eq, Decidable.not_not] at hne
      simp [hne]
  iexists List.zipWith evModelOf ρ.evs kvs
  iframe Hea
  isplitr
  · ipureintro; simp [Hkvl]
  by_cases hne : ρ.evs = []
  · -- no events: the cursor stands still
    imodintro
    have hes : List.zipWith evModelOf ρ.evs kvs = [] := by rw [hne]; simp
    rw [hes]
    have hsn : evsOf (Dm ++ [m]) w = evsOf Dm w := by rw [hsnoc, if_neg (by simp [hne])]; simp
    rw [hsn]
    simp only [List.getLast?_nil, Option.map_none, Option.getD_none]
    isplitr
    · unfold rangeWatchRespOk
      isplitr
      · ipureintro; simp [EvRevSorted]
      imodintro
      iintro %i %e %h
      simp at h
    isplitr
    · ipureintro; exact hhi
    isplitr
    · iexact Hcut
    iexists kvs
    iframe Hkv
    ipureintro; rw [hes]; exact ⟨rfl, Hkvl⟩
  -- events: the sealed log, unfiltered
  have hw := hρw hne
  irevert Hrecv
  rw [hw]
  iintro #Hrecv
  ihave ⟨%L, %d, #HLe, -, %HLd⟩ := recv_unfiltered V.R.γ w rs rg fcs lo $$ [Hrecv Hwi Hfcs]
  · iframe #
  ihave #HL := mvcc.evLog_sealed _ _ $$ HLe
  obtain ⟨hflat, hdL⟩ := HLd
  rw [evs_after Dm w rs ρ (hfilt hne)] at hflat
  have hflat' : evsOf Dm w ++ ρ.evs = mvcc.watchEvents L rg lo d := hflat
  ihave %HLw := v3rpc.sealed_pure _ L $$ HL
  iunfold srvNoDupKeys at Hnd
  ihave #HLc := mvcc.evLog_certOk _ _ $$ HLe
  ihave Hnd' := Hnd $$ %L HL HLc
  imod Hnd' with %HLnd
  -- (W3) the watched log, as the contract's model sees it
  ihave #Hsm' := Hsm
  iunfold srvLogsSmall at Hsm'
  ihave %HLs := Hsm' $$ %L HL
  ihave #Hlaws' := Hlaws
  iunfold watchLaws at Hlaws'
  icases Hlaws' with ⟨-, -, -, #Hconv⟩
  ihave HHWL0 := Hconv $$ %L HLe %HLs
  imod HHWL0 with #HWL
  imodintro
  -- the start revision (D25: the registration's, at or above the watch's)
  ihave %Hlor : ⌜sint.Z rr ≤ (lo : Int)⌝ $$ []
  · unfold mvcc.watcherIs
    icases Hwi with ⟨%γw0, %C, -, -, -, -, %Hlo⟩
    ipureintro
    obtain ⟨-, hsr, -, -⟩ := hcr
    rw [Hlo.2, hsr]
    show sint.Z rr ≤ ((if rr = W64 0 then C.length else (sint.Z rr).toNat : Nat) : Int)
    split
    · rename_i h; rw [h]; simp
    · omega
  have Hlo : sint.Z P.rev ≤ (lo : Int) := by
    rcases hrr with h | h
    · rw [h]; simp
    · omega
  -- the cut
  ihave %Hcc : ⌜d ≤ L.length ∧ lo ≤ d ∧ ∃ a, lo ≤ a ∧
      (∀ e ∈ evsOf Dm w, ∃ j, j < a ∧ e.kv.modRev = W64 (j : Int)) ∧
      ρ.evs = mvcc.watchEvents L rg a d⌝ $$ []
  · icases Hcut with (%HE | ⟨%L1, %d1, #HL1, %HE1⟩)
    · ipureintro
      exact content_cut L L rg lo d 0 (evsOf Dm w) ρ.evs (Or.inl (List.prefix_refl _)) hflat' hdL
        hne (Or.inl HE)
    · ihave %Hc : iprop(⌜L1 <+: L ∨ L <+: L1⌝) $$ []
      · iapply mvcc.idxSealed_prefix
        isplit
        · iexact HL1
        · iexact HL
      ipureintro
      exact content_cut L L1 rg lo d d1 (evsOf Dm w) ρ.evs Hc hflat' hdL hne (Or.inr HE1)
  obtain ⟨hdd, hlod, a, hla, hEj, hevs⟩ := Hcc
  have hLlen : L.length < 2 ^ 63 := HLw.2
  have hmemrev : ∀ ev ∈ ρ.evs, ∃ j, a ≤ j ∧ j < d ∧ ev.kv.modRev = W64 (j : Int) := by
    intro ev hev; rw [hevs] at hev; exact v3rpc.watchEvents_mem_rev L rg a d ev hev
  have hsorted : EvRevSorted (List.zipWith evModelOf ρ.evs kvs) := by
    unfold EvRevSorted
    have h1 := watchEvents_sorted L hLlen rg a d
    rw [← hevs] at h1
    have h2 : ((List.zipWith evModelOf ρ.evs kvs).map EvModel.rev).Pairwise
        (fun x y => sint.Z x ≤ sint.Z y) := by
      rw [zipWith_evModel_rev _ _ Hkvl, List.pairwise_map]; exact h1
    exact (List.pairwise_map (f := EvModel.rev) (R := fun x y => sint.Z x ≤ sint.Z y)).1 h2
  have hgt : ∀ e ∈ List.zipWith evModelOf ρ.evs kvs, sint.Z hi < sint.Z e.rev := by
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
  have hlast : (List.zipWith evModelOf ρ.evs kvs).getLast?.map EvModel.rev =
      ρ.evs.getLast?.map (fun e => e.kv.modRev) := by
    rw [← List.getLast?_map, zipWith_evModel_rev _ _ Hkvl, List.getLast?_map]
  obtain ⟨elast, helast⟩ : ∃ e, ρ.evs.getLast? = some e := by
    cases h : ρ.evs.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.1 h) hne
    | some e => exact ⟨e, rfl⟩
  have hsn : evsOf (Dm ++ [m]) w = evsOf Dm w ++ ρ.evs := by
    rw [hsnoc, if_pos hne]
  isplitr
  · unfold rangeWatchRespOk
    isplitr
    · ipureintro; exact ⟨hsorted, hgt, rfl⟩
    imodintro
    iintro %i %e %he
    rw [List.getElem?_zipWith] at he
    cases hev : ρ.evs[i]? with
    | none => rw [hev] at he; simp at he
    | some ev =>
      cases hkv : kvs[i]? with
      | none => rw [hev, hkv] at he; simp at he
      | some kv =>
        rw [hev, hkv] at he
        simp at he; subst he
        ihave #Hk := Hkv $$ %i %ev %kv %hev %hkv
        have hmem : ev ∈ mvcc.watchEvents L rg a d := by
          rw [← hevs]; exact List.mem_of_getElem? hev
        iapply ev_ok V P rr srr L rg X a d ev kv hok hpfx hcr hmem hdd (by omega) hst HLnd
        iframe #
  isplitr
  · ipureintro
    right
    refine ⟨elast, ?_, ?_⟩
    · rw [hsn, List.getLast?_append, helast]; rfl
    · rw [hlast, helast]; rfl
  isplitr
  · iright
    iexists L, d
    iframe HL
    ipureintro
    exact ⟨hsn.trans hflat', hlod, hdd⟩
  iexists kvs
  iframe Hkv
  ipureintro; exact ⟨rfl, Hkvl⟩

end content


end client
end EtcdGrove
end Perennial
