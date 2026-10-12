/-
Proof of `Spec/.../mvcc/watchableStore__notify.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__notify
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__addVictim
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watcher__send
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.newWatcherBatch
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watcherGroup__delete

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

/-! ## One revision's batch (pure) -/

/-- Every event of revision `N` is at mod revision `N`. -/
theorem evsOfRevM_modRev (N : Nat) (before : List EtcdKv) (hs : before.Pairwise etcdKvLess)
    (cs : List Change) : ∀ ev ∈ evsOfRevM N before cs, ev.kv.modRev = W64 N := by
  intro ev hev
  unfold evsOfRevM at hev
  rw [List.mem_filterMap] at hev
  obtain ⟨i, hi, hev⟩ := hev
  rw [List.mem_range] at hi
  cases hk : changeKv (W64 N) before cs i with
  | none => rw [hk] at hev; cases hev
  | some kv =>
    rw [hk] at hev
    simp only [Option.map_some, Option.some.injEq] at hev
    subst hev
    unfold evOfKv
    split
    · rfl
    · rename_i hc
      unfold changeKv at hk
      rw [List.getElem?_eq_getElem hi] at hk
      cases hci : cs[i] with
      | del k =>
        rw [hci] at hk
        simp only [Option.some.injEq] at hk
        subst hk
        exact absurd rfl hc
      | put k v l =>
        rw [hci] at hk
        simp only at hk
        rw [applyChanges_take_succ _ _ _ hi, hci] at hk
        obtain ⟨nv, hnv, -, hmod, -⟩ :=
          findKey_putKv_self (applyChanges_sorted (W64 N) (cs.take i) hs) (W64 N) k v l
        simp only [applyChange] at hk
        rw [hnv] at hk
        cases hk
        exact hmod

/-- `memberBatch` over events all at mod revision `m`, at or above `minRev`: the covered events in
one revision, or none. -/
theorem memberBatch_one_rev (r : WatchRange) (st : WatcherSt) (m : Nat) (hm : m < 2 ^ 63)
    (hmin : sint.Z st.minRev ≤ m) : ∀ (evs acc : List EvM),
    (∀ e ∈ evs, e.kv.modRev = W64 m) → (∀ e ∈ acc, e.kv.modRev = W64 m) →
    evs.foldl (fun ob ev =>
      if r.covers ev.kv.key && decide (sint.Z st.minRev ≤ sint.Z ev.kv.modRev) then
        some (ebAdd (ob.getD .empty) ev)
      else ob) (if acc = [] then none else some ⟨acc, W64 1, W64 0⟩) =
    (if acc ++ evs.filter (fun ev => r.covers ev.kv.key) = [] then none
      else some ⟨acc ++ evs.filter (fun ev => r.covers ev.kv.key), W64 1, W64 0⟩)
  | [], acc, _, _ => by simp
  | ev :: evs, acc, he, hacc => by
    have hev : ev.kv.modRev = W64 m := he ev List.mem_cons_self
    have hz : sint.Z (W64 m : w64) = m := by word
    rw [List.foldl_cons]
    by_cases hc : r.covers ev.kv.key = true
    · have hd : decide (sint.Z st.minRev ≤ sint.Z ev.kv.modRev) = true := by
        rw [hev, hz]; simpa using hmin
      simp only [hc, hd, Bool.and_self, ↓reduceIte]
      have hstep : some (ebAdd ((if acc = [] then none else some ⟨acc, W64 1, W64 0⟩ :
          Option EventBatch).getD .empty) ev) =
          (if acc ++ [ev] = [] then none else some ⟨acc ++ [ev], W64 1, W64 0⟩) := by
        rw [if_neg (show ¬ acc ++ [ev] = [] by simp)]
        by_cases ha : acc = []
        · subst ha
          simp only [↓reduceIte, Option.getD_none, List.nil_append]
          unfold ebAdd
          have hcap : ¬ sint.Z watchBatchMaxRevsV < sint.Z EventBatch.empty.revs := by decide
          rw [if_neg hcap]
          rfl
        · rw [if_neg ha]
          simp only [Option.getD_some]
          unfold ebAdd
          have hcap : ¬ sint.Z watchBatchMaxRevsV < sint.Z (W64 1 : w64) := by decide
          rw [if_neg hcap]
          obtain ⟨last, hl⟩ : ∃ last, acc.getLast? = some last := by
            cases h : acc.getLast? with
            | none => simp at h; exact absurd h ha
            | some x => exact ⟨x, rfl⟩
          rw [hl]
          have hlm : last.kv.modRev = W64 m := hacc last (List.mem_of_getLast? hl)
          simp only [hlm, hev, Int.lt_irrefl, ↓reduceIte]
      rw [hstep, memberBatch_one_rev r st m hm hmin evs (acc ++ [ev])
        (fun e h => he e (List.mem_cons_of_mem _ h))
        (fun e h => by
          rcases List.mem_append.1 h with h | h
          · exact hacc e h
          · rw [List.mem_singleton] at h; subst h; exact hev)]
      simp [List.filter_cons, hc]
    · have hc' : r.covers ev.kv.key = false := by simpa using hc
      simp only [hc', Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      rw [memberBatch_one_rev r st m hm hmin evs acc
        (fun e h => he e (List.mem_cons_of_mem _ h)) hacc]
      simp [List.filter_cons, hc']

/-- The range's events of the pending revision `N = ilog.length` of `ilog ++ [pend]`. -/
theorem watchEvents_next (ilog : Log) (pend : List Change) (hne : ilog ≠ []) (r : WatchRange) :
    watchEvents (ilog ++ [pend]) r ilog.length (ilog.length + 1) =
      (evsOfRevM ilog.length (stateAfter ilog) pend).filter (fun ev => r.covers ev.kv.key) := by
  unfold watchEvents
  rw [logEvents_succ]
  have hpos : 0 < ilog.length := List.length_pos_iff.2 hne
  have hs : stateAt (ilog ++ [pend]) (ilog.length - 1) = stateAfter ilog := by
    rw [stateAt_append_lt _ _ (by omega), stateAt_last]
  have hg : (ilog ++ [pend]).getD ilog.length [] = pend := by
    simp [List.getD_eq_getElem?_getD]
  rw [hs, hg]

/-- **`notify`'s batch** of a member at or below the pending revision `N`: the range's events of
`N`, in one revision, or none. -/
theorem notify_batch (ilog : Log) (pend : List Change) (hne : ilog ≠ [])
    (hlen : ilog.length < 2 ^ 63) (r : WatchRange) (st : WatcherSt)
    (hmin : sint.Z st.minRev ≤ ilog.length) :
    memberBatch r st (evsOfRevM ilog.length (stateAfter ilog) pend) =
      if watchEvents (ilog ++ [pend]) r ilog.length (ilog.length + 1) = [] then none
      else some ⟨watchEvents (ilog ++ [pend]) r ilog.length (ilog.length + 1), W64 1, W64 0⟩ := by
  rw [watchEvents_next ilog pend hne r]
  have h := memberBatch_one_rev r st ilog.length hlen hmin
    (evsOfRevM ilog.length (stateAfter ilog) pend) []
    (evsOfRevM_modRev _ _ (stateAfter_sorted ilog) pend) (fun _ h => by cases h)
  simp only [List.nil_append, ↓reduceIte] at h
  exact h

/-- Above every event's mod revision, a member gets no batch. -/
theorem memberBatch_none_of_gt (r : WatchRange) (st : WatcherSt) (m : Nat) (hm : m < 2 ^ 63)
    (hgt : (m : Int) < sint.Z st.minRev) : ∀ (evs : List EvM) (acc : Option EventBatch),
    (∀ e ∈ evs, e.kv.modRev = W64 m) →
    evs.foldl (fun ob ev =>
      if r.covers ev.kv.key && decide (sint.Z st.minRev ≤ sint.Z ev.kv.modRev) then
        some (ebAdd (ob.getD .empty) ev)
      else ob) acc = acc
  | [], _, _ => rfl
  | ev :: evs, acc, he => by
    have hev : ev.kv.modRev = W64 m := he ev List.mem_cons_self
    have hz : sint.Z (W64 m : w64) = m := by word
    rw [List.foldl_cons]
    have hd : decide (sint.Z st.minRev ≤ sint.Z ev.kv.modRev) = false := by
      rw [hev, hz]; simp; omega
    simp only [hd, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
    exact memberBatch_none_of_gt r st m hm hgt evs acc (fun e h => he e (List.mem_cons_of_mem _ h))

theorem batchOf_some {W : GMap Loc WatchRange} {ST : GMap Loc WatcherSt} {evs : List EvM} {w : Loc}
    {B : EventBatch} (h : batchOf W ST evs !! w = some B) :
    ∃ r st, W !! w = some r ∧ ST !! w = some st ∧ memberBatch r st evs = some B := by
  rw [batchOf_lookup] at h
  cases hW : W !! w <;> cases hS : ST !! w <;> rw [hW, hS] at h <;> simp at h
  exact ⟨_, _, rfl, rfl, h⟩

theorem batchOf_none {W : GMap Loc WatchRange} {ST : GMap Loc WatcherSt} {evs : List EvM} {w : Loc}
    {r : WatchRange} {st : WatcherSt} (hW : W !! w = some r) (hS : ST !! w = some st)
    (h : batchOf W ST evs !! w = none) : memberBatch r st evs = none := by
  rw [batchOf_lookup, hW, hS] at h; exact h

/-- A synced member with a batch at the pending revision `N`: at or below `N`, delivered exactly up
to `N`, its batch the range's events of `N` in one revision. -/
theorem batched_member (σ : WsState) (ilog : Log) (pend : List Change) (hne : ilog ≠ [])
    (hlen : ilog.length < 2 ^ 63) (hok : WsOk σ) (hLmu : σ.Lmu = ilog)
    (hbelow : σ.syncedBelow ilog.length) {w : Loc} {r : WatchRange} {st : WatcherSt}
    {γw : WatcherNames} {evsw : List EvM} {d : Nat} {B : EventBatch}
    (hW : (σ.Ws !! w).isSome) (hM : σ.M !! w = some γw) (hE : σ.E !! w = some (evsw, d))
    (hlo : (γw.lo : Int) ≤ sint.Z st.minRev) (hmd : sint.Z st.minRev ≤ d)
    (hB : memberBatch r st (evsOfRevM ilog.length (stateAfter ilog) pend) = some B) :
    sint.Z st.minRev ≤ ilog.length ∧ γw.lo ≤ ilog.length ∧ d = ilog.length ∧
      watchEvents (ilog ++ [pend]) r ilog.length (ilog.length + 1) ≠ [] ∧
      B = ⟨watchEvents (ilog ++ [pend]) r ilog.length (ilog.length + 1), W64 1, W64 0⟩ := by
  have hmin : sint.Z st.minRev ≤ ilog.length := by
    by_cases hc : sint.Z st.minRev ≤ ilog.length
    · exact hc
    exfalso
    have := memberBatch_none_of_gt r st ilog.length hlen (by omega)
      (evsOfRevM ilog.length (stateAfter ilog) pend) none
      (evsOfRevM_modRev _ _ (stateAfter_sorted ilog) pend)
    unfold memberBatch at hB
    rw [this] at hB; cases hB
  have hnb := notify_batch ilog pend hne hlen r st hmin
  rw [hB] at hnb
  have hsd := hok.synced_d w γw (evsw, d) hW hM hE
  rw [hLmu] at hsd
  have hbl := hbelow w γw (evsw, d) hW hM hE
  simp only at hsd hbl
  refine ⟨hmin, by omega, by omega, ?_, ?_⟩
  · intro h; rw [if_pos h] at hnb; cases hnb
  · by_cases h : watchEvents (ilog ++ [pend]) r ilog.length (ilog.length + 1) = []
    · rw [if_pos h] at hnb; cases hnb
    · rw [if_neg h] at hnb; exact Option.some.inj hnb

/-- The events of the pending revision are at its mod revision. -/
theorem watchEvents_next_modRev (ilog : Log) (pend : List Change) (hne : ilog ≠ [])
    (r : WatchRange) : ∀ ev ∈ watchEvents (ilog ++ [pend]) r ilog.length (ilog.length + 1),
      ev.kv.modRev = W64 ilog.length := by
  intro ev hev
  rw [watchEvents_next ilog pend hne r, List.mem_filter] at hev
  exact evsOfRevM_modRev _ _ (stateAfter_sorted ilog) pend ev hev.1

theorem WsOk_vs {σ : WsState} (h : WsOk σ) (v : GoSlice) : WsOk { σ with vs := v } :=
  ⟨h.ws_wu, h.ws_v, h.wu_v, h.v_one, h.live_st, h.live_e, h.st_m, h.wo_m, h.m_st, h.wo_st,
    h.wo_live, h.st_flags, h.wo_flags, h.synced_d⟩

/-- A map with values computed from the key. -/
def gmapMapK {K V V' : Type} (f : K → V → V') (m : GMap K V) : GMap K V' :=
  ⟨fun k => (m.lookup k).map (f k),
   by
    obtain ⟨l, hl⟩ := m.finite
    exact ⟨l, fun k h => hl k (by simpa using h)⟩⟩

theorem gmapMapK_lookup {K V V' : Type} (f : K → V → V') (m : GMap K V) (k : K) :
    gmapMapK f m !! k = (m !! k).map (f k) := rfl

section proof
open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- The loop's pure state (see `notify.wp_proof`): the states of the processed members updated,
the victims out of the synced group, the remaining batches. -/
structure NotifyRel (σ : WsState) (N : Nat) (Bt : GMap Loc EventBatch)
    (PB : GMap Loc (Loc × EventBatch)) (keys : List Loc) (i : Nat) (STi : GMap Loc WatcherSt)
    (Wsi : GMap Loc WatchRange) (Bv : GMap Loc EventBatch) (Out : GMap Loc (List EvM))
    (PBr : GMap Loc (Loc × EventBatch)) : Prop where
  st_rest : ∀ k, k ∉ keys.take i → STi !! k = σ.ST !! k
  st_done : ∀ k ∈ keys.take i, ∃ st, σ.ST !! k = some st ∧
    STi !! k = some { st with minRev := W64 (N + 1), victim := (Bv !! k).isSome }
  ws : ∀ k, Wsi !! k = if (Bv !! k).isSome then none else σ.Ws !! k
  bv : ∀ k B, Bv !! k = some B → k ∈ keys.take i ∧ Bt !! k = some B
  out : ∀ k, (Out !! k).isSome ↔ k ∈ keys.take i
  pbr : ∀ k, PBr !! k = if k ∈ keys.take i then none else PB !! k
  lo_done : ∀ k ∈ keys.take i, ∀ γw, σ.M !! k = some γw → γw.lo ≤ N + 1

/-- A processed synced member's resources after `notify`: its delivered events `evsw`, the
pending extension `ext` (a victim's batch), delivered up to `N + 1`. -/
def memberDone (γ : WsNames) (σ : WsState) (N : Nat) (w : Loc) (st : WatcherSt)
    (evsw ext : List EvM) : IProp GF :=
  iprop(∃ (γw : WatcherNames) (r : WatchRange) (fcs : GoSlice),
    ⌜σ.M !! w = some γw⌝ ∗ watcherMeta γ w γw ∗ watcherFixed w r fcs ∗
    watcherChan γ w γw st.ch ∗ filtersOk fcs ∗ ⌜sint.Z r.startRev ≤ (γw.lo : Int)⌝ ∗
    monoListAuthOwn γw.evs (1 : Qp).half evsw ∗
    dghostVar γw.live (DFrac.own (1 : Qp).half) true ∗
    ⌜(γw.lo : Int) ≤ sint.Z st.minRev ∧ sint.Z st.minRev = N + 1⌝ ∗
    evsWf γ r γw.lo (evsw ++ ext) (N + 1))

/-- The loop's member resources: the processed done, the others as before. -/
def memberAt (γ : WsNames) (σ : WsState) (N : Nat) (keys : List Loc) (i : Nat)
    (Out : GMap Loc (List EvM)) (Bv : GMap Loc EventBatch) (w : Loc) (st : WatcherSt) : IProp GF :=
  if w ∈ keys.take i then
    memberDone γ σ N w st ((Out !! w).getD []) (((Bv !! w).map EventBatch.evs).getD [])
  else memberRes γ 1 σ w st

/-- A synced member's resources, unfolded. -/
theorem memberRes_synced (γ : WsNames) (q : Qp) (σ : WsState) (w : Loc) (st : WatcherSt)
    (hW : (σ.Ws !! w).isSome) :
    memberRes γ q σ w st ⊢ ∃ (γw : WatcherNames) (r : WatchRange) (fcs : GoSlice)
      (evsw : List EvM) (d : Nat),
      ⌜σ.M !! w = some γw⌝ ∗ watcherMeta γ w γw ∗ watcherFixed w r fcs ∗
      watcherChan γ w γw st.ch ∗ filtersOk fcs ∗ ⌜sint.Z r.startRev ≤ (γw.lo : Int)⌝ ∗
      ⌜σ.E !! w = some (evsw, d)⌝ ∗ monoListAuthOwn γw.evs q.half evsw ∗
      dghostVar γw.live (DFrac.own q.half) true ∗
      ⌜(γw.lo : Int) ≤ sint.Z st.minRev ∧ sint.Z st.minRev ≤ d⌝ ∗ evsWf γ r γw.lo evsw d := by
  have hl : σ.live w := Or.inl hW
  unfold memberRes popFacts
  simp only [hl, hW, ↓reduceIte]
  iintro ⟨%γw, %r, %fcs, %hM, #Hm, #Hf, #Hc, #Hfo, %Hsr, %evsw, %d, %hE, Ha, Hl, %Hp, #Hwf⟩
  iexists γw, r, fcs, evsw, d
  iframe Hm Hf Hc Hfo Ha Hl Hwf
  ipureintro; exact ⟨hM, Hsr, hE, Hp⟩

theorem memberAt_rest (γ : WsNames) (σ : WsState) (N : Nat) (keys : List Loc) (i : Nat)
    (Out : GMap Loc (List EvM)) (Bv : GMap Loc EventBatch) (w : Loc) (st : WatcherSt)
    (h : w ∉ keys.take i) : memberAt (GF := GF) γ σ N keys i Out Bv w st = memberRes γ 1 σ w st := by
  unfold memberAt; rw [if_neg h]

theorem std_delete_eq {V : Type} (m : GMap Loc V) (k : Loc) : Std.delete m k = GMap.delete k m := rfl

/-- The loop's pure state, one key further: `key` processed (a victim if `vic`). -/
theorem NotifyRel.step {σ : WsState} {N : Nat} {Bt : GMap Loc EventBatch}
    {PB : GMap Loc (Loc × EventBatch)} {keys : List Loc} {i : Nat} {STi : GMap Loc WatcherSt}
    {Wsi : GMap Loc WatchRange} {Bv : GMap Loc EventBatch} {Out : GMap Loc (List EvM)}
    {PBr : GMap Loc (Loc × EventBatch)} (h : NotifyRel σ N Bt PB keys i STi Wsi Bv Out PBr)
    {key : Loc} (hkey : keys[i]? = some key) (hnot : key ∉ keys.take i) {stw : WatcherSt}
    (hST : σ.ST !! key = some stw) {B : EventBatch} (hBt : Bt !! key = some B)
    (hBv : Bv !! key = none) (vic : Bool) (e : List EvM)
    (hlo : ∀ γw, σ.M !! key = some γw → γw.lo ≤ N + 1) :
    NotifyRel σ N Bt PB keys (i + 1)
      (<[key := { stw with minRev := W64 (N + 1), victim := vic }]> STi)
      (if vic then GMap.delete key Wsi else Wsi)
      (if vic then <[key := B]> Bv else Bv) (<[key := e]> Out) (GMap.delete key PBr) := by
  have htake : keys.take (i + 1) = keys.take i ++ [key] := by
    rw [List.take_add_one, hkey]; rfl
  have hmem : ∀ k, k ∈ keys.take (i + 1) ↔ k ∈ keys.take i ∨ k = key := by
    intro k; rw [htake]; simp
  have hBv' : ∀ k, k ≠ key → (if vic then <[key := B]> Bv else Bv) !! k = Bv !! k := by
    intro k hk; cases vic
    · rfl
    · exact GMap.lookup_insert_ne _ _ (Ne.symm hk)
  have hBvk : (if vic then <[key := B]> Bv else Bv) !! key = if vic then some B else none := by
    cases vic
    · exact hBv
    · exact GMap.lookup_insert _ _ _
  constructor
  · intro k hk
    have hk' : k ≠ key := fun e => hk ((hmem k).2 (Or.inr e))
    rw [GMap.lookup_insert_ne _ _ (Ne.symm hk')]
    exact h.st_rest k (fun hm => hk ((hmem k).2 (Or.inl hm)))
  · intro k hk
    rcases (hmem k).1 hk with hk | rfl
    · obtain ⟨st0, h1, h2⟩ := h.st_done k hk
      have hk' : k ≠ key := fun e => hnot (e ▸ hk)
      refine ⟨st0, h1, ?_⟩
      rw [GMap.lookup_insert_ne _ _ (Ne.symm hk'), h2, hBv' k hk']
    · refine ⟨stw, hST, ?_⟩
      rw [GMap.lookup_insert, hBvk]
      cases vic <;> rfl
  · intro k
    by_cases hk : k = key
    · subst hk
      rw [hBvk]
      cases vic
      · simp only [Bool.false_eq_true, ↓reduceIte, Option.isSome_none]
        rw [h.ws, hBv]; rfl
      · simp only [↓reduceIte, Option.isSome_some, GMap.lookup_delete]
    · rw [hBv' k hk]
      cases vic
      · exact h.ws k
      · simp only [↓reduceIte]
        rw [GMap.lookup_delete_ne _ (Ne.symm hk)]; exact h.ws k
  · intro k B' hB'
    by_cases hk : k = key
    · subst hk
      rw [hBvk] at hB'
      cases vic
      · cases hB'
      · simp only [↓reduceIte, Option.some.injEq] at hB'
        subst hB'
        exact ⟨(hmem k).2 (Or.inr rfl), hBt⟩
    · rw [hBv' k hk] at hB'
      obtain ⟨h1, h2⟩ := h.bv k B' hB'
      exact ⟨(hmem k).2 (Or.inl h1), h2⟩
  · intro k
    rw [hmem k]
    by_cases hk : k = key
    · subst hk; simp [GMap.lookup_insert]
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hk), h.out k]; simp [hk]
  · intro k
    by_cases hk : k = key
    · subst hk; rw [GMap.lookup_delete]; simp [hmem]
    · rw [GMap.lookup_delete_ne _ (Ne.symm hk), h.pbr k]
      by_cases hm : k ∈ keys.take i
      · rw [if_pos hm, if_pos ((hmem k).2 (Or.inl hm))]
      · rw [if_neg hm, if_neg (by rw [hmem]; simp [hm, hk])]
  · intro k hk γw hM
    rcases (hmem k).1 hk with hk | rfl
    · exact h.lo_done k hk γw hM
    · exact hlo γw hM

theorem memberAt_succ_ne (γ : WsNames) (σ : WsState) (N : Nat) (keys : List Loc) (i : Nat)
    (Out Out' : GMap Loc (List EvM)) (Bv Bv' : GMap Loc EventBatch) {key : Loc}
    (hkey : keys[i]? = some key) (k : Loc) (hk : k ≠ key) (hO : Out' !! k = Out !! k)
    (hB : Bv' !! k = Bv !! k) (v : WatcherSt) :
    memberAt (GF := GF) γ σ N keys (i + 1) Out' Bv' k v = memberAt γ σ N keys i Out Bv k v := by
  have htake : keys.take (i + 1) = keys.take i ++ [key] := by
    rw [List.take_add_one, hkey]; rfl
  unfold memberAt
  rw [htake, hO, hB]
  simp [hk]

theorem memberAt_succ_key (γ : WsNames) (σ : WsState) (N : Nat) (keys : List Loc) (i : Nat)
    (Out : GMap Loc (List EvM)) (Bv : GMap Loc EventBatch) {key : Loc}
    (hkey : keys[i]? = some key) (v : WatcherSt) :
    memberAt (GF := GF) γ σ N keys (i + 1) Out Bv key v =
      memberDone γ σ N key v ((Out !! key).getD []) (((Bv !! key).map EventBatch.evs).getD []) := by
  have htake : keys.take (i + 1) = keys.take i ++ [key] := by
    rw [List.take_add_one, hkey]; rfl
  unfold memberAt
  rw [htake, if_pos (by simp)]

/-- Replacing one key's entry of a big separating conjunction, with a new predicate that agrees
elsewhere. -/
theorem bigSepM_step {V : Type} {Φ Ψ : Loc → V → IProp GF} (m : GMap Loc V) (w : Loc) (y : V)
    (h : ∀ k v, k ≠ w → Φ k v ⊢ Ψ k v) :
    ([∗map] k ↦ v ∈ Std.delete m w, Φ k v) ∗ Ψ w y ⊢ [∗map] k ↦ v ∈ <[w := y]> m, Ψ k v := by
  refine (sep_comm.1.trans ?_).trans BigSepM.bigSepM_insert_delete.2
  refine sep_mono_right (BigSepM.bigSepM_mono (fun {k v} hk => h k v ?_))
  intro e; subst e
  rw [std_delete_eq] at hk
  exact absurd hk (by simp [gmap_get?_eq, GMap.lookup_delete])

/-- The lock's state after `notify` (the loop's final state, the new victims appended). -/
def notifyState (σ : WsState) (N : Nat) (STi : GMap Loc WatcherSt) (Wsi : GMap Loc WatchRange)
    (Bv : GMap Loc EventBatch) (Out : GMap Loc (List EvM)) (vs' : GoSlice) (vm : GoMap) : WsState :=
  { σ with
    Ws := Wsi, ST := STi,
    E := gmapMapK (fun k e => match Out !! k with
      | some ev => (ev, N + 1)
      | none => if (σ.Ws !! k).isSome then (e.1, max (((σ.M !! k).map WatcherNames.lo).getD 0) (N + 1))
        else e) σ.E,
    vs := vs',
    vbs := if GMap.size Bv = 0 then σ.vbs else σ.vbs ++ [vm],
    VB := if GMap.size Bv = 0 then σ.VB else σ.VB ++ [Bv] }

theorem findSome_isSome_of_mem {B : GMap Loc EventBatch} {l : List (GMap Loc EventBatch)} {w : Loc}
    (hB : B ∈ l) (hw : (B !! w).isSome) : (l.findSome? (· !! w)).isSome := by
  induction l with
  | nil => cases hB
  | cons x xs ih =>
    rw [List.findSome?_cons]
    rcases List.mem_cons.1 hB with rfl | h
    · cases h' : B !! w with
      | none => rw [h'] at hw; cases hw
      | some _ => simp
    · cases h' : x !! w with
      | none => exact ih h
      | some _ => simp

theorem notify_final (σ : WsState) (N : Nat) (hLmu : σ.Lmu.length = N) (hok : WsOk σ)
    (Bt : GMap Loc EventBatch) (hBtWs : ∀ k, (Bt !! k).isSome → (σ.Ws !! k).isSome)
    (PB : GMap Loc (Loc × EventBatch)) (keys : List Loc)
    (hkeys : ∀ k, k ∈ keys ↔ (Bt !! k).isSome) (STi : GMap Loc WatcherSt)
    (Wsi : GMap Loc WatchRange) (Bv : GMap Loc EventBatch) (Out : GMap Loc (List EvM))
    (PBr : GMap Loc (Loc × EventBatch))
    (hrel : NotifyRel σ N Bt PB keys keys.length STi Wsi Bv Out PBr) (vs' : GoSlice) (vm : GoMap) :
    WsOk (notifyState σ N STi Wsi Bv Out vs' vm) ∧
      (notifyState σ N STi Wsi Bv Out vs' vm).syncedAbove (N + 1) ∧
      (∀ k, (notifyState σ N STi Wsi Bv Out vs' vm).live k ↔ σ.live k) ∧
      (∀ k, (notifyState σ N STi Wsi Bv Out vs' vm).victimOf k = (σ.victimOf k).or (Bv !! k)) := by
  have htk : keys.take keys.length = keys := List.take_length
  have hBvBt : ∀ k B, Bv !! k = some B → Bt !! k = some B := fun k B h => (hrel.bv k B h).2
  have hBvWs : ∀ k, (Bv !! k).isSome → (σ.Ws !! k).isSome := by
    intro k h
    cases hb : Bv !! k with
    | none => rw [hb] at h; cases h
    | some B => exact hBtWs k (by rw [hBvBt k B hb]; rfl)
  have hvo : ∀ k, (notifyState σ N STi Wsi Bv Out vs' vm).victimOf k = (σ.victimOf k).or (Bv !! k) := by
    intro k
    unfold notifyState WsState.victimOf
    simp only
    split
    · rename_i h0
      have : Bv = ∅ := GMap.map_size_empty_inv _ h0
      subst this; simp
    · rw [List.findSome?_append]; simp
  have hWsi : ∀ k, Wsi !! k = if (Bv !! k).isSome then none else σ.Ws !! k := hrel.ws
  have hlive : ∀ k, (notifyState σ N STi Wsi Bv Out vs' vm).live k ↔ σ.live k := by
    intro k
    unfold WsState.live
    rw [hvo k]
    show (Wsi !! k).isSome = true ∨ (σ.Wu !! k).isSome = true ∨ ((σ.victimOf k).or (Bv !! k)).isSome = true ↔ _
    rw [hWsi k]
    cases hb : Bv !! k with
    | none => simp
    | some B =>
      have hw := hBvWs k (by rw [hb]; rfl)
      simp [hw]
  have hST : ∀ k, (STi !! k).isSome ↔ (σ.ST !! k).isSome := by
    intro k
    by_cases hk : k ∈ keys
    · obtain ⟨st, h1, h2⟩ := hrel.st_done k (by rw [htk]; exact hk)
      rw [h1, h2]; rfl
    · rw [hrel.st_rest k (by rw [htk]; exact hk)]
  have hBvkeys : ∀ k, (Bv !! k).isSome → k ∈ keys := by
    intro k h
    cases hb : Bv !! k with
    | none => rw [hb] at h; cases h
    | some B => have := (hrel.bv k B hb).1; rwa [htk] at this
  have hE : ∀ k, (notifyState σ N STi Wsi Bv Out vs' vm).E !! k = (σ.E !! k).map (fun e => match Out !! k with
      | some ev => (ev, N + 1)
      | none => if (σ.Ws !! k).isSome then (e.1, max (((σ.M !! k).map WatcherNames.lo).getD 0) (N + 1))
        else e) := fun k => rfl
  have hd : ∀ k γw ed, (Wsi !! k).isSome → σ.M !! k = some γw →
      (notifyState σ N STi Wsi Bv Out vs' vm).E !! k = some ed → max γw.lo (N + 1) ≤ ed.2 := by
    intro k γw ed hw hM hed
    rw [hE] at hed
    cases he : σ.E !! k with
    | none => rw [he] at hed; cases hed
    | some e =>
      rw [he] at hed
      simp only [Option.map_some, Option.some.injEq] at hed
      subst hed
      cases ho : Out !! k with
      | some ev =>
        simp only
        have hk : k ∈ keys := by
          have := (hrel.out k).1 (by rw [ho]; rfl); rwa [htk] at this
        have := hrel.lo_done k (by rw [htk]; exact hk) γw hM
        omega
      | none =>
        have hws : (σ.Ws !! k).isSome := by
          rw [hWsi k] at hw; split at hw
          · cases hw
          · exact hw
        simp only [hws, ↓reduceIte, hM, Option.map_some, Option.getD_some, Nat.le_refl]
  refine ⟨?_, ?_, hlive, hvo⟩
  · constructor
    · intro w h
      simp only [notifyState] at h ⊢
      rw [hWsi w] at h; split at h
      · cases h
      · exact hok.ws_wu w h
    · intro w h
      rw [hvo w]
      simp only [notifyState] at h
      rw [hWsi w] at h; split at h
      · cases h
      · rename_i hb
        rw [hok.ws_v w h]
        cases hb' : Bv !! w with
        | none => rfl
        | some _ => rw [hb'] at hb; exact absurd rfl hb
    · intro w h
      simp only [notifyState] at h
      rw [hvo w, hok.wu_v w h]
      cases hb : Bv !! w with
      | none => rfl
      | some B =>
        have := hok.ws_wu w (hBvWs w (by rw [hb]; rfl))
        rw [this] at h; cases h
    · intro i j B B' w hi hj hB hB'
      show i = j
      unfold notifyState at hi hj
      simp only at hi hj
      by_cases h0 : Bv.size = 0
      · rw [if_pos h0] at hi hj
        exact hok.v_one i j B B' w hi hj hB hB'
      · rw [if_neg h0] at hi hj
        by_cases hi' : i < σ.VB.length <;> by_cases hj' : j < σ.VB.length
        · rw [List.getElem?_append_left hi'] at hi
          rw [List.getElem?_append_left hj'] at hj
          exact hok.v_one i j B B' w hi hj hB hB'
        · rw [List.getElem?_append_left hi'] at hi
          rw [List.getElem?_append_right (by omega)] at hj
          have hj1 : j - σ.VB.length = 0 := by
            have := (List.getElem?_eq_some_iff.1 hj).1; simp at this; omega
          rw [hj1] at hj; simp at hj; subst hj
          have hws := hBvWs w hB'
          have := hok.ws_v w hws
          unfold WsState.victimOf at this
          have := findSome_isSome_of_mem (List.mem_of_getElem? hi) hB
          rw [‹σ.VB.findSome? (· !! w) = none›] at this; cases this
        · rw [List.getElem?_append_left hj'] at hj
          rw [List.getElem?_append_right (by omega)] at hi
          have hi1 : i - σ.VB.length = 0 := by
            have := (List.getElem?_eq_some_iff.1 hi).1; simp at this; omega
          rw [hi1] at hi; simp at hi; subst hi
          have hws := hBvWs w hB
          have := hok.ws_v w hws
          unfold WsState.victimOf at this
          have := findSome_isSome_of_mem (List.mem_of_getElem? hj) hB'
          rw [‹σ.VB.findSome? (· !! w) = none›] at this; cases this
        · have h1 := (List.getElem?_eq_some_iff.1 hi).1
          have h2 := (List.getElem?_eq_some_iff.1 hj).1
          simp at h1 h2; omega
    · intro w h
      rw [hlive] at h
      show (STi !! w).isSome
      rw [hST]; exact hok.live_st w h
    · intro w
      show ((notifyState σ N STi Wsi Bv Out vs' vm).E !! w).isSome ↔ _
      rw [hE, hlive, ← hok.live_e w]; simp
    · intro w h; exact hok.st_m w ((hST w).1 h)
    · exact hok.wo_m
    · intro w h
      rcases hok.m_st w h with h1 | h1
      · exact Or.inl ((hST w).2 h1)
      · exact Or.inr h1
    · intro w h
      have := hok.wo_st w h
      show STi !! w = none
      cases hs : STi !! w with
      | none => rfl
      | some _ =>
        have := (hST w).1 (by rw [hs]; rfl)
        rw [‹σ.ST !! w = none›] at this; cases this
    · intro w h; rw [hlive]; exact hok.wo_live w h
    · intro w st' h
      show _ ∧ _ ∧ ((notifyState σ N STi Wsi Bv Out vs' vm).live w →
        (st'.victim = true ↔ ((notifyState σ N STi Wsi Bv Out vs' vm).victimOf w).isSome)) ∧
        (st'.ch = null ↔ ¬ (notifyState σ N STi Wsi Bv Out vs' vm).live w)
      rw [hlive, hvo]
      change STi !! w = some st' at h
      by_cases hk : w ∈ keys
      · obtain ⟨st, h1, h2⟩ := hrel.st_done w (by rw [htk]; exact hk)
        rw [h] at h2; cases h2
        obtain ⟨hc, hr, hv, hch⟩ := hok.st_flags w st h1
        have hws : (σ.Ws !! w).isSome := hBtWs w ((hkeys w).1 hk)
        refine ⟨hc, hr, fun _ => ?_, hch⟩
        rw [hok.ws_v w hws]; simp
      · rw [hrel.st_rest w (by rw [htk]; exact hk)] at h
        obtain ⟨hc, hr, hv, hch⟩ := hok.st_flags w st' h
        have hb : Bv !! w = none := by
          cases hb : Bv !! w with
          | none => rfl
          | some _ => exact absurd (hBvkeys w (by rw [hb]; rfl)) hk
        rw [hb]
        refine ⟨hc, hr, fun hl => ?_, hch⟩
        rw [Option.or_none]; exact hv hl
    · exact hok.wo_flags
    · intro w γw ed hw hM hed
      have := hd w γw ed hw hM hed
      show max γw.lo σ.Lmu.length ≤ ed.2
      omega
  · intro w γw ed hw hM hed
    exact hd w γw ed hw hM hed

theorem popFacts_synced (γ : WsNames) (σ : WsState) (k : Loc) (r : WatchRange) (lo : Nat)
    (st : WatcherSt) (evsw : List EvM) (d : Nat) (h : (σ.Ws !! k).isSome) :
    popFacts (GF := GF) γ σ k r lo st evsw d =
      iprop(⌜(lo : Int) ≤ sint.Z st.minRev ∧ sint.Z st.minRev ≤ d⌝ ∗ evsWf γ r lo evsw d) := by
  unfold popFacts; rw [if_pos h]

theorem popFacts_victim (γ : WsNames) (σ : WsState) (k : Loc) (r : WatchRange) (lo : Nat)
    (st : WatcherSt) (evsw : List EvM) (d : Nat) (B : EventBatch) (h1 : (σ.Ws !! k).isSome = false)
    (h2 : (σ.Wu !! k).isSome = false) (h3 : σ.victimOf k = some B) :
    popFacts (GF := GF) γ σ k r lo st evsw d =
      iprop(⌜(lo : Int) ≤ sint.Z st.minRev ∧ d = sint.nat st.minRev⌝ ∗ evsWf γ r lo (evsw ++ B.evs) d) := by
  unfold popFacts; simp only [h1, h2, h3, Bool.false_eq_true, ↓reduceIte]

/-- The lock's resources of a watcher after `notify`. -/
theorem memberRes_final (γ : WsNames) (σ : WsState) (ilog : Log) (pend : List Change) (N : Nat)
    (hN : ilog.length = N) (hLmu : σ.Lmu = ilog) (hne : ilog ≠ []) (hlen : N + 2 < 2 ^ 63)
    (hok : WsOk σ) (hbelow : σ.syncedBelow N) (keys : List Loc) (PB : GMap Loc (Loc × EventBatch))
    (STi : GMap Loc WatcherSt) (Wsi : GMap Loc WatchRange) (Bv : GMap Loc EventBatch)
    (Out : GMap Loc (List EvM)) (PBr : GMap Loc (Loc × EventBatch))
    (hkeys : ∀ k, k ∈ keys ↔
      (batchOf σ.Ws σ.ST (evsOfRevM N (stateAfter ilog) pend) !! k).isSome)
    (hrel : NotifyRel σ N (batchOf σ.Ws σ.ST (evsOfRevM N (stateAfter ilog) pend)) PB keys
      keys.length STi Wsi Bv Out PBr)
    (vs' : GoSlice) (vm : GoMap) (k : Loc) (st : WatcherSt) (hSTk : STi !! k = some st) :
    (monoListLbOwn γ.st.idx.hist (histOf (ilog ++ [pend])) ∗
        ([∗map] w ↦ r ∈ Wsi, ∃ fcs, watcherFixed w r fcs)) ∗
        memberAt (GF := GF) γ σ N keys keys.length Out Bv k st ⊢
      memberRes γ 1 (notifyState σ N STi Wsi Bv Out vs' vm) k st := by
  have hBtWs : ∀ k, (batchOf σ.Ws σ.ST (evsOfRevM N (stateAfter ilog) pend) !! k).isSome →
      (σ.Ws !! k).isSome := by
    intro k h
    cases hb : batchOf σ.Ws σ.ST (evsOfRevM N (stateAfter ilog) pend) !! k with
    | none => rw [hb] at h; cases h
    | some B => obtain ⟨r, _, hW, -⟩ := batchOf_some hb; rw [hW]; rfl
  obtain ⟨-, -, hlive, hvo⟩ := notify_final σ N (by rw [hLmu, hN]) hok _ hBtWs PB keys hkeys STi
    Wsi Bv Out PBr hrel vs' vm
  have htk : keys.take keys.length = keys := List.take_length
  have hWsi : ∀ k, (notifyState σ N STi Wsi Bv Out vs' vm).Ws !! k =
      if (Bv !! k).isSome then none else σ.Ws !! k := hrel.ws
  have hE : ∀ k, (notifyState σ N STi Wsi Bv Out vs' vm).E !! k = (σ.E !! k).map (fun e =>
      match Out !! k with
      | some ev => (ev, N + 1)
      | none => if (σ.Ws !! k).isSome then
          (e.1, max (((σ.M !! k).map WatcherNames.lo).getD 0) (N + 1))
        else e) := fun k => rfl
  have hM' : (notifyState σ N STi Wsi Bv Out vs' vm).M = σ.M := rfl
  have hBvkeys : ∀ k, (Bv !! k).isSome → k ∈ keys := by
    intro k h
    cases hb : Bv !! k with
    | none => rw [hb] at h; cases h
    | some B => have := (hrel.bv k B hb).1; rwa [htk] at this
  have hlv' : (notifyState σ N STi Wsi Bv Out vs' vm).live k = σ.live k := propext (hlive k)
  unfold memberRes
  simp only [hM', hlv']
  by_cases hk : k ∈ keys
  · unfold memberAt
    rw [if_pos (by rw [htk]; exact hk)]
    obtain ⟨ev, hev⟩ : ∃ ev, Out !! k = some ev := by
      have := (hrel.out k).2 (by rw [htk]; exact hk)
      cases h : Out !! k with
      | none => rw [h] at this; cases this
      | some ev => exact ⟨ev, rfl⟩
    have hws := hBtWs k ((hkeys k).1 hk)
    have hlv : σ.live k := Or.inl hws
    obtain ⟨e0, he0⟩ : ∃ e0, σ.E !! k = some e0 := by
      have := (hok.live_e k).2 (Or.inl hws)
      cases h : σ.E !! k with
      | none => rw [h] at this; cases this
      | some e0 => exact ⟨e0, rfl⟩
    have hE' : (notifyState σ N STi Wsi Bv Out vs' vm).E !! k = some (ev, N + 1) := by
      rw [hE, he0]; simp [hev]
    unfold memberDone
    simp only [hev, hlv, if_true, hE', Option.getD_some]
    cases hb : Bv !! k with
    | none =>
      have hw' : ((notifyState σ N STi Wsi Bv Out vs' vm).Ws !! k).isSome = true := by
        rw [hWsi, hb]; exact hws
      simp only [popFacts_synced γ _ k _ _ st _ _ hw', Option.map_none, Option.getD_none,
        List.append_nil]
      iintro ⟨-, ⟨%γw, %r, %fcs, %hM, #Hm, #Hf, #Hc, #Hfo, %Hsr, Ha, Hl, %Hmin, #Hwf⟩⟩
      iexists γw, r, fcs
      iframe Hm Hf Hc Hfo Ha Hl Hwf
      ipureintro
      exact ⟨hM, Hsr, rfl, Hmin.1, by omega⟩
    | some B =>
      have hw' : ((notifyState σ N STi Wsi Bv Out vs' vm).Ws !! k).isSome = false := by
        rw [hWsi, hb]; rfl
      have hu' : ((notifyState σ N STi Wsi Bv Out vs' vm).Wu !! k).isSome = false := by
        show (σ.Wu !! k).isSome = false
        rw [hok.ws_wu k hws]; rfl
      have hv' : (notifyState σ N STi Wsi Bv Out vs' vm).victimOf k = some B := by
        rw [hvo, hok.ws_v k hws, hb]; rfl
      simp only [popFacts_victim γ _ k _ _ st _ _ B hw' hu' hv', Option.map_some,
        Option.getD_some]
      iintro ⟨-, ⟨%γw, %r, %fcs, %hM, #Hm, #Hf, #Hc, #Hfo, %Hsr, Ha, Hl, %Hmin, #Hwf⟩⟩
      iexists γw, r, fcs
      iframe Hm Hf Hc Hfo Ha Hl Hwf
      ipureintro
      refine ⟨hM, Hsr, rfl, Hmin.1, ?_⟩
      have : sint.Z st.minRev = ((N + 1 : Nat) : Int) := by rw [Hmin.2]; push_cast; rfl
      have h2 : sint.nat st.minRev = (sint.Z st.minRev).toNat := rfl
      rw [h2, this]; rfl
  · unfold memberAt
    rw [if_neg (by rw [htk]; exact hk)]
    have hb : Bv !! k = none := by
      cases hb : Bv !! k with
      | none => rfl
      | some _ => exact absurd (hBvkeys k (by rw [hb]; rfl)) hk
    have ho : Out !! k = none := by
      cases ho : Out !! k with
      | none => rfl
      | some _ => exact absurd (by have := (hrel.out k).1 (by rw [ho]; rfl); rwa [htk] at this) hk
    have hw' : (notifyState σ N STi Wsi Bv Out vs' vm).Ws !! k = σ.Ws !! k := by rw [hWsi, hb]; rfl
    have hv' : (notifyState σ N STi Wsi Bv Out vs' vm).victimOf k = σ.victimOf k := by
      rw [hvo, hb]; simp
    unfold memberRes
    by_cases hl' : ¬ σ.live k
    · simp only [hl', if_false]
      iintro ⟨-, H⟩
      iexact H
    have hl : σ.live k := Classical.not_not.1 hl'
    by_cases hws : (σ.Ws !! k).isSome
    · -- a synced member without events at `N`
      have hws' : ((notifyState σ N STi Wsi Bv Out vs' vm).Ws !! k).isSome = true := by
        rw [hw']; exact hws
      simp only [hl, if_true, popFacts_synced γ _ k _ _ st _ _ hws', popFacts_synced γ σ k _ _ st _ _ hws]
      obtain ⟨r0, hr0⟩ : ∃ r0, σ.Ws !! k = some r0 := by
        cases h : σ.Ws !! k with
        | none => rw [h] at hws; cases hws
        | some r0 => exact ⟨r0, rfl⟩
      have hWsik : Wsi !! k = some r0 := by rw [hrel.ws, hb]; exact hr0
      have hSTk' : σ.ST !! k = some st := by
        rw [← hrel.st_rest k (by rw [htk]; exact hk)]; exact hSTk
      have hnb : memberBatch r0 st (evsOfRevM N (stateAfter ilog) pend) = none := by
        apply batchOf_none hr0 hSTk'
        cases h : batchOf σ.Ws σ.ST (evsOfRevM N (stateAfter ilog) pend) !! k with
        | none => rfl
        | some _ => exact absurd ((hkeys k).2 (by rw [h]; rfl)) hk
      iintro ⟨⟨#Hlb, #Hfxs⟩, ⟨%γw, %r, %fcs, %hM, #Hm, #Hf, #Hc, #Hfo, %Hsr, %evsw, %d, %hEk, Ha, Hl,
        %Hp, #Hwf⟩⟩
      icases (BigSepM.bigSepM_lookup_acc hWsik).1 $$ Hfxs with ⟨⟨%fcs0, #Hf0⟩, -⟩
      ihave %Hag := watcherFixed_agree k r r0 fcs fcs0 $$ [$Hf $Hf0]
      obtain ⟨hrr, -⟩ := Hag
      subst hrr
      have hsd := hok.synced_d k γw (evsw, d) hws hM hEk
      have hbl := hbelow k γw (evsw, d) hws hM hEk
      rw [hLmu, hN] at hsd
      simp only at hsd hbl
      have hE'k : (notifyState σ N STi Wsi Bv Out vs' vm).E !! k = some (evsw, max γw.lo (N + 1)) := by
        rw [hE, hEk]; simp [ho, hws, hM]
      iexists γw, r, fcs
      iframe Hm Hf Hc Hfo Ha Hl
      isplitr
      · ipureintro; exact hM
      isplitr
      · ipureintro; exact Hsr
      iexists max γw.lo (N + 1)
      isplitr
      · ipureintro; exact hE'k
      isplitr
      · ipureintro; exact ⟨Hp.1, by omega⟩
      by_cases hlo : γw.lo ≤ N
      · -- delivered up to `N`; nothing at `N`
        have hdN : d = N := by omega
        have hminN : sint.Z st.minRev ≤ N := by omega
        have hnb' := notify_batch ilog pend hne (by omega) r st (by rw [hN]; exact hminN)
        rw [hN, hnb] at hnb'
        have hwE : watchEvents (ilog ++ [pend]) r N (N + 1) = [] := by
          by_cases h : watchEvents (ilog ++ [pend]) r N (N + 1) = []
          · exact h
          · rw [if_neg h] at hnb'; cases hnb'
        iunfold evsWf at Hwf
        iunfold evsWf
        icases Hwf with ⟨%L, #HlbL, %HL⟩
        ihave %Hcmp := mono_list_lb_valid _ _ _ $$ Hlb HlbL
        have hcmp := histOf_cmp_log Hcmp
        rw [hdN] at HL
        iexists ilog ++ [pend]
        iframe Hlb
        ipureintro
        refine ⟨?_, Or.inl (by simp; omega)⟩
        rw [HL.1, show max γw.lo (N + 1) = N + 1 by omega,
          watchEvents_cmp hcmp.symm r HL.2 (Or.inl (by simp; omega)),
          watchEvents_append (ilog ++ [pend]) r (show γw.lo ≤ N by omega) (show N ≤ N + 1 by omega),
          hwE, List.append_nil]
      · have hd : d = γw.lo := by omega
        rw [show max γw.lo (N + 1) = γw.lo by omega, ← hd]
        iexact Hwf
    · have hpop : ∀ r lo evsw d, popFacts (GF := GF) γ (notifyState σ N STi Wsi Bv Out vs' vm) k r lo st evsw d =
          popFacts γ σ k r lo st evsw d := by
        intro r lo evsw d; unfold popFacts; rw [hw', hv']; rfl
      have hE'k : (notifyState σ N STi Wsi Bv Out vs' vm).E !! k = σ.E !! k := by
        rw [hE]; cases σ.E !! k <;> simp [ho, hws]
      simp only [hpop, hE'k]
      iintro ⟨-, H⟩
      iexact H

end proof

end mvcc
end EtcdGrove
end Perennial

namespace Perennial
namespace EtcdGrove
open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc
section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.watchableStore.notify.wp_proof
    (hNWB : mvcc.newWatcherBatch.spec (GF := GF) (hG := hG))
    (hSend : mvcc.watcher.send.spec (GF := GF) (hG := hG))
    (hDel : mvcc.watcherGroup.delete.spec (GF := GF) (hG := hG))
    (hAddV : mvcc.watchableStore.addVictim.spec (GF := GF) (hG := hG)) :
    mvcc.watchableStore.notify.spec (GF := GF) (hG := hG) := by
  intro s st γ σ ilog pend evs dq es evm
  wp_start as ⟨#Hws, Hbody, %Hpre, #Hlb, Hevs, #HevIs, %Hevm⟩
  obtain ⟨hLmu, hbelow, hlen, hne⟩ := Hpre
  obtain ⟨hes, hevm⟩ := Hevm
  ihave Hmi : (mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hmi with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨%gW, #HgW, #HgWS⟩,
    ⟨%gS, #HgS, #HgSS⟩, ⟨%gP, #HgP, #HgPS⟩⟩
  iunfold mvcc.watchStoreBody at Hbody
  iNamed Hbody
  have hok_live : ∀ w, (σ.Ws !! w).isSome → (σ.ST !! w).isSome :=
    fun w h => Hok.live_st w (Or.inl h)
  wp_auto
  rw [go.make1_underlying, go.is_underlying (t := watcherBatch.ty)]
  wp_apply (wp_map_make1 (K := Loc) (V := Loc)) as %vm Hvm
  (try wp_auto)
  wp_apply (hNWB (syncedAddr s) σ.Ws σ.ST evs dq es evm) $$ [$Hsynced Hst $Hevs $HevIs]
    as %wb ⟨Hsynced, Hst, Hevs, Hwb⟩
  · iunfold mvcc.ownStates; iframe Hst
    ipureintro; exact ⟨hok_live, hes⟩
  iunfold mvcc.ownStates at Hst
  icases Hwb with (%hWs0 | ⟨%hWs0, Hwb⟩)
  · obtain ⟨hWse, hwbn⟩ := hWs0
    subst hwbn
    wp_func_lits
    wp_auto
    wp_apply +noauto (hAddV s st γ σ.vs σ.vbs vm (DFrac.own 1) ∅)
      $$ [$Hws $Hvf $Hvs $Hvcap $Hvm] as ⟨Hvm, %vs', Hvf, Hvs, Hvcap⟩
    imod ghostVar_update { σ with vs := vs' } γ.wst σ $$ Hσ with Hσ
    (try wp_auto)
    iapply HΦ
    iframe Hevs
    iexists { σ with vs := vs' }
    simp only [GMap.map_size_empty, ↓reduceIte]
    iunfold mvcc.watchStoreBody
    simp only [named]
    iframe Hσ Hwlog Hcert Hsynced Hunsynced Hvf Hvs Hvcap Hvbs Hwo Hmeta Hmfix
    have em : ∀ w st, mvcc.memberRes (GF := GF) γ 1 { σ with vs := vs' } w st = mvcc.memberRes γ 1 σ w st :=
      fun _ _ => rfl
    have eo : ∀ w st, mvcc.outRes (GF := GF) γ { σ with vs := vs' } w st = mvcc.outRes γ σ w st :=
      fun _ _ => rfl
    simp only [em, eo]
    iframe Hst Hmem Hout
    ipureintro
    refine ⟨⟨Hvlen, mvcc.WsOk_vs Hok vs'⟩, hLmu, fun w γw ed hw => ?_⟩
    rw [hWse] at hw; cases hw
  iunfold mvcc.ownWatcherBatch at Hwb
  icases Hwb with ⟨%PB, Hwbm, %HBt, Hbs⟩
  generalize hN : ilog.length = N at *
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List Loc) (i : Int) => iprop(∃ (STi : GMap Loc WatcherSt)
      (Wsi : GMap Loc WatchRange) (PBv : GMap Loc (Loc × EventBatch)) (Out : GMap Loc (List EvM))
      (PBr : GMap Loc (Loc × EventBatch)) (ebv wv : Loc),
      "Hsynced" ∷ mvcc.ownWatcherGroup (mvcc.syncedAddr s) Wsi ∗
      "Hst" ∷ ([∗map] w ↦ st ∈ STi, mvcc.watcherOwn w st) ∗
      "Hmem" ∷ ([∗map] w ↦ st ∈ STi,
        mvcc.memberAt γ σ N keys i.toNat Out (GMap.fmap Prod.snd PBv) w st) ∗
      "Hvm" ∷ vm ↦$ GMap.fmap Prod.fst PBv ∗
      "Hbv" ∷ ([∗map] _w ↦ p ∈ PBv, ⌜p.1 ≠ null⌝ ∗ mvcc.ownEventBatch p.1 p.2) ∗
      "Hrem" ∷ ([∗map] _w ↦ p ∈ PBr, ⌜p.1 ≠ null⌝ ∗ mvcc.ownEventBatch p.1 p.2) ∗
      "eb" ∷ eb_ptr ↦ ebv ∗ "w" ∷ w_ptr ↦ wv ∗
      "s" ∷ s_ptr ↦ s ∗ "rev" ∷ rev_ptr ↦ W64 (N : Int) ∗ "victim" ∷ victim_ptr ↦ vm ∗
      "%Hi" ∷ ⌜0 ≤ i ∧ mvcc.NotifyRel σ N (mvcc.batchOf σ.Ws σ.ST evm) PB keys i.toNat STi Wsi
        (GMap.fmap Prod.snd PBv) Out PBr⌝)) $$ Hwbm
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [Hsynced Hst Hmem Hvm Hbs eb w s rev victim]
  · iexists σ.ST, σ.Ws, ∅, ∅, PB, zero_val Loc, zero_val Loc
    simp only [named, GMap.fmap_empty, show (0 : Int).toNat = 0 from rfl, List.take_zero]
    iframe Hsynced Hst Hvm eb w s rev victim Hbs
    isplitl [Hmem]
    · iapply (BigSepM.bigSepM_mono (fun {k v} _ => ?_)) $$ Hmem
      unfold mvcc.memberAt; simp
    isplitr
    · iapply BigSepM.bigSepM_empty.2; iempintro
    ipureintro
    refine ⟨Int.le_refl _, ⟨fun _ _ => rfl, fun k hk => by simp at hk, fun k => by simp,
      fun k B h => by simp at h, fun k => by simp, fun k => by simp, fun k hk => by simp at hk⟩⟩
  isplitr
  · imodintro
    iintro %i %key %v ⟨%Hkey, %Hv⟩ HP
    iNamed HP
    obtain ⟨hi0, Hrel⟩ := Hi
    rw [GMap.lookup_fmap] at Hv
    obtain ⟨⟨ebp, B⟩, hp, hvp⟩ : ∃ p, PB !! key = some p ∧ p.1 = v := by
      cases h : PB !! key with
      | none => rw [h] at Hv; cases Hv
      | some p => rw [h] at Hv; exact ⟨p, rfl, Option.some.inj Hv⟩
    simp only at hvp
    subst hvp
    have hBt : mvcc.batchOf σ.Ws σ.ST evm !! key = some B := by rw [HBt, GMap.lookup_fmap, hp]; rfl
    obtain ⟨r, stw, hWs, hST, hMB⟩ := mvcc.batchOf_some hBt
    have hnot : key ∉ keys.take i.toNat := by
      intro hm
      obtain ⟨j, hj, hjk⟩ := List.getElem_of_mem hm
      rw [List.getElem_take] at hjk
      have hj' : keys[j]? = some key := by
        rw [List.getElem?_eq_getElem (by simp at hj; omega)]; exact congrArg some hjk
      have := list_nodup_getElem?_inj keys Hknodup j i.toNat key hj' Hkey
      simp at hj; omega
    have hSTi : STi !! key = some stw := (Hrel.st_rest key hnot).trans hST
    have hPBr : PBr !! key = some (ebp, B) := by rw [Hrel.pbr, if_neg hnot, hp]
    have hBvk : GMap.fmap Prod.snd PBv !! key = none := by
      cases h : GMap.fmap Prod.snd PBv !! key with
      | none => rfl
      | some B' => exact absurd (Hrel.bv key B' h).1 hnot
    have hWsi : Wsi !! key = some r := by rw [Hrel.ws, hBvk]; exact hWs
    icases (BigSepM.bigSepM_delete hPBr).1 $$ Hrem with ⟨⟨%Hebnn, HB⟩, Hrem⟩
    icases (BigSepM.bigSepM_delete hSTi).1 $$ Hst with ⟨Hstw, Hst⟩
    icases (BigSepM.bigSepM_delete hSTi).1 $$ Hmem with ⟨Hmemw, Hmem⟩
    rw [mvcc.memberAt_rest γ σ N keys i.toNat Out _ key stw hnot]
    icases mvcc.memberRes_synced γ 1 σ key stw (by simp [hWs]) $$ Hmemw with
      ⟨%γw, %r', %fcs, %evsw, %d, %hM, #Hmeta, #Hfx, #Hch, #Hfo, %Hsr, %hE, Ha, Hl, %Hp, #Hwf⟩
    icases mvcc.ownWatcherGroup_member _ _ key r' fcs $$ [$Hsynced $Hfx] with ⟨Hsynced, %Hag⟩
    have hr : r' = r := by
      rw [hWsi] at Hag
      rcases Hag with h | h
      · cases h
      · exact (Option.some.inj h).symm
    subst hr
    have hbm := mvcc.batched_member σ ilog pend hne (by omega) Hok hLmu (by rw [hN]; exact hbelow)
      (by simp [hWs]) hM hE Hp.1 Hp.2 (by rw [hN, ← hevm]; exact hMB)
    rw [hN] at hbm
    obtain ⟨hminN, hloN, hdN, hwEne, hB⟩ := hbm
    iunfold mvcc.evsWf at Hwf
    icases Hwf with ⟨%L, #HlbL, %HL⟩
    rw [hdN] at HL
    ihave %Hcmp := mono_list_lb_valid _ _ _ $$ Hlb HlbL
    have hcmp := mvcc.histOf_cmp_log Hcmp
    have hevsw : evsw = mvcc.watchEvents (ilog ++ [pend]) r' γw.lo N := by
      rw [HL.1]
      exact mvcc.watchEvents_cmp hcmp.symm r' HL.2 (Or.inl (by simp; omega))
    have hnew : evsw ++ B.evs = mvcc.watchEvents (ilog ++ [pend]) r' γw.lo (N + 1) := by
      rw [hB, hevsw, ← hN]
      exact (mvcc.watchEvents_append _ _ (by omega) (by omega)).symm
    ihave #Hwf' : mvcc.evsWf γ r' γw.lo (evsw ++ B.evs) (N + 1) $$ []
    · iunfold mvcc.evsWf
      iexists ilog ++ [pend]
      iframe Hlb
      ipureintro; exact ⟨hnew, Or.inl (by simp; omega)⟩
    subst hB
    iunfold mvcc.ownEventBatch at HB
    icases HB with ⟨%sl, %ps, Heb, Hsl, Hcap, %Hlen, #HevB⟩
    iunfold mvcc.watcherOwn at Hstw
    icases Hstw with ⟨HminRev, Hvict, Hcomp, Hrest, Hchf⟩
    ihave #Hfx0 := Hfx
    iunfold mvcc.watcherFixed at Hfx0
    icases Hfx0 with ⟨%Hwnn, %ks, %es', #Hk, #Hks, #He, #Hes, #Hsr', #Hid, #Hfcs⟩
    simp only
    wp_auto
    have hmod : ∀ ev ∈ mvcc.watchEvents (ilog ++ [pend]) r' N (N + 1), ev.kv.modRev = W64 N := by
      rw [← hN]; exact mvcc.watchEvents_next_modRev ilog pend hne r'
    wp_apply (hSend γ key γw r' fcs stw.ch 1 (Qp.half 1) evsw (N + 1) _ ps
        (mvcc.watchEvents (ilog ++ [pend]) r' N (N + 1)) (DFrac.own 1))
      $$ [Hchf Hl Ha Hsl] as %b ⟨Hchf, Hl, Hsl, Ha⟩
    · rw [if_neg hwEne]
      simp only at Hlen
      iframe Hmeta Hfx Hfo Hch Hchf Hl Ha Hwf' Hsl HevB
      ipureintro
      refine ⟨Hlen, rfl, fun _ => rfl, ?_, ?_⟩
      · intro ev hev; rw [hmod ev hev]; exact Int.le_refl _
      · intro _ ev hev; rw [hmod ev hev]
        have : sint.Z (W64 (N : Int) : w64) = N := by word
        rw [this]; omega
    have hvic0 : stw.victim = false := by
      have h1 := (Hok.st_flags key stw hST).2.2.1 (Or.inl (by simp [hWs]))
      have h2 := Hok.ws_v key (by simp [hWs])
      rw [h2] at h1; simpa using h1
    have hlo1 : ∀ γw', σ.M !! key = some γw' → γw'.lo ≤ N + 1 := by
      intro γw' h; rw [hM] at h; cases h; omega
    have hPBv0 : PBv !! key = none := by
      rw [GMap.lookup_fmap] at hBvk
      cases h : PBv !! key with
      | none => rfl
      | some _ => rw [h] at hBvk; cases hBvk
    have hNN : (W64 (N : Int) : w64) + W64 1 = W64 ((N + 1 : Nat) : Int) := by
      rw [← mvcc.W64_add_one]; push_cast; rfl
    have hZ : sint.Z (W64 ((N + 1 : Nat) : Int) : w64) = N + 1 := by word
    have hi1 : (i + 1).toNat = i.toNat + 1 := by omega
    iunfold gaugeSpec at HgPS HgSS
    icases HgPS with ⟨-, -, #HgPA⟩
    icases HgSS with ⟨#HgSI, -, -⟩
    cases b
    · -- the channel is full: a victim
      simp only [if_neg hwEne, Bool.false_eq_true, ↓reduceIte]
      wp_auto
      wp_apply wp_mapInsert $$ Hvm as Hvm
      (try wp_auto)
      wp_apply (hDel (mvcc.syncedAddr s) Wsi key r' fcs) $$ [$Hsynced $Hfx] as Hsynced
      (try wp_auto)
      wp_apply HgSI
      (try wp_auto)
      rw [hNN]
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists <[key := { stw with minRev := W64 ((N + 1 : Nat) : Int), victim := true }]> STi,
        GMap.delete key Wsi, <[key := (ebp, mvcc.EventBatch.mk (mvcc.watchEvents (ilog ++ [pend]) r' N (N + 1)) (W64 1) (W64 0))]> PBv,
        <[key := evsw]> Out, GMap.delete key PBr, ebp, key
      simp only [named]
      rw [hi1, ← mvcc.std_delete_eq, GMap.fmap_insert, GMap.fmap_insert]
      iframe Hsynced Hvm Hrem eb w s rev victim
      isplitl [Hst HminRev Hvict Hcomp Hrest Hchf]
      · iapply (mvcc.bigSepM_step STi key _ (fun k v _ => .rfl)) $$ [$Hst HminRev Hvict Hcomp Hrest Hchf]
        iunfold mvcc.watcherOwn
        iframe
      isplitl [Hmem Ha Hl]
      · iapply (mvcc.bigSepM_step STi key _ (fun k v hk => by
          rw [mvcc.memberAt_succ_ne γ σ N keys i.toNat Out _ _ _ Hkey k hk
            (GMap.lookup_insert_ne _ _ (Ne.symm hk)) (GMap.lookup_insert_ne _ _ (Ne.symm hk))])) $$ [$Hmem Ha Hl]
        rw [mvcc.memberAt_succ_key γ σ N keys i.toNat _ _ Hkey, GMap.lookup_insert, GMap.lookup_insert]
        iunfold mvcc.memberDone
        iexists γw, r', fcs
        simp only [Option.getD_some, Option.map_some]
        iframe Hmeta Hfx Hch Hfo Ha Hl Hwf'
        ipureintro
        refine ⟨hM, Hsr, by rw [hZ]; omega, hZ⟩
      isplitl [Hbv Heb Hsl Hcap]
      · iapply (BigSepM.bigSepM_insert hPBv0).2
        iframe Hbv
        isplitr
        · ipureintro; exact Hebnn
        iunfold mvcc.ownEventBatch
        iexists sl, ps
        iframe Heb Hsl Hcap HevB
        ipureintro; exact Hlen
      ipureintro
      refine ⟨by omega, ?_⟩
      have := Hrel.step Hkey hnot hST hBt hBvk true evsw hlo1
      rw [mvcc.std_delete_eq]
      simpa using this
    · -- sent
      simp only [if_neg hwEne, ↓reduceIte]
      wp_auto
      wp_apply HgPA
      (try wp_auto)
      rw [hNN]
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists <[key := { stw with minRev := W64 ((N + 1 : Nat) : Int), victim := false }]> STi, Wsi,
        PBv, <[key := evsw ++ mvcc.watchEvents (ilog ++ [pend]) r' N (N + 1)]> Out,
        GMap.delete key PBr, ebp, key
      simp only [named]
      rw [hi1, ← mvcc.std_delete_eq]
      iframe Hsynced Hvm Hbv Hrem eb w s rev victim
      isplitl [Hst HminRev Hvict Hcomp Hrest Hchf]
      · iapply (mvcc.bigSepM_step STi key _ (fun k v _ => .rfl)) $$ [$Hst HminRev Hvict Hcomp Hrest Hchf]
        iunfold mvcc.watcherOwn
        rw [← hvic0]
        iframe
      isplitl [Hmem Ha Hl]
      · iapply (mvcc.bigSepM_step STi key _ (fun k v hk => by
          rw [mvcc.memberAt_succ_ne γ σ N keys i.toNat Out _ _ _ Hkey k hk
            (GMap.lookup_insert_ne _ _ (Ne.symm hk)) rfl])) $$ [$Hmem Ha Hl]
        rw [mvcc.memberAt_succ_key γ σ N keys i.toNat _ _ Hkey, GMap.lookup_insert, hBvk]
        iunfold mvcc.memberDone
        iexists γw, r', fcs
        simp only [Option.getD_some, Option.map_none, Option.getD_none, List.append_nil]
        iframe Hmeta Hfx Hch Hfo Ha Hl Hwf'
        ipureintro
        refine ⟨hM, Hsr, by rw [hZ]; omega, hZ⟩
      ipureintro
      refine ⟨by omega, ?_⟩
      have := Hrel.step Hkey hnot hST hBt hBvk false (evsw ++ mvcc.watchEvents (ilog ++ [pend]) r' N (N + 1)) hlo1
      rw [mvcc.std_delete_eq]
      simpa using this
  iintro HP Hwbm
  iNamed HP
  obtain ⟨hi0, Hrel⟩ := Hi
  have hsz : ((GMap.size (GMap.fmap Prod.fst PB) : Nat) : Int).toNat = keys.length := by
    rw [Hklen]; simp
  rw [hsz] at Hrel ⊢
  have hkeys : ∀ k, k ∈ keys ↔
      (mvcc.batchOf σ.Ws σ.ST (mvcc.evsOfRevM N (stateAfter ilog) pend) !! k).isSome := by
    intro k; rw [Hkset k, ← hevm, HBt, GMap.lookup_fmap, GMap.lookup_fmap]
    cases PB !! k <;> rfl
  rw [hevm] at Hrel
  wp_auto
  wp_apply +noauto (hAddV s st γ σ.vs σ.vbs vm (DFrac.own 1) (GMap.fmap Prod.fst PBv))
    $$ [$Hws $Hvf $Hvs $Hvcap $Hvm] as ⟨Hvm, %vs', Hvf, Hvs, Hvcap⟩
  have hsz2 : (GMap.fmap Prod.fst PBv).size = (GMap.fmap Prod.snd PBv).size := by
    rw [GMap.map_size_fmap, GMap.map_size_fmap]
  rw [hsz2]
  obtain ⟨hok', habove, -, -⟩ := mvcc.notify_final σ N (by rw [hLmu, hN]) Hok _
    (fun k h => by
      cases hb : mvcc.batchOf σ.Ws σ.ST (mvcc.evsOfRevM N (stateAfter ilog) pend) !! k with
      | none => rw [hb] at h; cases h
      | some B => obtain ⟨r, _, hW, -⟩ := mvcc.batchOf_some hb; rw [hW]; rfl)
    PB keys hkeys STi Wsi (GMap.fmap Prod.snd PBv) Out PBr Hrel vs' vm
  icases mvcc.ownWatcherGroup_fixed _ _ $$ Hsynced with ⟨Hsynced, #Hfxs⟩
  ihave Hmem' : ([∗map] k ↦ x ∈ STi,
      mvcc.memberRes γ 1 (mvcc.notifyState σ N STi Wsi (GMap.fmap Prod.snd PBv) Out vs' vm) k x) $$ [Hmem]
  · iapply (BigSepM.bigSepM_impl (Ψ := fun k x =>
      mvcc.memberRes γ 1 (mvcc.notifyState σ N STi Wsi (GMap.fmap Prod.snd PBv) Out vs' vm) k x)) $$ Hmem
    imodintro
    iintro %k %v %hkv Hm
    iapply (mvcc.memberRes_final γ σ ilog pend N hN hLmu hne hlen Hok hbelow keys PB STi Wsi
      (GMap.fmap Prod.snd PBv) Out PBr hkeys Hrel vs' vm k v (by simpa [gmap_get?_eq] using hkv))
    iframe Hm Hlb Hfxs
  imod ghostVar_update (mvcc.notifyState σ N STi Wsi (GMap.fmap Prod.snd PBv) Out vs' vm)
    γ.wst σ $$ Hσ with Hσ
  (try wp_auto)
  iapply HΦ
  iframe Hevs
  iexists mvcc.notifyState σ N STi Wsi (GMap.fmap Prod.snd PBv) Out vs' vm
  isplitl
  · iunfold mvcc.watchStoreBody
    have e1 : (mvcc.notifyState σ N STi Wsi (GMap.fmap Prod.snd PBv) Out vs' vm).Lmu = σ.Lmu := rfl
    have e2 : (mvcc.notifyState σ N STi Wsi (GMap.fmap Prod.snd PBv) Out vs' vm).Ws = Wsi := rfl
    have e3 : (mvcc.notifyState σ N STi Wsi (GMap.fmap Prod.snd PBv) Out vs' vm).Wu = σ.Wu := rfl
    have e4 : (mvcc.notifyState σ N STi Wsi (GMap.fmap Prod.snd PBv) Out vs' vm).vs = vs' := rfl
    have e5 : (mvcc.notifyState σ N STi Wsi (GMap.fmap Prod.snd PBv) Out vs' vm).vbs =
        if (GMap.fmap Prod.snd PBv).size = 0 then σ.vbs else σ.vbs ++ [vm] := rfl
    have e6 : (mvcc.notifyState σ N STi Wsi (GMap.fmap Prod.snd PBv) Out vs' vm).VB =
        if (GMap.fmap Prod.snd PBv).size = 0 then σ.VB else σ.VB ++ [GMap.fmap Prod.snd PBv] := rfl
    have e7 : (mvcc.notifyState σ N STi Wsi (GMap.fmap Prod.snd PBv) Out vs' vm).ST = STi := rfl
    have e8 : (mvcc.notifyState σ N STi Wsi (GMap.fmap Prod.snd PBv) Out vs' vm).Wo = σ.Wo := rfl
    have e9 : (mvcc.notifyState σ N STi Wsi (GMap.fmap Prod.snd PBv) Out vs' vm).M = σ.M := rfl
    have eo : ∀ w st, mvcc.outRes (GF := GF) γ
        (mvcc.notifyState σ N STi Wsi (GMap.fmap Prod.snd PBv) Out vs' vm) w st =
        mvcc.outRes γ σ w st := fun _ _ => rfl
    simp only [e1, e2, e3, e4, e5, e6, e7, e8, e9, eo, named]
    iframe Hσ Hwlog Hcert Hsynced Hunsynced Hvf Hvs Hvcap Hst Hwo Hmeta Hmfix Hmem' Hout
    by_cases h0 : (GMap.fmap Prod.snd PBv).size = 0
    · simp only [h0, ↓reduceIte]
      iframe Hvbs
      ipureintro; exact ⟨Hvlen, hok'⟩
    · simp only [h0, ↓reduceIte]
      rw [List.zip_append Hvlen]
      isplitr
      · ipureintro; simp [Hvlen]
      isplitl [Hvbs Hbv Hvm]
      · iapply BigSepL.bigSepL_append.2
        iframe Hvbs
        simp only [List.zip_cons_cons, List.zip_nil_right]
        iapply BigSepL.bigSepL_singleton.2
        iunfold mvcc.ownWatcherBatch
        iexists PBv
        iframe Hvm Hbv
        ipureintro; rfl
      ipureintro; exact hok'
  ipureintro
  exact ⟨hLmu, habove⟩

end proof
end EtcdGrove
end Perennial
