/-
The tester's watch check against mvcc's watch model (pure; `notes/mvccfull-proof-plan.md`).
Lean-first (no Rocq counterpart); mvccrand's (`WatchModel.lean` there), over a key list `ks` and
with the watchers' filters. (mvccrand's imported its `World`, for `revOk` and `histOkM` alone: they
are pure, and here.)

**What a watcher expects** (`expChs Hl mt lo hi`): the changes of the history's revisions `[lo, hi)`
the watcher matches (`mt : change → Bool`: for mvccfull's watchers `matchesM`, the range and the
filter, `watcher.matches`), each with its revision, in order (`rangeChs`: one revision's). The
event mvcc makes of a change at revision `r` is `chEv r` (a put: its record's key-value,
`kvOfRec`; a delete: the key alone at modification revision `r`, every other field zero, as
`evOfKv` makes of `changeKv`'s `zeroKv`).

**The correspondence** (`watchEvents_eq_expChs`): under the invariant's `histOkM ks σ Hl` (every
revision of the notified log is the history's, its changes `pendOf`'s of the log's), mvcc's
`watchEvents σ.notifiedLog (watchRangeOf kk e endk s id) lo hi`, through which `wsRecvOk` states
what a stream delivers, is `(expChs Hl (inRangeM … ·.key') lo hi).map chEv`; filtered by the
watcher's filter predicates (`filterFs f`, what `stream.watch` registers for the filter `f`), it is
`(expChs Hl (matchesM f …) lo hi).map chEv` (`watchEvents_filtered_eq_expChs`). The heart is one
revision (`evsOfRevM_pendOf`): the events of mvcc's changes `cs` from the state `s` are the events
of the tester's changes `(pendOf M r cs).chs` when `M` has `s`'s key-values (`fkMatch`, `stMatch`'s
first part), by induction on the changes.

**The position of a watcher** (`watcher.rev`, `watcher.index`: the next event is the `index`-th
matching change of revision `rev`). `posOk Hl mt lo rev index n`: after `n` received events of a
watcher registered from `lo`, `rev ≥ lo`, `index` at most the number of matching changes of `rev`,
and the expected changes before `rev` plus `index` are `n`. It holds at registration
(`posOk_start`). `expect(w, upto)` returns `expNext Hl mt rev index upto`, which under `posOk` is
the `n`-th expected change up to `upto` (`expNext_eq_get`); `receive`'s update of the position
after it (`advW`, inline in mvccfull's `receive`; mvccrand's `advance`) keeps `posOk` at `n + 1`
(`posOk_advW`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.History
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.WriteModel
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.HistoryLaws
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.watcher__matches

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section model
variable [GooseExts]

/-! ## The tester's expected changes -/

/-- The changes of revision `r` of `Hl` the watcher matches (`mt`), in order. -/
def rangeChs (Hl : List HRev) (mt : change → Bool) (r : Nat) : List change :=
  ((Hl[r]?.map Prod.snd).getD []).filter fun ch => mt ch

/-- **A watcher's expected changes**: those of the revisions `[lo, hi)` in its range, each with its
revision, in order. -/
def expChs (Hl : List HRev) (mt : change → Bool) (lo hi : Nat) : List (Nat × change) :=
  ((List.range' lo (hi - lo)).map fun r => (rangeChs Hl mt r).map fun ch => (r, ch)).flatten

/-- **The event mvcc makes of the change `ch` at revision `r`**: a put's record as a key-value, a
delete's key alone at modification revision `r`. -/
def chEv (r : Nat) (ch : change) : EvM :=
  if ch.del' then ⟨true, { zeroKv ch.key' with modRev := W64 r }, none⟩
  else ⟨false, kvOfRec ch.key' ch.kv', none⟩

theorem chEv_key (r : Nat) (ch : change) : (chEv r ch).kv.key = ch.key' := by
  unfold chEv; split <;> rfl

theorem chEv_del (r : Nat) (ch : change) : (chEv r ch).del = ch.del' := by
  unfold chEv; split <;> simp_all

theorem expChs_empty (Hl : List HRev) (mt : change → Bool) {lo hi : Nat} (h : hi ≤ lo) :
    expChs Hl mt lo hi = [] := by
  unfold expChs; rw [show hi - lo = 0 by omega]; rfl

theorem expChs_append (Hl : List HRev) (mt : change → Bool) {lo mid hi : Nat} (h1 : lo ≤ mid)
    (h2 : mid ≤ hi) : expChs Hl mt lo hi = expChs Hl mt lo mid ++ expChs Hl mt mid hi := by
  unfold expChs
  rw [← List.flatten_append, ← List.map_append]
  congr 2
  rw [show hi - lo = (mid - lo) + (hi - mid) by omega, ← List.range'_append_1,
    show lo + (mid - lo) = mid by omega]

theorem expChs_cons (Hl : List HRev) (mt : change → Bool) {lo hi : Nat} (h : lo < hi) :
    expChs Hl mt lo hi = (rangeChs Hl mt lo).map (fun ch => (lo, ch)) ++ expChs Hl mt (lo + 1) hi := by
  rw [expChs_append Hl mt (Nat.le_succ lo) (by omega : lo + 1 ≤ hi)]
  congr 1
  unfold expChs
  rw [show lo + 1 - lo = 1 by omega]
  simp

theorem mem_expChs {Hl : List HRev} {mt : change → Bool} {lo hi : Nat} {p : Nat × change}
    (h : p ∈ expChs Hl mt lo hi) : lo ≤ p.1 ∧ p.1 < hi ∧ p.2 ∈ rangeChs Hl mt p.1 := by
  unfold expChs at h
  obtain ⟨l, hl, hp⟩ := List.mem_flatten.1 h
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hl
  obtain ⟨ch, hch, rfl⟩ := List.mem_map.1 hp
  rw [List.mem_range'_1] at hr
  exact ⟨hr.1, by omega, hch⟩

/-- The history's revisions below `hi` fix the expected changes below `hi`. -/
theorem expChs_prefix {Hl Hl' : List HRev} (hp : Hl <+: Hl') (mt : change → Bool) {lo hi : Nat}
    (hhi : hi ≤ Hl.length) : expChs Hl mt lo hi = expChs Hl' mt lo hi := by
  unfold expChs
  congr 1
  apply List.map_congr_left
  intro r hr
  rw [List.mem_range'_1] at hr
  unfold rangeChs
  obtain ⟨T, rfl⟩ := hp
  rw [List.getElem?_append_left (by omega)]

/-- An expected change at position `n` of `[lo, hi)` is one of `[lo, r + 1)` (revisions increase). -/
theorem expChs_getElem_cut {Hl : List HRev} {mt : change → Bool} {lo hi n r : Nat}
    {ch : change} (h : (expChs Hl mt lo hi)[n]? = some (r, ch)) :
    (expChs Hl mt lo (r + 1))[n]? = some (r, ch) := by
  have hm := mem_expChs (List.mem_of_getElem? h)
  simp only at hm
  rw [expChs_append Hl mt (show lo ≤ r + 1 by omega) (show r + 1 ≤ hi by omega)] at h
  by_cases hn : n < (expChs Hl mt lo (r + 1)).length
  · rw [List.getElem?_append_left hn] at h; exact h
  · rw [List.getElem?_append_right (by omega)] at h
    have := mem_expChs (List.mem_of_getElem? h)
    simp only at this; omega

/-! ## One revision: mvcc's events of its changes are the tester's -/

/-- The tester's map has the store's key-values (`stMatch`'s first part). -/
def fkMatch (M : GMap GoString kvRec) (s : List EtcdKv) : Prop :=
  ∀ k, findKey k s = (M !! k).map (kvOfRec k)

theorem fkMatch_put (M : GMap GoString kvRec) (s : List EtcdKv) (hs : s.Pairwise etcdKvLess)
    (r : w64) (k v : GoString) (l : w64) (hM : fkMatch M s) :
    fkMatch (<[k := putRec M r k v l]> M) (applyChange r s (.put k v l)) := by
  intro x
  simp only [applyChange]
  by_cases hx : x = k
  · subst hx
    rw [findKey_putKv_self_eq hs, GMap.lookup_insert, hM x]
    unfold putRec
    cases M !! x <;> rfl
  · rw [findKey_putKv_other hs r x k v l (Ne.symm hx), GMap.lookup_insert_ne _ _ (Ne.symm hx)]
    exact hM x

theorem fkMatch_del (M : GMap GoString kvRec) (s : List EtcdKv) (r : w64) (k : GoString)
    (hM : fkMatch M s) : fkMatch (GMap.delete k M) (applyChange r s (.del k)) := by
  intro x
  simp only [applyChange]
  by_cases hx : x = k
  · subst hx; rw [findKey_filter_eq]; simp
  · rw [findKey_filter_ne s k x hx, GMap.lookup_delete_ne _ (Ne.symm hx)]; exact hM x

theorem fkMatch_step (P : PendM) (s : List EtcdKv) (hs : s.Pairwise etcdKvLess)
    (hM : fkMatch P.st s) (c : Change) : fkMatch (P.step c).st (applyChange P.rev s c) := by
  cases c with
  | put k v l => exact fkMatch_put P.st s hs P.rev k v l hM
  | del k => exact fkMatch_del P.st s P.rev k hM

theorem fkMatch_foldl (cs : List Change) :
    ∀ (P : PendM) (s : List EtcdKv), s.Pairwise etcdKvLess → fkMatch P.st s →
      fkMatch (cs.foldl PendM.step P).st (cs.foldl (applyChange P.rev) s) := by
  induction cs with
  | nil => intro P s _ h; exact h
  | cons c cs ih =>
    intro P s hs hM
    simp only [List.foldl_cons]
    have hrev : (P.step c).rev = P.rev := by cases c <;> rfl
    have := ih (P.step c) (applyChange P.rev s c) (applyChange_sorted hs P.rev c)
      (fkMatch_step P s hs hM c)
    rw [hrev] at this
    exact this

theorem fkMatch_pendOf (M : GMap GoString kvRec) (rev : w64) (s : List EtcdKv)
    (hs : s.Pairwise etcdKvLess) (hM : fkMatch M s) (cs : List Change) :
    fkMatch (pendOf M rev cs).st (applyChanges rev s cs) :=
  fkMatch_foldl cs ⟨rev, M, []⟩ s hs hM

theorem changeKv_append_lt (r : w64) (s : List EtcdKv) (cs cs' : List Change) (i : Nat)
    (hi : i < cs.length) : changeKv r s (cs ++ cs') i = changeKv r s cs i := by
  unfold changeKv
  rw [List.getElem?_append_left hi, List.take_append_of_le_length (by omega)]

theorem changeKv_last (r : w64) (s : List EtcdKv) (cs : List Change) (c : Change) :
    changeKv r s (cs ++ [c]) cs.length = match c with
      | .put k _ _ => findKey k (applyChange r (applyChanges r s cs) c)
      | .del k => some (zeroKv k) := by
  unfold changeKv
  rw [List.getElem?_concat_length, List.take_of_length_le (by simp),
    applyChanges_append_singleton]
  cases c <;> rfl

theorem filterMap_congr' {α β : Type} {f g : α → Option β} :
    ∀ {l : List α}, (∀ x ∈ l, f x = g x) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | a :: l, h => by
    rw [List.filterMap_cons, List.filterMap_cons, h a List.mem_cons_self,
      filterMap_congr' (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem evsOfRevM_snoc (r : Nat) (s : List EtcdKv) (cs : List Change) (c : Change) :
    evsOfRevM r s (cs ++ [c]) =
      evsOfRevM r s cs ++ ((changeKv (W64 r) s (cs ++ [c]) cs.length).map (evOfKv r)).toList := by
  unfold evsOfRevM
  rw [List.length_append, List.length_singleton, List.range_succ, List.filterMap_append]
  congr 1
  · apply filterMap_congr'
    intro i hi
    rw [List.mem_range] at hi
    rw [changeKv_append_lt _ _ _ _ _ hi]

theorem mem_pendOf_chs_mod (M : GMap GoString kvRec) (rev : w64) (cs : List Change) :
    ∀ ch ∈ (pendOf M rev cs).chs, ch.del' = false → ch.kv'.mod' = rev := by
  obtain ⟨rs, rfl⟩ : ∃ rs, cs = rs.reverse := ⟨cs.reverse, (List.reverse_reverse cs).symm⟩
  induction rs with
  | nil => intro ch h; rw [List.reverse_nil, pendOf_nil] at h; exact absurd h List.not_mem_nil
  | cons c rs ih =>
    rw [List.reverse_cons]
    generalize rs.reverse = cs at ih ⊢
    intro ch hch hd
    rw [pendOf_append] at hch
    simp only [List.foldl_cons, List.foldl_nil] at hch
    have hr := pendOf_rev M rev cs
    cases c with
    | put k v l =>
      simp only [PendM.step, PendM.put, List.mem_append, List.mem_singleton] at hch
      rcases hch with h | rfl
      · exact ih ch h hd
      · simp only [putRec, hr]; split <;> rfl
    | del k =>
      simp only [PendM.step, PendM.delOne, List.mem_append, List.mem_singleton] at hch
      rcases hch with h | rfl
      · exact ih ch h hd
      · simp [delChange] at hd

theorem w64_ne_zero_of (r : Nat) (h1 : 1 ≤ r) (h2 : r < 2 ^ 63) : (W64 (r : Int)) ≠ W64 0 := by
  intro h
  have := congrArg (fun x : w64 => uint.nat x) h
  rw [txn.hl_nat_W64 r h2] at this
  have h0 : uint.nat (W64 0) = 0 := rfl
  omega

/-- **One revision**: mvcc's events of the changes `cs` of revision `r` from the state `s` are the
events of the tester's changes, when the tester's map `M` has `s`'s key-values (and `s`'s create
revisions are not zero, as a reachable log's are). -/
theorem evsOfRevM_pendOf (r : Nat) (hr1 : 1 ≤ r) (hr : r < 2 ^ 63) (M : GMap GoString kvRec)
    (s : List EtcdKv) (hs : s.Pairwise etcdKvLess) (hpos : ∀ v ∈ s, v.createRev ≠ W64 0)
    (hM : fkMatch M s) (cs : List Change) :
    evsOfRevM r s cs = (pendOf M (W64 r) cs).chs.map (chEv r) := by
  have hr0 := w64_ne_zero_of r hr1 hr
  obtain ⟨rs, rfl⟩ : ∃ rs, cs = rs.reverse := ⟨cs.reverse, (List.reverse_reverse cs).symm⟩
  induction rs with
  | nil => rfl
  | cons c rs ih =>
    rw [List.reverse_cons]
    generalize rs.reverse = cs at ih ⊢
    rw [evsOfRevM_snoc, ih, changeKv_last, pendOf_append]
    simp only [List.foldl_cons, List.foldl_nil]
    have hP := fkMatch_pendOf M (W64 r) s hs hM cs
    have hPr := pendOf_rev M (W64 r) cs
    have hpos' : ∀ v ∈ applyChanges (W64 r) s cs, v.createRev ≠ W64 0 := by
      intro v hv
      by_cases hc : v.createRev = W64 r
      · rw [hc]; exact hr0
      · obtain ⟨w, hw, -, hwc⟩ := txn.mem_applyChanges_createRev cs s v hv hc
        rw [← hwc]; exact hpos w hw
    cases c with
    | put k v l =>
      have hf := fkMatch_put _ _ (applyChanges_sorted (W64 r) cs hs) (W64 r) k v l hP k
      rw [GMap.lookup_insert] at hf
      simp only [hf, Option.map_some, Option.toList_some, PendM.step, PendM.put, List.map_append,
        List.map_cons, List.map_nil, hPr]
      congr 2
      have hcr : (putRec (pendOf M (W64 r) cs).st (W64 r) k v l).create' ≠ W64 0 := by
        unfold putRec
        cases hk : (pendOf M (W64 r) cs).st !! k with
        | none => exact hr0
        | some e =>
          have hfk := hP k
          rw [hk] at hfk
          exact hpos' _ (List.mem_of_find?_eq_some hfk)
      unfold evOfKv chEv
      simp only [Bool.false_eq_true, ↓reduceIte, kvOfRec] at hcr ⊢
      simp only [hcr, ↓reduceIte]
    | del k =>
      simp only [Option.map_some, Option.toList_some, PendM.step, PendM.delOne, List.map_append,
        List.map_cons, List.map_nil]
      unfold evOfKv chEv delChange zeroKv
      simp

/-! ## The log's events: the correspondence -/

theorem stateAt_createRev_ne (L : Log) (h0 : L[0]? = some []) (hlen : L.length < 2 ^ 63) :
    ∀ r, r < L.length → ∀ v ∈ stateAt L r, v.createRev ≠ W64 0
  | 0, _, v, hv => by rw [txn.stateAt_zero_nil L h0] at hv; exact absurd hv List.not_mem_nil
  | j + 1, hr, v, hv => by
    rw [txn.stateAt_succ L j hr] at hv
    by_cases hc : v.createRev = W64 ((j + 1 : Nat) : Int)
    · rw [hc]; exact w64_ne_zero_of (j + 1) (by omega) (by omega)
    · obtain ⟨w, hw, -, hwc⟩ := txn.mem_applyChanges_createRev _ _ v hv hc
      rw [← hwc]
      exact stateAt_createRev_ne L h0 hlen j (by omega) w hw

/-- **A revision `e` of the history `Hs` is the log `L`'s revision `r`** (over the keys `ks`): its
state is the store's at `r`, and past revision `0` it is the tester's model (`pendOf`) of the log's
changes of `r` from the revision before (so its changes are what a watcher of the revision
expects). -/
def revOk (ks : List GoString) (L : Log) (Hs : List HRev) (r : Nat) (e : HRev) : Prop :=
  stMatch ks e.1 (stateAt L r) ∧
  (1 ≤ r → ∃ e', Hs[r - 1]? = some e' ∧
    e = ((pendOf e'.1 (W64 (r : Int)) (L.getD r [])).st, (pendOf e'.1 (W64 (r : Int)) (L.getD r [])).chs))

/-- **The history covers the notified history** (the store's and the streams'): every revision of
`σ.notifiedLog` is in `Hl`, the log's revision. -/
def histOkM (ks : List GoString) (σ : MvccState) (Hl : List HRev) : Prop :=
  σ.notifiedLog.length ≤ Hl.length ∧
  ∀ r < σ.notifiedLog.length, ∃ e, Hl[r]? = some e ∧ revOk ks σ.notifiedLog Hl r e

/-- Every revision of `L` is the history's (`histOkM`'s second part, for any log). -/
abbrev HistRevs (ks : List GoString) (L : Log) (Hl : List HRev) : Prop :=
  ∀ r < L.length, ∃ e, Hl[r]? = some e ∧ revOk ks L Hl r e

/-- The events of a revision `m ≥ 1` of the log are the tester's of its changes. -/
theorem evsOfRev_hist (ks : List GoString) (L : Log) (Hl : List HRev) (hrev : HistRevs ks L Hl)
    (h0 : L[0]? = some []) (hlen : L.length < 2 ^ 63) (m : Nat) (hm1 : 1 ≤ m) (hm : m < L.length) :
    evsOfRevM m (stateAt L (m - 1)) (L.getD m []) =
      ((Hl[m]?.map Prod.snd).getD []).map (chEv m) := by
  obtain ⟨e, he, hok⟩ := hrev m hm
  obtain ⟨e', he', rfl⟩ := hok.2 hm1
  obtain ⟨e'', he'', hok'⟩ := hrev (m - 1) (by omega)
  rw [he'] at he''
  cases he''
  rw [he]
  simp only [Option.map_some, Option.getD_some]
  exact evsOfRevM_pendOf m hm1 (by omega) e'.1 _ (stateAt_sorted L (m - 1))
    (stateAt_createRev_ne L h0 hlen (m - 1) (by omega)) hok'.1.1 _

theorem watchEvents_hist (ks : List GoString) (L : Log) (Hl : List HRev) (hrev : HistRevs ks L Hl)
    (h0 : L[0]? = some []) (hlen : L.length < 2 ^ 63) (rg : WatchRange) (inR : GoString → Bool)
    (hcov : ∀ k, rg.covers k = inR k) (lo hi : Nat) (hlo : 1 ≤ lo) (hhi : hi ≤ L.length) :
    watchEvents L rg lo hi = (expChs Hl (fun ch => inR ch.key') lo hi).map fun p => chEv p.1 p.2 := by
  unfold watchEvents logEvents expChs
  rw [List.filter_flatten, List.map_flatten, List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro m hm
  rw [List.mem_range'_1] at hm
  simp only [Function.comp_apply]
  rw [evsOfRev_hist ks L Hl hrev h0 hlen m (by omega) (by omega), List.filter_map, List.map_map]
  unfold rangeChs
  congr 1
  apply List.filter_congr
  intro ch _
  simp only [Function.comp_apply, chEv_key, hcov]

/-- `covers_eq_inRangeM` for every key (the empty key is in neither range). -/
theorem covers_eq_inRangeM' (kk e : GoString) (endk : GoSlice) (s id : w64) (k : GoString)
    (hkk : kk ≠ []) :
    (watchRangeOf kk e endk s id).covers k = inRangeM (decide (endk = slice.nil)) kk e k := by
  by_cases hk : k = []
  · subst hk
    obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hkk
    have hlt := go.goStringLt_nil_cons x xs
    unfold watchRangeOf WatchRange.covers inRangeM
    by_cases hn : endk = slice.nil
    · simp [hn]
    · simp only [hn, ↓reduceIte]
      have h1 : ¬ adt.affCmp [] e < 0 := by rw [adt.affCmp_neg_iff]; exact fun h => h.1 rfl
      simp [h1, mvcc.inRange, hlt]
  · exact covers_eq_inRangeM kk e endk s id k hk hkk

/-- **The correspondence**: what mvcc's watch guarantee says a watcher of the stream receives (the
range's events of the notified log at revisions `[lo, hi)`) is the tester's expected changes of the
history, made events. -/
theorem watchEvents_eq_expChs (ks : List GoString) (σ : MvccState) (Hl : List HRev)
    (hok : histOkM ks σ Hl)
    (hwf : LogWf' σ.notifiedLog) (hlen : σ.notifiedLog.length < 2 ^ 63)
    (kk e : GoString) (endk : GoSlice) (s id : w64) (hkk : kk ≠ []) (lo hi : Nat) (hlo : 1 ≤ lo)
    (hhi : hi ≤ σ.notifiedLog.length) :
    watchEvents σ.notifiedLog (watchRangeOf kk e endk s id) lo hi =
      (expChs Hl (fun ch => inRangeM (decide (endk = slice.nil)) kk e ch.key') lo hi).map
        fun p => chEv p.1 p.2 := by
  by_cases hle : hi ≤ lo
  · rw [watchEvents_empty _ _ hle, expChs_empty _ _ hle]; rfl
  have hne : σ.notifiedLog ≠ [] := by intro h; rw [h] at hhi; simp at hhi; omega
  exact watchEvents_hist ks σ.notifiedLog Hl hok.2 (hwf.1 hne) hlen _ _
    (fun k => covers_eq_inRangeM' kk e endk s id k hkk) lo hi hlo hhi

/-! ## The watchers' filters -/

/-- **The filter predicates `stream.watch` registers for the tester's filter `f`** (a predicate
drops the events it holds of: `1`, the watch server's NoPut, drops the puts; `2`, NoDelete, the
deletes; any other none). -/
def filterFs (f : w64) : List (EvM → Bool) :=
  if f = W64 1 then [fun ev => !ev.del] else if f = W64 2 then [fun ev => ev.del] else []

theorem filtered_filterFs (f : w64) (ps : List (Nat × change)) :
    filtered (filterFs f) (ps.map fun p => chEv p.1 p.2) =
      (ps.filter fun p => filtOk f p.2.del').map fun p => chEv p.1 p.2 := by
  unfold filtered
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro p _
  simp only [Function.comp_apply, filterFs, filtOk]
  by_cases h1 : f = W64 1
  · simp only [h1, ↓reduceIte]
    cases hd : p.2.del' <;> simp [chEv_del, hd]
  · simp only [h1, ↓reduceIte]
    by_cases h2 : f = W64 2
    · simp only [h2, ↓reduceIte]
      cases hd : p.2.del' <;> simp [chEv_del, hd]
    · simp only [h2, ↓reduceIte]
      cases hd : p.2.del' <;> simp <;> assumption

theorem expChs_filter (Hl : List HRev) (mt g : change → Bool) (lo hi : Nat) :
    (expChs Hl mt lo hi).filter (fun p => g p.2) = expChs Hl (fun ch => mt ch && g ch) lo hi := by
  unfold expChs rangeChs
  rw [List.filter_flatten, List.map_map]
  congr 1
  apply List.map_congr_left
  intro r _
  simp only [Function.comp_apply, List.filter_map, List.filter_filter]
  congr 1
  apply List.filter_congr
  intro ch _
  simp [Bool.and_comm]

/-- **The correspondence, filtered**: what a watcher registered with `filterFs f` receives is the
expected changes it matches (`matchesM`, `watcher.matches`), made events. -/
theorem watchEvents_filtered_eq_expChs (ks : List GoString) (σ : MvccState) (Hl : List HRev)
    (hok : histOkM ks σ Hl)
    (hwf : LogWf' σ.notifiedLog) (hlen : σ.notifiedLog.length < 2 ^ 63) (f : w64)
    (kk e : GoString) (endk : GoSlice) (s id : w64) (hkk : kk ≠ []) (lo hi : Nat) (hlo : 1 ≤ lo)
    (hhi : hi ≤ σ.notifiedLog.length) :
    filtered (filterFs f) (watchEvents σ.notifiedLog (watchRangeOf kk e endk s id) lo hi) =
      (expChs Hl (matchesM f (decide (endk = slice.nil)) kk e) lo hi).map
        fun p => chEv p.1 p.2 := by
  rw [watchEvents_eq_expChs ks σ Hl hok hwf hlen kk e endk s id hkk lo hi hlo hhi,
    filtered_filterFs, expChs_filter Hl _ (fun ch => filtOk f ch.del')]
  rfl

/-- An expected change's event is at its revision. -/
theorem chEv_modRev (ks : List GoString) (L : Log) (Hl : List HRev) (hrev : HistRevs ks L Hl)
    (mt : change → Bool) (lo hi : Nat) (hlo : 1 ≤ lo) (hhi : hi ≤ L.length) (p : Nat × change)
    (hp : p ∈ expChs Hl mt lo hi) : (chEv p.1 p.2).kv.modRev = W64 p.1 := by
  obtain ⟨h1, h2, h3⟩ := mem_expChs hp
  unfold chEv
  split
  · rfl
  · rename_i hd
    simp only [Bool.not_eq_true] at hd
    obtain ⟨e, he, hok⟩ := hrev p.1 (by omega)
    obtain ⟨e', -, rfl⟩ := hok.2 (by omega)
    unfold rangeChs at h3
    rw [he] at h3
    simp only [Option.map_some, Option.getD_some] at h3
    exact mem_pendOf_chs_mod _ _ _ p.2 (List.mem_filter.1 h3).1 hd

theorem filtered_nil (evs : List EvM) : filtered [] evs = evs := by
  unfold filtered; simp

/-! ## A watcher's position and `expect` -/

/-- **What `expect(w, upto)` returns** for a watcher at position (`rev`, `index`): the `index`-th
in-range change of revision `rev`, else the first in-range change of a later revision, up to
`upto`. -/
def expNext (Hl : List HRev) (mt : change → Bool) (rev index : Nat) (upto : Int) :
    Option (Nat × change) :=
  if upto < rev then none
  else ((((rangeChs Hl mt rev).drop index).map fun ch => (rev, ch)) ++
    expChs Hl mt (rev + 1) (upto.toNat + 1)).head?

/-- **`expect`'s result** `(ch, r, ok)` for a watcher at (`rev`, `index`): `expNext`'s change and
revision (with the bound on its revision's in-range changes, which `advance` needs: they are a Go
slice's), or `ok = false` when there is none. -/
def expRes (Hl : List HRev) (mt : change → Bool) (rev index : Nat) (upto : Int) (ch : change)
    (r : w64) (ok : Bool) : Prop :=
  match expNext Hl mt rev index upto with
  | some (r', ch') => ok = true ∧ ch = ch' ∧ r = W64 (r' : Int) ∧ (rangeChs Hl mt r').length < 2 ^ 63
  | none => ok = false

/-! ### `expect`'s loops -/

/-- The in-range changes `expect` skips at revision `r`: the watcher's index at its revision. -/
def expSkip (rev index r : Nat) : Nat := if r = rev then index else 0

/-- What is left for `expect` at revision `r` (nothing returned before it): `r`'s in-range changes
past the skipped ones, then the later revisions' up to `upto`. -/
def expRem (Hl : List HRev) (mt : change → Bool) (rev index : Nat) (upto : Int) (r : Nat) :
    List (Nat × change) :=
  if (r : Int) ≤ upto then
    (((rangeChs Hl mt r).drop (expSkip rev index r)).map fun ch => (r, ch)) ++
      expChs Hl mt (r + 1) (upto.toNat + 1)
  else []

theorem expNext_eq_rem (Hl : List HRev) (mt : change → Bool) (rev index : Nat) (upto : Int) :
    expNext Hl mt rev index upto = (expRem Hl mt rev index upto rev).head? := by
  unfold expNext expRem expSkip
  by_cases h : upto < rev
  · simp only [h, ↓reduceIte, show ¬ (rev : Int) ≤ upto by omega, List.head?_nil]
  · simp only [h, ↓reduceIte, show (rev : Int) ≤ upto by omega]

theorem expRem_step (Hl : List HRev) (mt : change → Bool) (rev index : Nat) (upto : Int)
    (r : Nat) (hrv : rev ≤ r) (hr : (r : Int) ≤ upto)
    (hd : (rangeChs Hl mt r).drop (expSkip rev index r) = []) :
    expRem Hl mt rev index upto r = expRem Hl mt rev index upto (r + 1) := by
  have hs : expSkip rev index (r + 1) = 0 := by
    unfold expSkip; simp only [show r + 1 ≠ rev by omega, ↓reduceIte]
  unfold expRem
  simp only [hr, ↓reduceIte, hd, List.map_nil, List.nil_append]
  by_cases h2 : ((r + 1 : Nat) : Int) ≤ upto
  · simp only [h2, ↓reduceIte, hs, List.drop_zero]
    exact expChs_cons Hl mt (by omega)
  · simp only [h2, ↓reduceIte]
    exact expChs_empty Hl mt (by omega)

theorem expRem_end (Hl : List HRev) (mt : change → Bool) (rev index : Nat) (upto : Int)
    (r : Nat) (h : upto < (r : Int)) : expRem Hl mt rev index upto r = [] := by
  unfold expRem; simp only [show ¬ (r : Int) ≤ upto by omega, ↓reduceIte]

theorem drop_filter_take {α : Type} (l : List α) (p : α → Bool) (j : Nat) :
    (l.filter p).drop ((l.take j).filter p).length = (l.drop j).filter p := by
  have h : (l.filter p).drop ((l.take j).filter p).length =
      ((l.take j ++ l.drop j).filter p).drop ((l.take j).filter p).length := by
    rw [List.take_append_drop]
  rw [h, List.filter_append, List.drop_left]

theorem filter_take_succ' {α : Type} (l : List α) (p : α → Bool) (j : Nat) (x : α)
    (hx : l[j]? = some x) :
    (l.take (j + 1)).filter p = (l.take j).filter p ++ (if p x then [x] else []) := by
  rw [List.take_add_one, hx, List.filter_append]
  cases h : p x <;> simp [List.filter, h]

/-- The inner loop finds the `j`-th change of `r`, in range, after skipping `expSkip`'s. -/
theorem expRem_found (Hl : List HRev) (mt : change → Bool) (rev index : Nat) (upto : Int)
    (r : Nat) (hr : (r : Int) ≤ upto) (chs : List change)
    (hchs : (Hl[r]?.map Prod.snd).getD [] = chs) (j : Nat) (ch : change) (hj : chs[j]? = some ch)
    (hin : mt ch = true)
    (hseen : ((chs.take j).filter fun ch => mt ch).length = expSkip rev index r) :
    (expRem Hl mt rev index upto r).head? = some (r, ch) := by
  unfold expRem rangeChs
  simp only [hr, ↓reduceIte]
  rw [hchs, ← hseen, drop_filter_take]
  obtain ⟨hjl, hjc⟩ := List.getElem?_eq_some_iff.1 hj
  rw [List.drop_eq_getElem_cons hjl, hjc]
  simp [hin]

/-- The inner loop ends with no change left at `r`. -/
theorem rangeChs_drop_nil (Hl : List HRev) (mt : change → Bool) (r k : Nat) (chs : List change)
    (hchs : (Hl[r]?.map Prod.snd).getD [] = chs)
    (hk : (chs.filter fun ch => mt ch).length ≤ k) : (rangeChs Hl mt r).drop k = [] := by
  unfold rangeChs; rw [hchs]; exact List.drop_eq_nil_of_le hk

/-- **A watcher's position after `n` events** (registered from `lo`): its revision `rev` from
`lo`, its `index` at most the in-range changes of `rev`, and `n` the expected changes before `rev`
and the first `index` of `rev`'s. -/
def posOk (Hl : List HRev) (mt : change → Bool) (lo rev index n : Nat) : Prop :=
  lo ≤ rev ∧ index ≤ (rangeChs Hl mt rev).length ∧ (expChs Hl mt lo rev).length + index = n

theorem posOk_start (Hl : List HRev) (mt : change → Bool) (lo : Nat) : posOk Hl mt lo lo 0 0 := by
  refine ⟨(Nat.le_refl _), Nat.zero_le _, ?_⟩
  rw [expChs_empty _ _ (Nat.le_refl _)]; rfl

/-- **`expect` under the position invariant: the `n`-th expected change up to `upto`.** -/
theorem expNext_eq_get (Hl : List HRev) (mt : change → Bool) (lo rev index n : Nat)
    (hlo : 1 ≤ lo) (h : posOk Hl mt lo rev index n) (upto : Int) :
    expNext Hl mt rev index upto = (expChs Hl mt lo (upto.toNat + 1))[n]? := by
  obtain ⟨h1, h2, h3⟩ := h
  unfold expNext
  split
  · rename_i hu
    -- nothing up to `upto`: the expected changes up to it are fewer than `n`
    symm
    rw [List.getElem?_eq_none_iff]
    by_cases hb : upto.toNat + 1 ≤ lo
    · rw [expChs_empty _ _ hb]; simp
    · rw [expChs_append Hl mt (show lo ≤ upto.toNat + 1 by omega)
        (show upto.toNat + 1 ≤ rev by omega)] at h3
      simp only [List.length_append] at h3
      omega
  · rename_i hu
    have hr : rev < upto.toNat + 1 := by omega
    rw [expChs_append Hl mt h1 (show rev ≤ upto.toNat + 1 by omega), expChs_cons Hl mt hr,
      ← h3, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left, ← List.head?_drop,
      List.drop_append_of_le_length (by simpa using h2), List.map_drop]

theorem expNext_some {Hl : List HRev} {mt : change → Bool} {rev index : Nat} {upto : Int}
    {r : Nat} {ch : change} (h : expNext Hl mt rev index upto = some (r, ch)) :
    rev ≤ r ∧ (r : Int) ≤ upto ∧ ch ∈ rangeChs Hl mt r := by
  unfold expNext at h
  split at h
  · cases h
  · rename_i hu
    have hm := List.mem_of_mem_head? h
    rcases List.mem_append.1 hm with hm | hm
    · obtain ⟨c, hc, he⟩ := List.mem_map.1 hm
      cases he
      exact ⟨(Nat.le_refl _), by omega, List.mem_of_mem_drop hc⟩
    · have := mem_expChs hm
      simp only at this
      exact ⟨by omega, by omega, this.2.2⟩

/-- **`advance` after `expect`'s change keeps the position**, at one more event. -/
theorem posOk_next (Hl : List HRev) (mt : change → Bool) (lo rev index n : Nat) (upto : Int)
    (r : Nat) (ch : change) (h : posOk Hl mt lo rev index n)
    (hn : expNext Hl mt rev index upto = some (r, ch)) :
    posOk Hl mt lo (if rev < r then r else rev) (if rev < r then 1 else index + 1) (n + 1) := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨hr1, hr2, hr3⟩ := expNext_some hn
  unfold expNext at hn
  simp only [show ¬ upto < (rev : Int) from by omega, ↓reduceIte] at hn
  by_cases hlt : rev < r
  · simp only [hlt, ↓reduceIte]
    -- `rev`'s remaining changes are none, and none of `(rev, r)`
    have hd : (rangeChs Hl mt rev).drop index = [] := by
      cases hdc : (rangeChs Hl mt rev).drop index with
      | nil => rfl
      | cons c cs =>
        rw [hdc] at hn
        simp at hn
        omega
    rw [hd, List.map_nil, List.nil_append] at hn
    have hlen : (rangeChs Hl mt rev).length = index := by
      have := List.length_drop (l := rangeChs Hl mt rev) (i := index)
      rw [hd] at this; simp at this; omega
    have hmid : expChs Hl mt (rev + 1) r = [] := by
      rw [expChs_append Hl mt (show rev + 1 ≤ r by omega)
        (show r ≤ upto.toNat + 1 by omega)] at hn
      cases hc : expChs Hl mt (rev + 1) r with
      | nil => rfl
      | cons p ps =>
        rw [hc] at hn
        simp at hn
        have := mem_expChs (show (r, ch) ∈ expChs Hl mt (rev + 1) r by rw [hc, ← hn]; simp)
        simp only at this; omega
    refine ⟨by omega, ?_, ?_⟩
    · have := List.length_pos_of_mem hr3; omega
    · rw [expChs_append Hl mt h1 (show rev ≤ r by omega), expChs_cons Hl mt hlt, hmid]
      simp only [List.length_append, List.length_map, List.length_nil]
      omega
  · simp only [hlt, ↓reduceIte]
    have hre : r = rev := by omega
    subst hre
    refine ⟨h1, ?_, by omega⟩
    cases hdc : (rangeChs Hl mt r).drop index with
    | nil =>
      rw [hdc, List.map_nil, List.nil_append] at hn
      have := mem_expChs (List.mem_of_mem_head? hn)
      simp only at this; omega
    | cons c cs =>
      have := List.length_drop (l := rangeChs Hl mt r) (i := index)
      rw [hdc] at this; simp at this; omega

/-- **The watcher `wv` after `receive` takes its event at revision `r`** (mvccfull's `receive`,
inline: `if w.rev < r { w.rev, w.index = r, 0 }; w.index++`; mvccrand's `advance`): to the first
change after it of revision `r` when `r` is past its revision, else one change further in it. -/
def advW (wv : watcher) (r : w64) : watcher :=
  if sint.Z wv.rev' < sint.Z r then { wv with rev' := r, index' := W64 1 }
  else { wv with index' := wv.index' + W64 1 }

/-- `advance`'s watcher after `expect`'s change: the position at one more event. -/
theorem posOk_advW (Hl : List HRev) (mt : change → Bool) (lo n : Nat) (upto : Int)
    (wv : watcher) (r : Nat) (ch : change) (h0r : 0 ≤ sint.Z wv.rev') (h0i : 0 ≤ sint.Z wv.index')
    (h : posOk Hl mt lo (sint.nat wv.rev') (sint.nat wv.index') n)
    (hn : expNext Hl mt (sint.nat wv.rev') (sint.nat wv.index') upto = some (r, ch))
    (hr : r < 2 ^ 63) (hlen : (rangeChs Hl mt r).length < 2 ^ 63) :
    0 ≤ sint.Z (advW wv (W64 r)).rev' ∧ 0 ≤ sint.Z (advW wv (W64 r)).index' ∧
      posOk Hl mt lo (sint.nat (advW wv (W64 r)).rev') (sint.nat (advW wv (W64 r)).index') (n + 1) := by
  have hp := posOk_next Hl mt lo _ _ n upto r ch h hn
  obtain ⟨hr1, -, hr3⟩ := expNext_some hn
  have hrZ : sint.Z (W64 (r : Int)) = r := by word
  have hrN : sint.nat (W64 (r : Int)) = r := by word
  unfold advW
  by_cases hlt : sint.nat wv.rev' < r
  · have hlt' : sint.Z wv.rev' < sint.Z (W64 (r : Int)) := by
      rw [hrZ]; have : sint.nat wv.rev' = (sint.Z wv.rev').toNat := rfl; omega
    simp only [hlt', ↓reduceIte]
    simp only [hlt, ↓reduceIte] at hp
    refine ⟨by omega, by word, ?_⟩
    rw [hrN, show sint.nat (W64 1) = 1 from rfl]
    exact hp
  · have hlt' : ¬ sint.Z wv.rev' < sint.Z (W64 (r : Int)) := by
      rw [hrZ]; have : sint.nat wv.rev' = (sint.Z wv.rev').toNat := rfl; omega
    simp only [hlt', ↓reduceIte]
    simp only [hlt, ↓reduceIte] at hp
    have hre : r = sint.nat wv.rev' := by omega
    subst hre
    have hi := hp.2.1
    have hiN : sint.nat (wv.index' + W64 1) = sint.nat wv.index' + 1 := by
      have : sint.nat wv.index' = (sint.Z wv.index').toNat := rfl
      word
    refine ⟨h0r, by word, ?_⟩
    rw [hiN]
    exact hp

/-- **An event received in order**: if the `n`-th expected change is `(r, ch)`, `expect` at upto
`r` from the position after `n` events returns it. -/
theorem expNext_of_get (Hl : List HRev) (mt : change → Bool) (lo rev index n hi r : Nat)
    (ch : change) (hlo : 1 ≤ lo) (h : posOk Hl mt lo rev index n)
    (hn : (expChs Hl mt lo hi)[n]? = some (r, ch)) :
    expNext Hl mt rev index (r : Int) = some (r, ch) := by
  rw [expNext_eq_get Hl mt lo rev index n hlo h, Int.toNat_natCast]
  exact expChs_getElem_cut hn

/-- **Nothing more up to `upto`**: when the expected changes up to `upto` are the `n` received,
`expect` from the position after them returns none. -/
theorem expNext_none_of_length (Hl : List HRev) (mt : change → Bool) (lo rev index n : Nat)
    (upto : Int) (hlo : 1 ≤ lo) (h : posOk Hl mt lo rev index n)
    (hn : (expChs Hl mt lo (upto.toNat + 1)).length ≤ n) :
    expNext Hl mt rev index upto = none := by
  rw [expNext_eq_get Hl mt lo rev index n hlo h, List.getElem?_eq_none_iff]
  exact hn

theorem rangeChs_prefix {Hl Hl' : List HRev} (hp : Hl <+: Hl') (mt : change → Bool) {r : Nat}
    (hr : r < Hl.length) : rangeChs Hl mt r = rangeChs Hl' mt r := by
  unfold rangeChs
  obtain ⟨T, rfl⟩ := hp
  rw [List.getElem?_append_left hr]

/-- A longer history has the same positions below its lower bound's length. -/
theorem posOk_prefix {Hl Hl' : List HRev} (hp : Hl <+: Hl') (mt : change → Bool)
    {lo rev index n : Nat} (hr : rev < Hl.length) :
    posOk Hl mt lo rev index n ↔ posOk Hl' mt lo rev index n := by
  unfold posOk
  rw [rangeChs_prefix hp mt hr, expChs_prefix hp mt (by omega : rev ≤ Hl.length)]

/-- A longer history gives `expect` the same answer up to its lower bound's length. -/
theorem expNext_prefix {Hl Hl' : List HRev} (hp : Hl <+: Hl') (mt : change → Bool)
    (rev index : Nat) {upto : Int} (hu : upto < Hl.length) :
    expNext Hl mt rev index upto = expNext Hl' mt rev index upto := by
  unfold expNext
  split
  · rfl
  · rename_i h
    rw [rangeChs_prefix hp mt (by omega), expChs_prefix hp mt (by omega : upto.toNat + 1 ≤ Hl.length)]

end model

end mvccfull
end EtcdGrove
end Perennial
