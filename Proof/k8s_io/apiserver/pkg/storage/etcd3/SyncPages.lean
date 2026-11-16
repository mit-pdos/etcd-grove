/-
Lean-first (no Rocq counterpart).

# `syncPaginated`'s pages are the scope at the first page's revision (pure; k8s 7f-5a-P step 5)

`(*watchChan).syncPaginated` reads its scope with the client's `KV.Get`: recursive, from the prepared
key with `WithLimit(10000)` and `WithRange(GetPrefixRangeEnd(key))` (`syncGs`), the pages after the
first `WithRev(rev)` of the first page's revision, each from the last key read and `"\x00"`; not
recursive, the key alone with no option. Here:

- `rangeWireOf_sync0`, `rangeWireOf_syncR`: the recursive requests are `List`'s `pageOp`s;
- `srvRangeOk_page_more`: with a positive limit, `More` says the scope from the start key is longer
  than the limit;
- `srvRangeOk_key0`: the key alone gives its key-values and no `More`;
- `syncNext`: from a page with `More`, the next start key's scope is the rest (`fromL_next`).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.ListPages
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.WatchProd

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open go_etcd_io.etcd.server.v3.etcdserver

section pure
variable [GooseExts]

/-- **`syncPaginated`'s options before the first page**: recursive, `WithLimit(10000)` and
`WithRange(GetPrefixRangeEnd(key))`; none otherwise. -/
def syncGs (kp : GoString) (recur : Bool) : List (OpFull → OpFull) :=
  if recur then [withLimitM (W64 10000), withRangeM (prefixRangeEnd kp)] else []

theorem rangeWireOf_sync0 (kp start : GoString) :
    rangeWireOf (opGetModel start (syncGs kp true)) = pageOp kp start (W64 0) (W64 10000) := rfl

theorem rangeWireOf_syncR (kp start : GoString) (r : w64) :
    rangeWireOf (opGetModel start (syncGs kp true ++ [withRevM r])) =
      pageOp kp start r (W64 10000) := rfl

/-- **A page's `More`**: with a positive limit (below `2^63 - 1`), whether the scope from the start
key is longer than the limit. -/
theorem srvRangeOk_page_more (pfx start : GoString) (rev lim : w64) (s : KVStore)
    (kvs : List EtcdKv) (more : Bool) (hst : pfx <+: start) (h0 : 0 < sint.Z lim)
    (hmx : sint.Z lim < 2 ^ 63 - 1)
    (h : txn.srvRangeOk (pageOp pfx start rev lim) s.kvs kvs more) :
    more = decide (sint.nat lim < (fromL s pfx true start).length) := by
  have hR : rangeIn s.kvs (pageOp pfx start rev lim) = fromL s pfx true start := by
    unfold rangeIn fromL
    apply List.filter_congr
    intro v _
    exact inRange_page pfx start v.key hst
  obtain ⟨L, hsort, hmore, -⟩ := h
  have hord : (pageOp pfx start rev lim).effSortOrder = W64 0 := by
    simp [OpFull.effSortOrder]
  have hL : L = txn.srvPre (pageOp pfx start rev lim) s.kvs := by
    obtain ⟨-, -, -, h4⟩ := hsort
    exact h4 (by rw [hord]; decide) (by rw [hord]; decide)
  have hr : txn.kvRead false = id := by funext v; simp [txn.kvRead]
  have hpre : txn.srvPre (pageOp pfx start rev lim) s.kvs =
      mvcc.takeLimit (mvcc.limitOf (txn.rangeLimitOf (pageOp pfx start rev lim)))
        (fromL s pfx true start) := by
    unfold txn.srvPre
    rw [hR]
    simp [txn.fastKeysOnly, hr]
    try apply List.filter_eq_self.2
    intro v _
    simp [kvFilterOk]
  have hrl : txn.rangeLimitOf (pageOp pfx start rev lim) = lim + W64 1 := by
    have hmx' : sint.Z lim < 9223372036854775807 := by simpa using hmx
    simp [txn.rangeLimitOf, txn.isDefaultOrd, txn.hasRevFilters, h0, hmx']
  have hl1 : mvcc.limitOf (lim + W64 1) = some ((sint.Z lim).toNat + 1) := by
    unfold mvcc.limitOf
    have : sint.Z (lim + W64 1) = sint.Z lim + 1 := by word
    rw [this]; simp only [show 0 < sint.Z lim + 1 by omega, ↓reduceIte]; congr 1; omega
  rw [hmore, hL, hpre, hrl, hl1]
  unfold txn.srvMore mvcc.takeLimit
  have hlim : (pageOp pfx start rev lim).base.limit = lim := rfl
  rw [hlim]
  apply decide_eq_decide.2
  simp only [List.length_take]
  have hn : sint.nat lim = (sint.Z lim).toNat := rfl
  rw [hn]
  constructor
  · rintro ⟨-, h⟩; omega
  · intro h; exact ⟨h0, by omega⟩

/-- **The key alone** (`Get(key)`, no option): its key-values, and no `More`. -/
theorem srvRangeOk_key0 (key : GoString) (s kvs : List EtcdKv) (more : Bool)
    (h : txn.srvRangeOk (rangeWireOf (opGetModel key [])) s kvs more) :
    kvs = s.filter (fun v => decide (v.key = key)) ∧ more = false := by
  generalize ho : rangeWireOf (opGetModel key []) = o at h
  have ho' : o = (txn.rangeOpOf key [] (W64 0) (W64 0) (W32 0) (W32 0) false false false (W64 0) (W64 0) (W64 0) (W64 0)) := by
    rw [← ho]; rfl
  subst ho'
  obtain ⟨L, hsort, hmore, hkvs⟩ := h
  have hpre : txn.srvPre (txn.rangeOpOf key [] (W64 0) (W64 0) (W32 0) (W32 0) false false false (W64 0) (W64 0) (W64 0) (W64 0)) s =
      s.filter (fun v => decide (v.key = key)) := by
    have hr : txn.kvRead false = id := by funext v; simp [txn.kvRead]
    unfold txn.srvPre
    simp [txn.rangeLimitOf, txn.hasRevFilters, mvcc.limitOf, mvcc.takeLimit, txn.fastKeysOnly,
      rangeIn, inRange, hr]
    apply List.filter_congr
    intro v _
    simp [kvFilterOk]
  have hord : ((txn.rangeOpOf key [] (W64 0) (W64 0) (W32 0) (W32 0) false false false (W64 0) (W64 0) (W64 0) (W64 0)) :
      OpFull).effSortOrder = W64 0 := by
    simp [OpFull.effSortOrder]
  have hL : L = txn.srvPre (txn.rangeOpOf key [] (W64 0) (W64 0) (W32 0) (W32 0) false false false (W64 0) (W64 0) (W64 0) (W64 0)) s := by
    obtain ⟨-, -, -, h4⟩ := hsort
    exact h4 (by rw [hord]; decide) (by rw [hord]; decide)
  have hm : txn.srvMore (txn.rangeOpOf key [] (W64 0) (W64 0) (W32 0) (W32 0) false false false (W64 0) (W64 0) (W64 0) (W64 0)) L =
      false := by
    unfold txn.srvMore; simp
  refine ⟨?_, hmore.trans hm⟩
  rw [hkvs]
  unfold txn.srvTrunc
  rw [hm, hL, hpre]
  have hresp : ∀ o : OpFull, o.keysOnly = false → txn.respKv o = id := fun o h => by
    funext v; simp [txn.respKv, h]
  rw [hresp _ rfl]
  simp

/-- Not recursive, the scope is the key's key-values. -/
theorem scope_key (s : List EtcdKv) (kp : GoString) :
    s.filter (fun v => kInScope kp false v.key) = s.filter (fun v => decide (v.key = kp)) := by
  apply List.filter_congr
  intro v _
  simp [kInScope]

/-- **The next page's start key** (`syncPaginated`'s `string(lastKey) + "\x00"`): after a page
of `n` key-values cut by `More` (the scope from `st` longer than `n`), the scope from the next start
key is the rest. -/
theorem syncNext (s : KVStore) (kp st : GoString) (n : Nat) (hn : 0 < n)
    (hm : n < (fromL s kp true st).length) :
    ∃ kv, ((fromL s kp true st).take n).getLast? = some kv ∧
      fromL s kp true (kv.key ++ [W8 0]) = (fromL s kp true st).drop n := by
  refine ⟨(fromL s kp true st)[n - 1]'(by omega), ?_, ?_⟩
  · rw [List.getLast?_eq_getElem?]
    simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hm)]
    rw [List.getElem?_take]
    simp only [show n - 1 < n by omega, ↓reduceIte]
    exact List.getElem?_eq_getElem _
  · exact fromL_next s kp true st n hn (Nat.le_of_lt hm)

/-- **A recursive page** (`WithLimit(10000)`, from a start key under the prefix): the first `10000`
key-values of the scope from the start key, and `More` if there are more. -/
theorem srvRangeOk_sync (kp start : GoString) (rev : w64) (s : KVStore) (kvs : List EtcdKv)
    (more : Bool) (hst : kp <+: start)
    (h : txn.srvRangeOk (pageOp kp start rev (W64 10000)) s.kvs kvs more) :
    kvs = (fromL s kp true start).take 10000 ∧
      more = decide (10000 < (fromL s kp true start).length) := by
  have h1 := (srvRangeOk_page kp start rev (W64 10000) s kvs more hst (by decide) h).1
  have h2 := srvRangeOk_page_more kp start rev (W64 10000) s kvs more hst (by decide) (by decide) h
  have hl : limN (W64 10000) = 10000 := by decide
  rw [pageKvsL_eq, hl] at h1
  exact ⟨h1, h2⟩

/-- The scope from the key itself, not recursive, is the key's key-values. -/
theorem fromL_key (s : KVStore) (kp : GoString) :
    fromL s kp false kp = s.kvs.filter (fun v => decide (v.key = kp)) := by
  unfold fromL
  apply List.filter_congr
  intro v _
  by_cases h : v.key = kp
  · simp [kInScope, h, go.goStringLt_irrefl]
  · simp [kInScope, h]

/-- **What the page queues is a prefix of the initial raw events.** -/
theorem queue_prefix {I K : List KRaw} {pg F : List EtcdKv} (h : I ++ F.map KRaw.kv = K)
    (hp : pg <+: F) (j : Nat) (hj : j < pg.length) :
    I ++ (pg.take j).map KRaw.kv ++ [KRaw.kv pg[j]] <+: K := by
  rw [← h, List.append_assoc]
  apply (List.prefix_append_right_inj I).2
  have h1 : (pg.take j).map KRaw.kv ++ [KRaw.kv pg[j]] = (pg.take (j + 1)).map KRaw.kv := by
    rw [List.take_succ, List.getElem?_eq_getElem hj, List.map_append]; rfl
  rw [h1]
  exact ((List.take_prefix _ _).trans hp).map _

/-- The initial raw events are the start of the ideal raw stream (with initial events). -/
theorem kInitRaws_prefix (inS : GoString → Bool) (m : KWatchMode) (σ : KVState) (st : Nat)
    (hf : m.forceInit = true) : kInitRaws inS σ st <+: kRawIdealL inS m σ st [] := by
  unfold kRawIdealL kInitRaws
  rw [if_pos hf]
  exact List.prefix_append _ _

/-- The initial raw events, from the prepared key: its scope's key-values. -/
theorem kInitRaws_fromL (kp : GoString) (recur : Bool) (σ : KVState) (st : Nat) :
    kInitRaws (kInScope kp recur) σ st = (fromL (σ.at st) kp recur kp).map KRaw.kv := by
  unfold kInitRaws
  rw [fromL_kp]
  rfl

end pure

end k8s
end EtcdGrove
end Perennial
