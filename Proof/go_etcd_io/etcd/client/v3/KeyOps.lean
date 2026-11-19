/-
A get after a put, purely (unit C2a, 2026-10-14): the put and the get of one key with no options
(`putKeyOp`, `getKeyOp`) and what the server's answers to them are, as pure lemmas. Moved out of
`Results.lean` (2026-11-18), which links them with the linked results, so that a spec or a
definition naming them imports no linked result (CLAUDE.md, "Import tiers").
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvProposer

@[expose] public section

set_option pp.fullNames true
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace client

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

/-! ## A get after a put, purely (unit C2a, 2026-10-14) -/

section pure
open mvcc

/-- The get of one key with no options (what `kv.Get(ctx, key)` sends, `client_get_end_to_end`). -/
abbrev getKeyOp (key : GoString) : OpFull :=
  txn.rangeOpOf key [] (W64 0) (W64 0) (W32 0) (W32 0) false false false (W64 0) (W64 0) (W64 0)
    (W64 0)

/-- The put of `key ↦ val` with no options (what `kv.Put(ctx, key, val)` sends). -/
abbrev putKeyOp (key val : GoString) : OpFull :=
  txn.putOpOf key val (W64 0) false false false

/-- **The get of one key with no options selects the key's key-value** (pure): the server's
answer is the state's key-values of that key, no `More`. -/
theorem srvRangeOk_getKey (key : GoString) (s kvs : List EtcdKv) (more : Bool)
    (h : txn.srvRangeOk (getKeyOp key) s kvs more) :
    kvs = s.filter (fun v => decide (v.key = key)) ∧ more = false := by
  obtain ⟨L, hsort, hmore, hkvs⟩ := h
  have hpre : txn.srvPre (getKeyOp key) s = s.filter (fun v => decide (v.key = key)) := by
    have hr : txn.kvRead false = id := by funext v; simp [txn.kvRead]
    unfold txn.srvPre
    simp [txn.rangeLimitOf, txn.hasRevFilters, mvcc.limitOf, mvcc.takeLimit, txn.fastKeysOnly,
      rangeIn, inRange, hr]
    apply List.filter_congr
    intro v _
    simp [kvFilterOk]
  have hord : (getKeyOp key).effSortOrder = W64 0 := by
    simp [OpFull.effSortOrder]
  have hL : L = txn.srvPre (getKeyOp key) s := by
    obtain ⟨-, -, -, h4⟩ := hsort
    exact h4 (by rw [hord]; decide) (by rw [hord]; decide)
  have hm : txn.srvMore (getKeyOp key) L = false := by
    simp [txn.srvMore]
  refine ⟨?_, by rw [hmore, hm]⟩
  rw [hkvs]
  unfold txn.srvTrunc
  rw [hm, hL, hpre]
  have hid : txn.respKv (getKeyOp key) = id := by funext v; simp [txn.respKv]
  simp [hid]

/-- In a state sorted by key, the key-values of a key are the one its key finds. -/
theorem filter_key_of_findKey (k : GoString) :
    ∀ (s : List EtcdKv), s.Pairwise etcdKvLess → ∀ kv, findKey k s = some kv →
      s.filter (fun v => decide (v.key = k)) = [kv]
  | [], _, kv, h => by simp [findKey] at h
  | w :: ws, hs, kv, h => by
    rw [List.pairwise_cons] at hs
    rw [findKey_cons] at h
    by_cases hw : w.key = k
    · rw [ite_eq_left hw] at h
      cases h
      have hnil : ws.filter (fun v => decide (v.key = k)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro y hy
        have hlt := hs.1 y hy
        unfold etcdKvLess at hlt
        intro hyk
        simp only [decide_eq_true_eq] at hyk
        rw [hw, hyk] at hlt
        exact go.goStringLt_irrefl _ hlt
      simp [hw, hnil]
    · rw [ite_eq_right hw] at h
      simp only [List.filter_cons, hw, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact filter_key_of_findKey k ws hs.2 kv h

/-- In a state sorted by key, a key it does not find has no key-value. -/
theorem filter_key_of_findKey_none (k : GoString) :
    ∀ (s : List EtcdKv), findKey k s = none → s.filter (fun v => decide (v.key = k)) = []
  | [], _ => rfl
  | w :: ws, h => by
    rw [findKey_cons] at h
    by_cases hw : w.key = k
    · rw [ite_eq_left hw] at h; cases h
    · rw [ite_eq_right hw] at h
      simp only [List.filter_cons, hw, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact filter_key_of_findKey_none k ws h

/-- **The get of one key returns the key's value in the model** (pure; 2026-10-14, unit T1): its
first key-value's value is `kvVal` of the log read. -/
theorem getKey_value (key : GoString) (l : Log) (kvs : List EtcdKv) (more : Bool)
    (h : txn.srvRangeOk (getKeyOp key) (stateAfter l) kvs more) :
    kvs.head?.map EtcdKv.value = kvVal l key := by
  obtain ⟨hkvs, -⟩ := srvRangeOk_getKey key _ kvs more h
  unfold kvVal
  cases hf : findKey key (stateAfter l) with
  | none => rw [hkvs, filter_key_of_findKey_none key _ hf]; rfl
  | some kv => rw [hkvs, filter_key_of_findKey key _ (stateAfter_sorted l) kv hf]; rfl

/-- A key the changes do not touch keeps its key-value. -/
theorem findKey_applyChanges_untouched (k : GoString) (r : w64) :
    ∀ (cs : List Change) (s : List EtcdKv), s.Pairwise etcdKvLess → (∀ c ∈ cs, c.key ≠ k) →
      findKey k (applyChanges r s cs) = findKey k s
  | [], _, _, _ => rfl
  | c :: cs, s, hs, hc => by
    have hc0 := hc c (List.mem_cons_self ..)
    have hrest : ∀ c' ∈ cs, c'.key ≠ k := fun c' h => hc c' (List.mem_cons_of_mem _ h)
    show findKey k (applyChanges r (applyChange r s c) cs) = findKey k s
    rw [findKey_applyChanges_untouched k r cs _ (applyChange_sorted hs r c) hrest]
    cases c with
    | put k' v l =>
      exact findKey_putKv_other hs r k k' v l hc0
    | del k' =>
      show findKey k (s.filter fun x => !decide (x.key = k')) = findKey k s
      rw [findKey_filter_ne]
      simp only [Change.key] at hc0
      rw [ite_eq_right hc0]

/-- A key no later revision touches keeps its key-value. -/
theorem findKey_stateAfter_untouched (k : GoString) :
    ∀ (rest L : Log), (∀ cs ∈ rest, ∀ c ∈ cs, c.key ≠ k) →
      findKey k (stateAfter (L ++ rest)) = findKey k (stateAfter L)
  | [], L, _ => by simp
  | cs :: rest, L, h => by
    have h1 := findKey_stateAfter_untouched k rest (L ++ [cs])
      (fun cs' hcs' => h cs' (List.mem_cons_of_mem _ hcs'))
    rw [show L ++ cs :: rest = (L ++ [cs]) ++ rest by simp, h1, stateAfter_append,
      findKey_applyChanges_untouched k _ cs _ (stateAfter_sorted _) (h cs (List.mem_cons_self ..))]

/-- The put of `key ↦ val` finds the value it wrote. -/
theorem findKey_putKv_value (s : List EtcdKv) (hs : s.Pairwise etcdKvLess) (r : w64)
    (k v : GoString) (l : w64) :
    ∃ nv, findKey k (putKv r k v l s) = some nv ∧ nv.key = k ∧ nv.value = v := by
  unfold putKv
  simp only
  rw [findKey_btInsert _ s hs]
  cases h : s.find? (fun v => decide (v.key = k)) with
  | none =>
    refine ⟨{ key := k, createRev := r, modRev := r, version := W64 1, value := v, lease := l },
      ?_, rfl, rfl⟩
    simp
  | some kv =>
    have hk : kv.key = k := by simpa using List.find?_some h
    refine ⟨{ kv with modRev := r, version := kv.version + W64 1, value := v, lease := l }, ?_,
      hk, rfl⟩
    simp [hk]


/-- **A put applied with no error through any chain wrote the client's put change** (pure). -/
theorem chainStep_put_applied (op : OpFull) (rq : apply.IRRModel)
    (hk : apply.dispatchKind rq = .put) (hop : rq.put = some op) (log l : Log) :
    ∀ c : apply.Chain, apply.chainStep apply.backendStep c rq log (.applied l false) →
      l = log ++ [[txn.putChangeOf op (findKey op.key (stateAfter log))]]
  | .backend, h => by
    simp only [apply.chainStep, apply.backendStep, hk] at h
    obtain ⟨op', hop', h⟩ := h
    rw [hop] at hop'; cases hop'
    rcases h with ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, h⟩
    · cases h
    · cases h
    · cases h; rfl
  | .corrupt c, h => by
    simp only [apply.chainStep, hk, apply.corruptRejects, ↓reduceIte] at h
    cases h
  | .capped c, h => by
    simp only [apply.chainStep, hk, apply.cappedRejects, ↓reduceIte] at h
    cases h
  | .auth _ c, h => by
    unfold apply.chainStep at h
    split at h
    · rcases h with ⟨-, h⟩ | h
      · cases h
      · exact chainStep_put_applied op rq hk hop log l c h
    · exact chainStep_put_applied op rq hk hop log l c h
  | .quota c, h => by
    unfold apply.chainStep at h
    exact chainStep_put_applied op rq hk hop log l c h

/-- **What a successful put applied** (pure; chain-agnostic, unlike `v3rpc.put_end_to_end_model`):
the log after is the log the entry met with the client's put change. -/
theorem put_applied_log (o : OpFull) (hm : apply.HeaderModel) (x x' : apply.ApplyKV)
    (l : Log) (skip : Bool)
    (h : apply.applyStep (apply.withHeader (irrPut o) hm) true x x'
      (.dispatched (.applied l false) skip)) :
    x'.log = x.log ++ [[txn.putChangeOf o (findKey o.key (stateAfter x.log))]] := by
  obtain ⟨-, hd, hl, -⟩ := h
  have hk : apply.dispatchKind (apply.withHeader (irrPut o) hm) = .put := by
    simp [apply.dispatchKind, apply.withHeader, irrPut, apply.irrEmpty]
  have hop : (apply.withHeader (irrPut o) hm).put = some o := by
    simp [apply.withHeader, irrPut, apply.irrEmpty]
  unfold apply.dispatchStep at hd
  rw [hk] at hd
  simp only [apply.preV3Kind, apply.storeKind, Bool.false_eq_true, false_or, ↓reduceIte] at hd
  rw [hl]
  exact chainStep_put_applied o _ hk hop x.log l x.chain hd

/-- **A get after a put reads the put's value unless a later revision touched the key** (pure; the
corollary of `client_get_after_put`): the put of `key ↦ val` at the log `x.log` (`put_applied_log`:
`x'.log` is `x.log` with the put's change) and a get of `key` with no options at a log `l` extending
`x'.log`, with no later revision of `l` touching `key`: the get's key-values are exactly the put's
key-value (key `key`, value `val`), and no `More`. -/
theorem get_after_put_kvs (key val : GoString) (x x' : apply.ApplyKV) (l : Log)
    (kvs : List EtcdKv) (more : Bool)
    (hx' : x'.log = x.log ++ [[txn.putChangeOf (putKeyOp key val)
      (findKey key (stateAfter x.log))]])
    (hpre : x'.log <+: l) (hget : txn.srvRangeOk (getKeyOp key) (stateAfter l) kvs more)
    (hno : ∀ cs ∈ l.drop x'.log.length, ∀ c ∈ cs, c.key ≠ key) :
    ∃ kv, kvs = [kv] ∧ kv.key = key ∧ kv.value = val ∧ more = false := by
  obtain ⟨rest, rfl⟩ := hpre
  have hrest : List.drop x'.log.length (x'.log ++ rest) = rest := by simp
  rw [hrest] at hno
  obtain ⟨hkvs, hmore⟩ := srvRangeOk_getKey key _ kvs more hget
  have hput : findKey key (stateAfter x'.log) =
      findKey key (putKv (W64 x.log.length) key val (W64 0) (stateAfter x.log)) := by
    rw [hx', stateAfter_append]
    simp [applyChanges, applyChange, txn.putChangeOf, txn.putValOf, txn.putLeaseOf, putKeyOp,
      txn.putOpOf]
  obtain ⟨nv, hnv, hk, hv⟩ := findKey_putKv_value _ (stateAfter_sorted x.log) (W64 x.log.length)
    key val (W64 0)
  rw [hnv] at hput
  have hf := filter_key_of_findKey key _ (stateAfter_sorted (x'.log ++ rest)) nv
    (by rw [findKey_stateAfter_untouched key rest x'.log hno, hput])
  exact ⟨nv, by rw [hkvs, hf], hk, hv, hmore⟩

end pure


end client
end EtcdGrove
end Perennial
