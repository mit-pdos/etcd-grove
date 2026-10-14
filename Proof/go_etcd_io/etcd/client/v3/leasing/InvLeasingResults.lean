/-
The pure and logical lemmas behind `client/v3/leasing`'s main theorems (`Results.lean`): when a
cached get is etcd's record (`cached_get_stable`, from `leased_value_stable`), when the cache's
`Update` tracks the holder's put (`update_tracks_put`) and how it does not (`WithIgnoreValue`, the
lease, out-of-order updates), and when the cache's evaluation of a comparison is etcd's
(`evalCmpM_agrees`, `leaseEvalCmps_agrees`) and how it is not. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeasingKV
public import Proof.go_etcd_io.etcd.client.v3.concurrency.InvSTMAtomic

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

/-! ## Single keys in a well-formed state -/

theorem kvOf_eq_kvAt (s : List EtcdKv) (k : GoString) : kvOf s k = concurrency.kvAt s k := rfl

theorem wf_pairwise {s : List EtcdKv} (hwf : EtcdStateWf [] s) : s.Pairwise etcdKvLess := by
  have := hwf.1
  rw [List.pairwise_map] at this
  exact this

/-- The keys of a single-key range, in a state with unique keys: its record, if any. -/
theorem filter_key (s : List EtcdKv) (k : GoString) (hwf : EtcdStateWf [] s) :
    s.filter (fun v => inRange k [] v.key) = (kvOf s k).toList := by
  have hpw := wf_pairwise hwf
  induction s with
  | nil => rfl
  | cons w ws ih =>
    rw [List.pairwise_cons] at hpw
    have hwf' : EtcdStateWf [] ws := ⟨(List.pairwise_cons.1 hwf.1).2,
      fun v hv => hwf.2 v (List.mem_cons_of_mem _ hv)⟩
    rw [List.filter_cons]
    by_cases hw : w.key = k
    · have hin : inRange k [] w.key = true := by simp [inRange, hw]
      simp only [hin, ↓reduceIte]
      have hnone : ws.filter (fun v => inRange k [] v.key) = [] := by
        rw [List.filter_eq_nil_iff]
        intro v hv hvk
        have hlt := hpw.1 v hv
        have hvk' : v.key = k := by simpa [inRange] using hvk
        unfold etcdKvLess at hlt
        rw [hw, hvk'] at hlt
        exact goStringLt_irrefl _ hlt
      rw [hnone]
      simp [kvOf, hw]
    · have hin : inRange k [] w.key = false := by simp [inRange, hw]
      simp only [hin, Bool.false_eq_true, ↓reduceIte]
      rw [ih hwf' hpw.2]
      simp [kvOf, hw]

/-- etcd's record of `key` after a put of `key` (`putKv`), in a state with unique keys. -/
theorem kvOf_putKv (r : w64) (key val : GoString) (l : w64) (s : List EtcdKv)
    (hwf : EtcdStateWf [] s) :
    kvOf (putKv r key val l s) key = some (match kvOf s key with
      | some v => { v with modRev := r, version := v.version + W64 1, value := val, lease := l }
      | none => { key := key, createRev := r, modRev := r, version := W64 1, value := val,
                  lease := l }) := by
  unfold putKv
  rw [kvOf_eq_kvAt, concurrency.kvAt_btInsert _ s (wf_pairwise hwf) key]
  split <;> rename_i h <;> simp only [kvOf] at h ⊢ <;> rw [h]
  · have := List.find?_some h
    simp at this
    simp [this]
  · simp

/-! ## The cache and the holder's put (theorem 3) -/

/-- **When the cache tracks the holder's put**: for a cached key-value `c` that is etcd's record of
`key` before the put at `r` (`kvOf s key = some c.kv`, so modified before `r`), the cached
key-value after `Update` (`c.bump r valSl val`) is etcd's record after the put of `val` with the
lease `l` **exactly when the put keeps the cached lease** (`l = c.kv.lease`): `Update` never
changes the lease (a put without `WithLease` sets it to `0`). -/
theorem update_tracks_put (c : CachedKv) (r : w64) (valSl : GoSlice) (key val : GoString)
    (l : w64) (s : List EtcdKv) (hwf : EtcdStateWf [] s) (hrec : kvOf s key = some c.kv)
    (hmod : sint.Z c.kv.modRev < sint.Z r) :
    kvOf (applyTxnOp r s (.put key val l)).1 key = some (c.bump r valSl val).kv ↔
      l = c.kv.lease := by
  simp only [applyTxnOp]
  rw [kvOf_putKv r key val l s hwf, hrec]
  unfold CachedKv.bump
  simp only [hmod, ↓reduceIte, Option.some.injEq]
  constructor
  · intro h
    have := congrArg EtcdKv.lease h
    simpa using this
  · intro h
    subst h
    rfl

/-- **`Update` and `WithIgnoreValue`**: for the put of `key` keeping its value (`putIgnVal`, the
`Op`'s value empty), `Update` caches the `Op`'s (empty) value: the cached key-value is etcd's record
only if the record's value was empty (and the lease is kept). A cached `Get` then serves `""` for
a key whose value etcd kept: a finding (`STATUS.md`). -/
theorem update_ignoreValue (c : CachedKv) (r : w64) (valSl : GoSlice) (key : GoString)
    (l : Option w64) (s : List EtcdKv) (hwf : EtcdStateWf [] s) (hrec : kvOf s key = some c.kv)
    (hmod : sint.Z c.kv.modRev < sint.Z r) :
    kvOf (applyTxnOp r s (.putIgnVal key l)).1 key = some (c.bump r valSl []).kv ↔
      c.kv.value = [] ∧ l.getD c.kv.lease = c.kv.lease := by
  have hfind : s.find? (fun v => decide (v.key = key)) = some c.kv := hrec
  simp only [applyTxnOp, hfind, Option.map_some, Option.getD_some]
  rw [kvOf_putKv r key _ _ s hwf, hrec]
  unfold CachedKv.bump
  simp only [hmod, ↓reduceIte, Option.some.injEq]
  constructor
  · intro h
    have h1 := congrArg EtcdKv.value h
    have h2 := congrArg EtcdKv.lease h
    simp at h1 h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    rw [h1, h2]

/-- **`Update` of a key cached as absent**: the fresh key-value (`freshKv`, bumped) is etcd's
record of the new key exactly when the put has no lease. -/
theorem update_new_key (p : Loc) (keySl valSl : GoSlice) (r : w64) (key val : GoString) (l : w64)
    (s : List EtcdKv) (hwf : EtcdStateWf [] s) (habs : kvOf s key = none) (hr : 0 < sint.Z r) :
    kvOf (applyTxnOp r s (.put key val l)).1 key =
        some ((freshKv p keySl key r).bump r valSl val).kv ↔ l = W64 0 := by
  simp only [applyTxnOp]
  rw [kvOf_putKv r key val l s hwf, habs]
  unfold CachedKv.bump freshKv
  have h0 : sint.Z (W64 0) < sint.Z r := by simpa using hr
  simp only [h0, ↓reduceIte, Option.some.injEq]
  constructor
  · intro h
    have := congrArg EtcdKv.lease h
    simpa using this
  · intro h
    subst h
    simp

/-- **Out-of-order `Update`s** (two concurrent puts of one key by the holder, at `r1 < r2`, whose
`Update`s run in the opposite order): after the later put's `Update` alone, the cached key-value
has the later value and mod revision but the version incremented once, while etcd's record at
`r2` has it incremented twice; after both, the cache is right again. A cached `Get` in between
serves a record etcd never had: a finding (`STATUS.md`). -/
theorem update_out_of_order (c : CachedKv) (r1 r2 : w64) (sl1 sl2 : GoSlice) (v1 v2 : GoString)
    (h1 : sint.Z c.kv.modRev < sint.Z r1) (h12 : sint.Z r1 < sint.Z r2) :
    (c.bump r2 sl2 v2).kv = { c.kv with version := c.kv.version + W64 1, modRev := r2, value := v2 } ∧
    ((c.bump r2 sl2 v2).bump r1 sl1 v1).kv =
      { c.kv with version := c.kv.version + W64 1 + W64 1, modRev := r2, value := v2 } := by
  have h2 : sint.Z c.kv.modRev < sint.Z r2 := by omega
  unfold CachedKv.bump
  simp only [h2, ↓reduceIte]
  have h3 : ¬ sint.Z r2 < sint.Z r1 := by omega
  simp only [h3, ↓reduceIte]
  refine ⟨?_, ?_⟩ <;> first | trivial | rfl

/-! ## Cached gets (theorem 1) -/

/-- The cached get's answer of an entry whose cached key-value is its acquisition's. -/
theorem getResult_acq (o : OpFull) (e : LeaseEntry) (h : e.kv = e.acq) :
    getResult o e = if getEmpty o.base e.kvs then none
      else e.acq.map (fun v => if o.keysOnly then { v with value := [] } else v) := by
  unfold getResult
  rw [← h]
  unfold LeaseEntry.kv
  split
  · rfl
  · cases e.kvs <;> simp

section logic
variable {GF : BundledGFunctors}
variable [EM : EtcdModel GF]

/-- **A cached read is etcd's record while the lease lasts** (the corollary of theorem 1, from
`leased_value_stable`): under the protocol premise, an entry `e` with its facts (the lease key at
`e.rev` is `lv`, with the holder's lease) has, at every revision `b ≥ e.rev` at which the lease key
is present with `lv`'s create revision and in `(e.rev, b]` of which the holder committed nothing,
`key`'s record `e.acq`. -/
theorem cached_get_stable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi]
    [FfiSemantics ext ffi] [GoGlobalContext] [HeapGS HasLC.hasLC GF]
    [go.Semantics]
    (pfx key : GoString) (h : LeasingHist) (e : LeaseEntry) (b : w64) (sb : List EtcdKv)
    (hk : LeasingDataKey pfx key) (hrev : sint.Z e.rev ≤ sint.Z b)
    (hw : ∀ z : Int, sint.Z e.rev < z → z ≤ sint.Z b → h.writer z ≠ e.lease) :
    LeasingProtocol (GF := GF) pfx h ∗ entryFacts pfx key e ∗ etcdState b [] sb ⊢
      ∃ (s : List EtcdKv) (lv : EtcdKv), □ etcdState e.rev [] s ∗
        ⌜kvOf s (pfx ++ key) = some lv ∧ lv.lease = e.lease ∧
          ∀ lb, kvOf sb (pfx ++ key) = some lb → lb.createRev = lv.createRev → kvOf sb key = e.acq⌝ := by
  iintro ⟨#Hp, Hf, Hb⟩
  unfold entryFacts
  icases Hf with ⟨%s, #Hs, %Hwf, %Hacq, %lv, %Hlv, %Hlease, %Hc⟩
  ihave %Hrevs := etcdState_revs _ [] s $$ Hs
  have ha0 : 0 ≤ sint.Z e.rev := by have := Hrevs lv (kvOf_mem Hlv).1; omega
  ihave %Hok := leasingProtocol_ok pfx h $$ Hp
  ihave %Hsa := leasingProtocol_agree pfx h e.rev s ha0 $$ [$Hp $Hs]
  ihave %Hsb := leasingProtocol_agree pfx h b sb (by omega) $$ [$Hp $Hb]
  iexists s, lv
  iframe Hs
  ipureintro
  refine ⟨Hlv, Hlease, fun lb hlb hc => ?_⟩
  have hb : sint.Z b < 2 ^ 63 := by word
  rw [← Hacq]
  subst Hsa Hsb
  exact (leased_incarnation pfx key h Hok hk (sint.Z e.rev) (sint.Z b) lv lb ha0 hb Hlv hlb hc
    (sint.Z b) hrev (Int.le_refl _)).2 (fun z h1 h2 => by rw [Hlease]; exact hw z h1 h2)

end logic

/-! ## The cache's evaluation of comparisons (theorem 4) -/

section evalcmp
variable [ext : FfiSyntax]

/-- **When the cache's comparison is etcd's** (`evalCmpM_agrees`): for a comparison of one key
(`rangeEnd` empty) whose target is not the lease (`evalCmp` has no `LEASE` case), on the key's
record in a state with unique keys, `evalCmp`'s outcome (`leaseCmpHolds`) is etcd's
(`cmpHolds`), provided that, when the key is absent, the target is not the value (etcd fails a
value comparison on a missing key) and the operand is `0` (etcd compares the zero key-value,
`evalCmp` compares nothing: sign `0`). -/
theorem evalCmpM_agrees (s : List EtcdKv) (m : CmpModel) (hwf : EtcdStateWf [] s)
    (hr : m.rangeEnd = []) (hl : m.target ≠ .lease)
    (habs : kvOf s m.key = none → m.target ≠ .value ∧ m.num = W64 0) :
    leaseCmpHolds m (kvOf s m.key) = cmpHolds s m := by
  unfold cmpHolds leaseCmpHolds
  rw [hr, filter_key s m.key hwf]
  cases hk : kvOf s m.key with
  | some v =>
    simp only [Option.toList_some, List.cons_ne_nil, ↓reduceIte, List.all_cons, List.all_nil,
      Bool.and_true]
    unfold leaseCmpSign cmpKv
    cases ht : m.target <;> simp_all
  | none =>
    obtain ⟨hv, hn⟩ := habs hk
    simp only [Option.toList_none, ↓reduceIte]
    unfold leaseCmpSign cmpKv zeroKv
    cases ht : m.target <;> simp_all [int64Cmp, cmpSign]

/-- **The cache's evaluation of a transaction's comparisons is etcd's** when every comparison is of
a cached key (one key, not the lease) whose cached key-value is its record in etcd's state `s`,
with `evalCmpM_agrees`'s condition on absent keys. -/
theorem leaseEvalCmps_agrees (st : LeaseCacheSt) (s : List EtcdKv) (hwf : EtcdStateWf [] s) :
    ∀ ms : List CmpModel,
      (∀ m ∈ ms, m.rangeEnd = [] ∧ m.target ≠ .lease ∧
        (∃ e, st.entries !! m.key = some e ∧ e.kv = kvOf s m.key) ∧
        (kvOf s m.key = none → m.target ≠ .value ∧ m.num = W64 0)) →
      leaseEvalCmps st ms = (ms.all (cmpHolds s), true)
  | [], _ => rfl
  | m :: ms, hc => by
    obtain ⟨hr, hl, ⟨e, he, hkv⟩, habs⟩ := hc m (List.mem_cons_self ..)
    have ih := leaseEvalCmps_agrees st s hwf ms (fun m' hm' => hc m' (List.mem_cons_of_mem _ hm'))
    have hagree := evalCmpM_agrees s m hwf hr hl habs
    simp only [leaseEvalCmps, hr, ne_eq, not_true_eq_false, ↓reduceIte, he, List.all_cons]
    rw [hkv, hagree]
    by_cases hh : cmpHolds s m = true
    · simp [hh, ih]
    · simp [hh]

/-- **The divergences, concretely**: on a key cached as absent, `CreateRevision(k) < 5` fails in
the cache and holds in etcd; `Version(k) = 3`... (sign `0` against etcd's zero key-value): here
the `<` case; and a lease comparison is never evaluated (`LeaseValue(k) = 8` holds in the cache
for a key with lease `7`). -/
theorem evalCmpM_absent_lt (k : GoString) :
    leaseCmpHolds (compareM (cmpKeyM .create k) .lt (.num (W64 5))) none = false ∧
      cmpHolds [] (compareM (cmpKeyM .create k) .lt (.num (W64 5))) = true := by
  constructor
  · rfl
  · have h05 : (0 : Int) < sint.Z (5#64 : w64) := by decide
    simp [cmpHolds, compareM, cmpKeyM, cmpKv, zeroKv, CmpOp.holds, int64Cmp, cmpSign, h05]

theorem evalCmpM_lease (v : EtcdKv) (hv : v.lease = W64 7) :
    leaseCmpHolds (compareM (cmpKeyM .lease v.key) .eq (.num (W64 8))) (some v) = true ∧
      cmpKv (compareM (cmpKeyM .lease v.key) .eq (.num (W64 8))) v = false := by
  constructor
  · rfl
  · simp [cmpKv, compareM, cmpKeyM, hv, int64Cmp, cmpSign, CmpOp.holds]; decide

end evalcmp

end EtcdGrove
end Perennial
