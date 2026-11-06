/-
Proof of the spec of the same name (the mvcc store's compaction job, unit 5c).
The hypotheses are the callees' specs, in the order of `etc/link-lean-first-mvcc.txt`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__scheduleCompaction
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.treeIndex__Compact
public import Perennial.Proof.time
public import Spec.encoding.binary.bigEndian__PutUint64
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.newKVHasher
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.BytesToRev
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.kvHasher__WriteKeyValue
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.UnsafeSetFinishedCompact
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.kvHasher__Hash
public import Spec.go_uber_org.zap.Int64
public import Spec.go_uber_org.zap.Duration
public import Spec.go_uber_org.zap.Int
public import Spec.go_uber_org.zap.Uint32
public import Spec.go_uber_org.zap.String
public import Spec.github_com.dustin.go_humanize.Bytes
public import Spec.go_uber_org.zap.Logger__Info
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.RevToBytes
public import Spec.time.Time__Unix
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Errorf
public import Proof.ReceiptTactics
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.CmpJob

@[expose] public section

set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-! Pure facts of the job's batches: the keys a batch reads below `u64Be (rev + 1)` are revision
keys with a main at most `rev`, and one not kept is one compaction may delete (`KeyDel`). -/

theorem mvcc.sc_not_lt_prefix : ∀ (p x : List w8), ¬ go.GoStringLt (p ++ x) p
  | [], x => by intro h; unfold go.GoStringLt at h; cases h
  | a :: p, x => by
    intro h
    unfold go.GoStringLt at h
    cases h with
    | cons h' => exact mvcc.sc_not_lt_prefix p x h'
    | rel hr => exact absurd hr (Int.lt_irrefl _)

theorem mvcc.sc_u64Be_lt_inv (a b : w64) (x : List w8)
    (h : go.GoStringLt (u64Be a ++ x) (u64Be b)) : uint.Z a < uint.Z b := by
  rcases Int.lt_trichotomy (uint.Z a) (uint.Z b) with hlt | heq | hlt
  · exact hlt
  · have hab : a = b := by word
    subst hab
    exact absurd h (mvcc.sc_not_lt_prefix _ _)
  · have h2 := mvcc.RevOrder.u64Be_lt b a hlt [] x
    rw [List.append_nil] at h2
    exact absurd h (go.goStringLt_asymm h2)

theorem mvcc.sc_entry {ilog : mvcc.Log} (hcs : ∀ cs ∈ ilog, cs.length < 2 ^ 63)
    (hlen : ilog.length < 2 ^ 63) {m' : mvcc.Bucket}
    (hsub : ∀ k v, m'.lookup k = some v → (mvcc.bucketMap ilog).lookup k = some v)
    (klo : GoString) (rev : w64) (hrev0 : 0 ≤ sint.Z rev) (hrev1 : sint.Z rev < 2 ^ 63 - 1) (n : Nat)
    {p : GoString × GoString}
    (hp : p ∈ (mvcc.bucketRange m' klo (u64Be (rev + W64 1))).take n) :
    ∃ (r : mvcc.Rev) (t : Bool), p.1 = mvcc.revBytes r t ∧ 0 ≤ sint.Z r.main ∧
      0 ≤ sint.Z r.sub ∧ sint.Z r.main ≤ sint.Z rev := by
  have hp' := List.mem_of_mem_take hp
  have hmem := (((mvcc.bucketRange_eq_iff m' klo _ _).1 rfl).2 p.1 p.2).1 (by simpa using hp')
  obtain ⟨hl, -, hlt⟩ := hmem
  obtain ⟨r, i, t, hr, hi, hk⟩ := mvcc.RevOrder.bucketMap_key ilog hcs (hsub _ _ hl)
  refine ⟨⟨W64 r, W64 i⟩, t, hk, ?_, ?_, ?_⟩
  · simp only; word
  · simp only; word
  · rw [hk] at hlt
    unfold mvcc.revBytes at hlt
    rw [List.append_assoc, List.append_assoc] at hlt
    have := mvcc.sc_u64Be_lt_inv _ _ _ hlt
    simp only
    word

theorem mvcc.sc_keyDel (log : mvcc.Log) (rev : w64) (A : GMap Revision Unit)
    (hA : mvcc.keepSetIs A log (sint.Z rev)) (hrl : sint.Z rev < log.length) (r : mvcc.Rev)
    (t : Bool) (key : GoString) (hk : key = mvcc.revBytes r t) (h0 : 0 ≤ sint.Z r.main)
    (h1 : sint.Z r.main ≤ sint.Z rev) (hnot : (A.lookup (mvcc.revVal r)).isSome = false) :
    mvcc.KeyDel log (sint.Z rev) key :=
  ⟨hrl, r, t, hk, h0, h1, fun hk' => by have := (hA r).2 hk'; rw [hnot] at this; cases this⟩

/-! Counting the keys the job deletes (item 8, 2026-10-17): distinct revision keys of the job's
log up to `rev` (`sc_space`), so no more than its changes, fewer than `2 ^ 62` (`CompactSmall`,
from the certificate's time receipts: `CompactSmall_of_cert`):
`keyCompactions` (an `int`) stays non-negative, as `dbCompactionKeysCounter.Add` needs. -/

/-- `k` is the bucket key of a change of `log` at a revision at most `c`. -/
def mvcc.sc_space (log : mvcc.Log) (c : Int) (k : GoString) : Prop :=
  ∃ (r i : Nat) (ch : mvcc.Change), (r : Int) ≤ c ∧ (log.getD r [])[i]? = some ch ∧
    k = mvcc.revBytes ⟨W64 r, W64 i⟩ ch.isDel

theorem mvcc.sc_sum_range (log : mvcc.Log) : ∀ n : Nat,
    ((List.range n).map fun r => (log.getD r []).length).sum = ((log.take n).map List.length).sum
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, mvcc.sc_sum_range log n,
      List.take_add_one, List.map_append, List.sum_append]
    congr 1
    cases h : log[n]? <;> simp [List.getD_eq_getElem?_getD, h]

theorem mvcc.sc_count (log : mvcc.Log) (c : Int) (D : List GoString) (hnd : D.Nodup)
    (hD : ∀ k ∈ D, mvcc.sc_space log c k) :
    D.length ≤ ((log.take (c.toNat + 1)).map List.length).sum := by
  let U : List GoString := (List.range (c.toNat + 1)).flatMap fun r =>
    (log.getD r []).zipIdx.map fun p => mvcc.revBytes ⟨W64 r, W64 p.2⟩ p.1.isDel
  have hsub : D ⊆ U := by
    intro k hk
    obtain ⟨r, i, ch, hr, hi, rfl⟩ := hD k hk
    simp only [U, List.mem_flatMap, List.mem_range, List.mem_map]
    exact ⟨r, by omega, (ch, i), List.mem_zipIdx_iff_getElem?.2 hi, rfl⟩
  have hlen : U.length = ((log.take (c.toNat + 1)).map List.length).sum := by
    simp only [U, List.length_flatMap, List.length_map, List.length_zipIdx]
    exact mvcc.sc_sum_range log _
  calc D.length ≤ U.length := (List.subperm_of_subset hnd hsub).length_le
    _ = _ := hlen

theorem mvcc.sc_mem_bucketOfRev {r : Nat} {before : List EtcdKv} {cs : List mvcc.Change}
    {p : GoString × GoString} (h : p ∈ mvcc.bucketOfRev r before cs) :
    ∃ (i : Nat) (ch : mvcc.Change), cs[i]? = some ch ∧ p.1 = mvcc.revBytes ⟨W64 r, W64 i⟩ ch.isDel := by
  unfold mvcc.bucketOfRev at h
  rw [List.mem_filterMap] at h
  obtain ⟨⟨c, i⟩, hi, hp⟩ := h
  rw [List.mem_zipIdx_iff_getElem?] at hi
  cases hk : mvcc.changeKv (W64 r) before cs i with
  | none => rw [hk] at hp; simp at hp
  | some kv =>
    rw [hk] at hp
    simp only [Option.map_some, Option.some.injEq] at hp
    exact ⟨i, c, hi, by rw [← hp]⟩

theorem mvcc.sc_bucketMap_key (log : mvcc.Log) {k v : GoString}
    (h : (mvcc.bucketMap log).lookup k = some v) :
    ∃ (r i : Nat) (ch : mvcc.Change), r < log.length ∧ (log.getD r [])[i]? = some ch ∧
      k = mvcc.revBytes ⟨W64 r, W64 i⟩ ch.isDel := by
  unfold mvcc.bucketMap at h
  rw [mvcc.lookup_foldl_insert] at h
  cases hf : (mvcc.bucketOf log).reverse.find? (fun p => decide (p.1 = k)) with
  | none =>
    rw [hf] at h
    have h0 : (GMap.empty : GMap GoString GoString) !! k = none := rfl
    rw [h0] at h; cases h
  | some p =>
    have hp := List.mem_reverse.1 (List.mem_of_find?_eq_some hf)
    have hk : p.1 = k := by simpa using List.find?_some hf
    unfold mvcc.bucketOf at hp
    rw [List.mem_flatten] at hp
    obtain ⟨l, hl, hp⟩ := hp
    rw [List.mem_map] at hl
    obtain ⟨⟨cs, r⟩, hz, rfl⟩ := hl
    rw [List.mem_zipIdx_iff_getElem?] at hz
    simp only at hz
    have hr : r < log.length := (List.getElem?_eq_some_iff.1 hz).1
    obtain ⟨i, ch, hi, hpi⟩ := mvcc.sc_mem_bucketOfRev hp
    refine ⟨r, i, ch, hr, ?_, by rw [← hk, hpi]⟩
    rw [List.getD_eq_getElem?_getD, hz]; exact hi

/-- A key a batch reads (`sc_entry`'s), of a revision at most `rev`, is in the job's space. -/
theorem mvcc.sc_mem (log ilog : mvcc.Log) (rev : w64) (hrev : sint.Z rev < log.length)
    (hilen : ilog.length < 2 ^ 63) (hpre : log <+: ilog ∨ ilog <+: log) {m' : mvcc.Bucket}
    (hsub : ∀ k v, m'.lookup k = some v → (mvcc.bucketMap ilog).lookup k = some v)
    {k v : GoString} (hkv : m'.lookup k = some v) (r : mvcc.Rev) (t : Bool)
    (hk : k = mvcc.revBytes r t) (hm : sint.Z r.main ≤ sint.Z rev) :
    mvcc.sc_space log (sint.Z rev) k := by
  obtain ⟨r', i, ch, hr', hi, hk'⟩ := mvcc.sc_bucketMap_key ilog (hsub _ _ hkv)
  rw [hk] at hk'
  obtain ⟨-, hrr⟩ := mvcc.revBytes_inj _ _ _ _ hk'
  have hmain : r.main = W64 r' := by rw [hrr]
  have hrz : (r' : Int) ≤ sint.Z rev := by
    rw [hmain] at hm
    have : sint.Z (W64 (r' : Int)) = r' := by word
    omega
  have hget : log.getD r' [] = ilog.getD r' [] := by
    have h1 : r' < log.length := by omega
    rcases hpre with ⟨t', rfl⟩ | ⟨t', rfl⟩
    · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h1]
    · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hr']
  exact ⟨r', i, ch, hrz, by rw [hget]; exact hi, by rw [hk, ← hk']⟩

/-! The tracking of a batch (F2, stage 2): what the job deletes in a batch is what compaction at
`rev` deletes of the keys from the batch's `last` up to the next one's (`batchOk`). -/

/-- A key of the job's log has a sub below `2 ^ 63 - 1`: the next revision's sub does not overflow. -/
theorem mvcc.sc_sub (ilog : mvcc.Log) (hcs : ∀ cs ∈ ilog, cs.length < 2 ^ 63) {k v : GoString}
    (h : (mvcc.bucketMap ilog).lookup k = some v) (r : mvcc.Rev) (t : Bool)
    (hk : k = mvcc.revBytes r t) : sint.Z r.sub < 2 ^ 63 - 1 := by
  obtain ⟨r', i, ch, hr', hi, hk'⟩ := mvcc.sc_bucketMap_key ilog h
  rw [hk] at hk'
  obtain ⟨-, hrr⟩ := mvcc.revBytes_inj _ _ _ _ hk'
  have hcs' : (ilog.getD r' []).length < 2 ^ 63 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr']
    exact hcs _ (List.getElem_mem hr')
  have hil : i < (ilog.getD r' []).length := (List.getElem?_eq_some_iff.1 hi).1
  rw [hrr]
  simp only
  word

/-- The job's first `last` (zero bytes) is below every revision key. -/
theorem mvcc.sc_keyFloor0 : mvcc.keyFloor (List.replicate (sint.nat (W64 17)) (zero_val w8)) := by
  intro r t h0 h1
  right
  have e : List.replicate (sint.nat (W64 17)) (zero_val w8) =
      u64Be (W64 0) ++ ([W8 0] ++ u64Be (W64 0)) := by decide
  rw [e]
  unfold mvcc.revBytes
  rw [List.append_assoc, List.append_assoc]
  by_cases hm : uint.Z r.main = 0
  · have : r.main = W64 0 := by word
    rw [this]
    apply mvcc.RevOrder.u64Be_eq_lt
    simp only [List.singleton_append]
    exact (go.goStringLt_cons_iff _ _ _ _).2 (Or.inl (by decide))
  · exact mvcc.RevOrder.u64Be_lt _ _ (by word) _ _

/-- Compaction at `c` deletes the same keys of the job's log and of the writer's (one a prefix of
the other, both longer than `c`). -/
theorem mvcc.sc_keyDel_iff (log ilog : mvcc.Log) (c : Int) (hbl : mvcc.LogB log)
    (hbi : mvcc.LogB ilog) (hpre : log <+: ilog ∨ ilog <+: log) (hc0 : -1 ≤ c)
    (hl : c < log.length) (hil : c < ilog.length) (k : GoString) :
    mvcc.KeyDel ilog c k ↔ mvcc.KeyDel log c k := by
  rcases hpre with h | h
  · exact mvcc.KeyDel_prefix log ilog h hbi c hc0 hl k
  · exact (mvcc.KeyDel_prefix ilog log h hbl c hc0 hil k).symm

/-- A kept key is not deleted. -/
theorem mvcc.sc_kept (log : mvcc.Log) (rev : w64) (A : GMap Revision Unit)
    (hA : mvcc.keepSetIs A log (sint.Z rev)) (r : mvcc.Rev) (t : Bool) (key : GoString)
    (hk : key = mvcc.revBytes r t) (hkeep : (A.lookup (mvcc.revVal r)).isSome = true) :
    ¬ mvcc.KeyDel log (sint.Z rev) key := by
  rintro ⟨-, r', t', hk', -, -, hnk⟩
  rw [hk] at hk'
  obtain ⟨-, rfl⟩ := mvcc.revBytes_inj _ _ _ _ hk'
  exact hnk ((hA r).1 hkeep)

/-- In a sorted batch, every key is at or below the last. -/
theorem mvcc.sc_le_last {L : List (GoString × GoString)}
    (hs : (L.map Prod.fst).Pairwise go.GoStringLt) (hne : L ≠ []) {p : GoString × GoString}
    (hp : p ∈ L) : go.GoStringLe p.1 (L.getLast hne).1 := by
  have he := List.dropLast_concat_getLast hne
  rw [← he] at hs hp
  rw [List.map_append, List.pairwise_append] at hs
  rcases List.mem_append.1 hp with h | h
  · exact Or.inr (hs.2.2 _ (List.mem_map.2 ⟨_, h, rfl⟩) _ (by simp))
  · rw [List.mem_singleton.1 h]; exact Or.inl rfl

/-- A key of a sorted range at or below the last of its first `n`: among them. -/
theorem mvcc.sc_mem_take_of_le {Lr : List (GoString × GoString)}
    (hs : (Lr.map Prod.fst).Pairwise go.GoStringLt) (n : Nat) (hne : Lr.take n ≠ [])
    {p : GoString × GoString} (hp : p ∈ Lr) (hle : go.GoStringLe p.1 ((Lr.take n).getLast hne).1) :
    p ∈ Lr.take n := by
  have hl := List.getLast_mem hne
  rw [← List.take_append_drop n Lr] at hs hp
  rw [List.map_append, List.pairwise_append] at hs
  rcases List.mem_append.1 hp with h | h
  · exact h
  · exfalso
    have hlt := hs.2.2 _ (List.mem_map.2 ⟨_, hl, rfl⟩) _ (List.mem_map.2 ⟨_, h, rfl⟩)
    rcases hle with he | hlt'
    · rw [he] at hlt; exact go.goStringLt_irrefl _ hlt
    · exact go.goStringLt_asymm hlt hlt'

/-- Not above `b`: below `b`'s successor (its sub not at the top). -/
theorem mvcc.sc_lt_succ {a b : mvcc.Rev} (ha : 0 ≤ sint.Z a.main ∧ 0 ≤ sint.Z a.sub)
    (hb : 0 ≤ sint.Z b.sub) (hbs : sint.Z b.sub < 2 ^ 63 - 1) (h : ¬ mvcc.Rev.lt b a) :
    mvcc.Rev.lt a ⟨b.main, b.sub + W64 1⟩ := by
  unfold mvcc.Rev.lt at h ⊢
  simp only
  have hs : sint.Z (b.sub + W64 1) = sint.Z b.sub + 1 := by word
  rw [hs]
  by_cases hm : a.main = b.main
  · right
    refine ⟨hm, ?_⟩
    have : ¬ sint.Z b.sub < sint.Z a.sub := fun h' => h (Or.inr ⟨hm.symm, h'⟩)
    omega
  · left
    have hne : sint.Z a.main ≠ sint.Z b.main := fun h' => hm (by word)
    have : ¬ sint.Z b.main < sint.Z a.main := fun h' => h (Or.inl h')
    omega

/-- Below `b`'s successor: below `b`, or `b`. -/
theorem mvcc.sc_lt_succ_inv {a b : mvcc.Rev} (hb : 0 ≤ sint.Z b.sub)
    (hbs : sint.Z b.sub < 2 ^ 63 - 1) (h : mvcc.Rev.lt a ⟨b.main, b.sub + W64 1⟩) :
    mvcc.Rev.lt a b ∨ a = b := by
  unfold mvcc.Rev.lt at h ⊢
  simp only at h
  have hs : sint.Z (b.sub + W64 1) = sint.Z b.sub + 1 := by word
  rw [hs] at h
  rcases h with h | ⟨hm, hlt⟩
  · exact Or.inl (Or.inl h)
  · by_cases he : sint.Z a.sub = sint.Z b.sub
    · right
      have hse : a.sub = b.sub := by word
      cases a; cases b; simp_all
    · exact Or.inl (Or.inr ⟨hm, by omega⟩)

/-- **A batch of the job is `batchOk`** (the keys it deletes, `Db`, are compaction's among the
batch's keys `L`, all of them; the backend's view `p0`, read by the range, `p'` after the
deletes): the last batch (short, the whole range below `rev + 1`), at `(rev + 1, 0)`; a full one,
at the successor of its last key's revision. -/
theorem mvcc.sc_batchOk (log ilog : mvcc.Log) (rev : w64) (A : GMap Revision Unit)
    (hA : mvcc.keepSetIs A log (sint.Z rev)) (hbl : mvcc.LogB log) (hbi : mvcc.LogB ilog)
    (hpre : log <+: ilog ∨ ilog <+: log) (hr0 : 0 ≤ sint.Z rev) (hrz : sint.Z rev < 2 ^ 63 - 1)
    (hl : sint.Z rev < log.length) (hil : sint.Z rev < ilog.length)
    (bs : GoString) (m' p0 p' : mvcc.Bucket) (hm : ∀ k, m'.lookup k = p0.lookup k)
    (lim : Nat) (L : List (GoString × GoString))
    (hL : (mvcc.bucketRange m' bs (u64Be (rev + W64 1))).take lim = L)
    (hLent : ∀ p ∈ L, ∃ (r : mvcc.Rev) (t : Bool), p.1 = mvcc.revBytes r t ∧
      0 ≤ sint.Z r.main ∧ 0 ≤ sint.Z r.sub ∧ sint.Z r.main ≤ sint.Z rev ∧
      sint.Z r.sub < 2 ^ 63 - 1)
    (Db : List GoString)
    (hDb : ∀ k ∈ Db, mvcc.KeyDel log (sint.Z rev) k ∧ k ∈ L.map Prod.fst)
    (hcomp : ∀ p ∈ L, mvcc.KeyDel log (sint.Z rev) p.1 → p.1 ∈ Db)
    (hp' : ∀ k, p'.lookup k = if k ∈ Db then none else p0.lookup k)
    (hkeys : ∀ k x, p0.lookup k = some x →
      ∃ e ∈ mvcc.logEnts ilog 0 ilog.length, mvcc.entKey e = k)
    (cur' : mvcc.Rev)
    (hcase : (L.length < lim ∧ cur' = ⟨rev + W64 1, W64 0⟩) ∨
      (∃ (hne : L ≠ []) (r : mvcc.Rev) (t : Bool), (L.getLast hne).1 = mvcc.revBytes r t ∧
        cur' = ⟨r.main, r.sub + W64 1⟩)) :
    mvcc.batchOk ilog (sint.Z rev) bs p0 p' cur' := by
  subst hL
  have hkd := mvcc.sc_keyDel_iff log ilog (sint.Z rev) hbl hbi hpre (by omega) hl hil
  have hrs := (mvcc.bucketRange_eq_iff m' bs (u64Be (rev + W64 1)) _).1 rfl
  have hsrt : (((mvcc.bucketRange m' bs (u64Be (rev + W64 1))).take lim).map Prod.fst).Pairwise
      go.GoStringLt := hrs.1.sublist (List.Sublist.map _ (List.take_sublist _ _))
  have hbnd := mvcc.logEnts_bounds ilog hbi.1 hbi.2 0 ilog.length (Nat.le_refl _)
  have hinR : ∀ e ∈ mvcc.logEnts ilog 0 ilog.length, mvcc.KeyDel ilog (sint.Z rev) (mvcc.entKey e) →
      go.GoStringLe bs (mvcc.entKey e) → p0.lookup (mvcc.entKey e) ≠ none →
      ∃ v, (mvcc.entKey e, v) ∈ mvcc.bucketRange m' bs (u64Be (rev + W64 1)) := by
    intro e he hd hle hne
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hne
    refine ⟨v, (hrs.2 _ _).2 ⟨by rw [hm]; exact hv, hle, ?_⟩⟩
    obtain ⟨-, r, t, hk, h0, h1, -⟩ := hd
    rw [hk]
    unfold mvcc.revBytes
    rw [List.append_assoc, List.append_assoc]
    have := mvcc.RevOrder.u64Be_lt r.main (rev + W64 1) (by word)
      ([W8 95] ++ (u64Be r.sub ++ if t then [W8 116] else [])) []
    rw [List.append_nil] at this
    exact this
  refine ⟨fun k => decide (k ∈ Db), ?_, ?_, ?_, ?_⟩
  · intro k hk
    exact (hkd k).2 (hDb k (of_decide_eq_true hk)).1
  · intro e he hk
    obtain ⟨-, hkL⟩ := hDb _ (of_decide_eq_true hk)
    obtain ⟨p, hp, hpk⟩ := List.mem_map.1 hkL
    obtain ⟨r, t, hr, h0, h1, h2, h3⟩ := hLent p hp
    have hre : e.rev = r := (mvcc.revBytes_inj _ _ _ _ (hpk.symm.trans hr)).2
    rcases hcase with ⟨-, rfl⟩ | ⟨hne, rl, tl, hlast, rfl⟩
    · unfold mvcc.Rev.lt
      left
      rw [hre]
      show sint.Z r.main < sint.Z (rev + W64 1)
      word
    · obtain ⟨rl', tl', hl', l0, l1, -, l3⟩ := hLent _ (List.getLast_mem hne)
      obtain ⟨-, hrl⟩ := mvcc.revBytes_inj _ _ _ _ (hlast.symm.trans hl')
      subst rl'
      have hle := mvcc.sc_le_last hsrt hne hp
      rw [hpk, hlast] at hle
      exact mvcc.sc_lt_succ (hbnd e he) l1 l3 (mvcc.not_lt_of_key_le (hbnd e he) ⟨l0, l1⟩ hle)
  · intro k
    simp only [hp' k, decide_eq_true_eq]
  · intro e he hd hle hlt hne
    apply decide_eq_true
    obtain ⟨v, hv⟩ := hinR e he hd hle hne
    have hmemL : (mvcc.entKey e, v) ∈ (mvcc.bucketRange m' bs (u64Be (rev + W64 1))).take lim := by
      rcases hcase with ⟨hlt', -⟩ | ⟨hne', rl, tl, hlast, rfl⟩
      · rw [List.length_take] at hlt'
        rw [List.take_of_length_le (by omega)]
        exact hv
      · obtain ⟨rl', tl', hl', l0, l1, -, l3⟩ := hLent _ (List.getLast_mem hne')
        obtain ⟨-, hrl⟩ := mvcc.revBytes_inj _ _ _ _ (hlast.symm.trans hl')
        subst rl'
        apply mvcc.sc_mem_take_of_le hrs.1 lim hne' hv
        show go.GoStringLe (mvcc.entKey e) _
        rw [hlast]
        rcases mvcc.sc_lt_succ_inv l1 l3 hlt with hlt2 | heq
        · exact Or.inr (mvcc.revBytes_lt_of_lt (hbnd e he) ⟨l0, l1⟩ hlt2 _ _)
        · have hpl := List.mem_of_mem_take (List.getLast_mem hne')
          have hml := ((hrs.2 _ _).1 hpl).1
          obtain ⟨e2, he2, hk2⟩ := hkeys _ _ (by rw [← hm]; exact hml)
          rw [hlast] at hk2
          obtain ⟨-, hr2⟩ := mvcc.revBytes_inj _ _ _ _ hk2
          have he2e := mvcc.logEnts_rev_inj hbi he2 he (by rw [hr2, heq])
          rw [← he2e]
          exact Or.inl hk2
    exact hcomp _ hmemL ((hkd _).1 hd)

/-- **A batch's deletes so far** (its first `n` keys of `L`): the backend's view `pn` is the
range's `p0` without the keys `Db`, which are compaction's at `c` among them, all of them. -/
def mvcc.sc_pnOk (log : mvcc.Log) (c : Int) (L : List (GoString × GoString)) (n : Nat)
    (p0 pn : mvcc.Bucket) (Db : List GoString) : Prop :=
  (∀ k, pn.lookup k = if k ∈ Db then none else p0.lookup k) ∧
    (∀ k ∈ Db, mvcc.KeyDel log c k ∧ k ∈ (L.take n).map Prod.fst) ∧
    (∀ p ∈ L.take n, mvcc.KeyDel log c p.1 → p.1 ∈ Db)

theorem mvcc.sc_pnOk_zero (log : mvcc.Log) (c : Int) (L : List (GoString × GoString))
    (p0 : mvcc.Bucket) : mvcc.sc_pnOk log c L 0 p0 p0 [] :=
  ⟨fun k => by simp, fun k hk => by simp at hk, fun p hp => by simp at hp⟩

theorem mvcc.sc_pnOk_keep {log : mvcc.Log} {c : Int} {L : List (GoString × GoString)} {n : Nat}
    {p0 pn : mvcc.Bucket} {Db : List GoString} {e : GoString × GoString} (He : L[n]? = some e)
    (hnk : ¬ mvcc.KeyDel log c e.1) (h : mvcc.sc_pnOk log c L n p0 pn Db) :
    mvcc.sc_pnOk log c L (n + 1) p0 pn Db := by
  obtain ⟨h1, h2, h3⟩ := h
  unfold mvcc.sc_pnOk
  rw [List.take_add_one, He]
  refine ⟨h1, fun k hk => ?_, fun p hp hd => ?_⟩
  · obtain ⟨a, b⟩ := h2 k hk
    refine ⟨a, ?_⟩
    simp only [Option.toList_some, List.map_append, List.mem_append]
    exact Or.inl b
  · simp only [Option.toList_some, List.mem_append, List.mem_singleton] at hp
    rcases hp with hp | rfl
    · exact h3 p hp hd
    · exact absurd hd hnk

theorem mvcc.sc_pnOk_del {log : mvcc.Log} {c : Int} {L : List (GoString × GoString)} {n : Nat}
    {p0 pn : mvcc.Bucket} {Db : List GoString} {e : GoString × GoString} (He : L[n]? = some e)
    (hk : mvcc.KeyDel log c e.1) (h : mvcc.sc_pnOk log c L n p0 pn Db) :
    mvcc.sc_pnOk log c L (n + 1) p0 (GMap.delete e.1 pn) (e.1 :: Db) := by
  obtain ⟨h1, h2, h3⟩ := h
  unfold mvcc.sc_pnOk
  rw [List.take_add_one, He]
  refine ⟨fun k => ?_, fun k hk' => ?_, fun p hp hd => ?_⟩
  · by_cases hke : e.1 = k
    · subst hke
      rw [GMap.lookup_delete]
      simp
    · rw [GMap.lookup_delete_ne _ hke, h1 k]
      have : k ≠ e.1 := Ne.symm hke
      simp [List.mem_cons, this]
  · rcases List.mem_cons.1 hk' with rfl | hk'
    · refine ⟨hk, ?_⟩
      simp
    · obtain ⟨a, b⟩ := h2 k hk'
      refine ⟨a, ?_⟩
      simp only [Option.toList_some, List.map_append, List.mem_append]
      exact Or.inl b
  · simp only [Option.toList_some, List.mem_append, List.mem_singleton] at hp
    rcases hp with hp | rfl
    · exact List.mem_cons_of_mem _ (h3 p hp hd)
    · simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem mvcc.store.scheduleCompaction.wp_proof
    (h0 : mvcc.treeIndex.Compact.spec (GF := GF) (hG := hG))
    (h2 : binary.bigEndian.PutUint64.spec (GF := GF) (hG := hG))
    (h3 : mvcc.newKVHasher.spec (GF := GF) (hG := hG))
    (h4 : mvcc.BytesToRev.spec (GF := GF) (hG := hG))
    (h5 : mvcc.kvHasher.WriteKeyValue.spec (GF := GF) (hG := hG))
    (h6 : mvcc.UnsafeSetFinishedCompact.spec (GF := GF) (hG := hG))
    (h7 : mvcc.kvHasher.Hash.spec (GF := GF) (hG := hG))
    (h8 : zap.Int64.spec (GF := GF) (hG := hG))
    (h9 : zap.Duration.spec (GF := GF) (hG := hG))
    (h10 : zap.Int'.spec (GF := GF) (hG := hG))
    (h11 : zap.Uint32.spec (GF := GF) (hG := hG))
    (h12 : zap.String.spec (GF := GF) (hG := hG))
    (h13 : go_humanize.Bytes.spec (GF := GF) (hG := hG))
    (h14 : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (h15 : mvcc.RevToBytes.spec (GF := GF) (hG := hG))
    (h16 : time.Time.Unix.spec (GF := GF) (hG := hG)) :
    mvcc.store.scheduleCompaction.spec (GF := GF) (hG := hG) := by
  intro s γ rev prev q o
  wp_start as ⟨#Hjob, Hfs, #Hstopch, Htok⟩
  iunfold mvcc.compactJobPre at Hjob
  icases Hjob with ⟨#Hs, -, %Hcmp, #Hlb, #HcLb, #HsupM, %log, #Hcert, #Hnevc, %Hrev'⟩
  have Hrev1 : 1 ≤ sint.Z rev := Hrev'.1
  have Hrev : 0 ≤ sint.Z rev ∧ sint.Z rev < log.length := ⟨by omega, Hrev'.2⟩
  ihave %Hsmall : ⌜mvcc.CompactSmall log (sint.Z rev)⌝ $$ []
  · iapply mvcc.CompactSmall_of_cert s γ log (sint.Z rev) $$ [Hs Hcert]
    iframe Hs Hcert
  ihave #Hs0 := Hs
  iunfold mvcc.isStore at Hs0
  iNamed Hs0
  -- the compaction's objects, read through the job's leased share (M2, the storage side, item 17)
  icases mvcc.fieldShareAt_acc s γ q o $$ Hfs with ⟨Hflds, #Hph, Hfclose⟩
  iunfold mvcc.storeFields at Hflds
  iNamed Hflds
  obtain ⟨b, ti, ssched, sstop⟩ := o
  iunfold mvcc.physOk at Hph
  iNamed Hph
  try simp only
  -- (question 5's core stage) the store's compaction facts: the write right's invariant (the swap
  -- of the key for the compaction keys' write right), its registration, the write-back supply
  have hcmpM : mvcc.kbCmpM γ.kb := mvcc.storeCmp_cmpM γ Hcmp
  icases (mvcc.physCmp_on s γ hcmpM).1 $$ HmwP with ⟨#Hmwi, #Hrg⟩
  -- (M2, the storage side, Q1 (a)) the supply from the job's premise
  ihave #Hsup := (mvcc.kbWTSupplyM_on γ.kb hcmpM).1 $$ HsupM
  ihave #Hswk := mvcc.mwSwap_of_inv γ iprop(True) $$ Hmwi
  -- the store's contract with its compaction on (its tokens, lock resource, slots, write right)
  ihave #Hbk' := mvcc.isKeyBackendG_cmpOn _ s γ _ _ _ Hcmp $$ Hbk
  iunfold mvcc.isKeyBackendG at Hbk'
  icases Hbk' with ⟨%bi, %Hbi, -, -, #HBT, #HForce, #HSize, #HSizeU, #HCmp⟩
  icases HCmp $$ [] with ⟨#HLSR, #HUSR, -⟩
  · ipureintro; trivial
  subst Hbi
  ihave Hmi : (mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hmi with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    ⟨%hIdx, #HIdxG, #HIdx⟩, ⟨%hPause, #HPauseG, #HPause⟩, ⟨%hTot, #HTotG, #HTot⟩,
    ⟨%cKeys, #HKeysG, #HKeys⟩, ⟨%gLast, #HLastG, #HLast⟩, -⟩
  ihave #Htime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  iunfold mvcc.compactTok at Htok
  icases Htok with ⟨⟨%c', %hc', Htok⟩, Hjr⟩
  -- the job's budgets (question 5's core stage): its reader's token, the safe-range slot
  icases (mvcc.compactJobResM_on γ.kb hcmpM).1 $$ Hjr with ⟨HRT, HSR, Hjob⟩
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply HLSR $$ [$HSR] as HSRh
  (try wp_auto)
  wp_apply time.wp_Now as %t0 -
  (try wp_auto)
  wp_apply h0 ti γ.idx rev log c' $$ [$Htok] as %keep ⟨Htok, %A, Hkeep, %HA⟩
  · iframe #; ipureintro; exact ⟨hc', Hrev.1, Hrev.2⟩
  (try wp_auto)
  iunfold histSpec at HIdx HPause HTot
  iunfold counterSpec at HKeys
  icases HKeys with ⟨-, -, #HKeysAdd⟩
  iunfold gaugeSetSpec at HLast
  wp_apply time.wp_Since as %d1 -
  (try wp_auto)
  wp_apply HIdx
  (try wp_auto)
  wp_apply time.wp_Now as %t1 -
  (try wp_auto)
  wp_apply wp_slice_make2 (V := w8) (W64 8) as %endS ⟨HendS, -⟩
  · ipureintro; decide
  (try wp_auto)
  wp_apply (wp_bePutUint64 h2 endS _ (rev + W64 1) (by simp)) $$ [$HendS] as HendS
  (try wp_auto)
  ihave #HcfgS := Hcfg
  iStructNamedSuffix HcfgS "C"
  (try wp_auto)
  wp_apply h3 as %hv %Hhv
  (try wp_auto)
  wp_apply wp_slice_make2 (V := w8) (W64 17) as %lastS ⟨HlastS, HlastC⟩
  · ipureintro; decide
  (try wp_auto)
  -- the schema's `Key` bucket
  ihave #Hsch : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema $$ []
  · iPkgInit
  ihave Hsi : (go_etcd_io.etcd.server.v3.storage.schema.schemaInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hsch
  icases Hsi with ⟨-, -, -, ⟨%bK, #HKeyG, -⟩, -⟩
  ihave #Hc2 := Hcert
  iunfold mvcc.idxCert at Hc2
  icases Hc2 with ⟨-, %Hlwf, -⟩
  have Hrz : sint.Z rev < 2 ^ 63 - 1 := by have := Hrev.2; have := Hlwf.2.1; omega
  irename «end» => endP
  -- the batches
  -- `D`: the keys deleted so far (item 8): distinct keys of the job's space, below the cursor
  ihave HI : iprop(∃ (lst : GoSlice) (bs : List w8) (kc : w64) (hv' : kvHasher) (D : List GoString),
      "last" ∷ last_ptr ↦ lst ∗ "HlastS" ∷ lst ↦* bs ∗ "HlastC" ∷ ownSliceCap w8 lst (DFrac.own 1) ∗
      "%Hbs" ∷ ⌜bs.length = 17⌝ ∗ "keyCompactions" ∷ keyCompactions_ptr ↦ kc ∗
      "h" ∷ (h_ptr ↦ hv' ∗ ⌜mvcc.kvHasherOk hv'⌝) ∗
      "%HD" ∷ ⌜sint.Z kc = D.length ∧ D.Nodup ∧
        ∀ k ∈ D, mvcc.sc_space log (sint.Z rev) k ∧ go.GoStringLt k bs⌝ ∗
      "Hjc" ∷ mvcc.jobCurAt γ.kb (sint.Z rev) bs)
    $$ [last HlastS HlastC keyCompactions h Hjob]
  · iexists lastS, List.replicate (sint.nat (W64 17)) (zero_val w8), W64 0, hv, []
    simp only [named]
    ihave Hjc := mvcc.jobCurAt_start γ.kb (sint.Z rev) _ mvcc.sc_keyFloor0 $$ Hjob
    iframe
    ipureintro; simp [Hhv]; decide
  wp_for HI
  wp_apply +noauto time.wp_Now as %tst -
  -- (question 5's core stage) a receipt for the session's write-back token
  wp_take_receipt as Hr1
  imod mvcc.kbWTSupply_take γ.kb $$ [$Hsup $Hr1] with Hwt1
  (try wp_auto)
  wp_apply HBT as %bt #Hbt
  (try wp_auto)
  iunfold mvcc.isBatchTxG at Hbt
  icases Hbt with ⟨%Locked, %LockedO, #HbtS, -⟩
  ihave #HbtS0 := HbtS
  iunfold mvcc.batchTxSpecG at HbtS0
  icases HbtS0 with ⟨-, -, -, -, -, #HLockOut, #HRng, -⟩
  wp_bind (App (Val #(methods bt.ty _ bt.v)) (Val #()))
  iapply HLockOut $$ [HRT Hwt1]
  · iframe HRT Hwt1; iframe #
  inext
  iintro ⟨Hlocked, HW, HP, HRT⟩
  imod mvcc.storeW_open s γ ⊤ (by solve_ndisj) $$ Hrg HW with ⟨HW, #Hreg⟩
  -- (question 5's core stage, part (1)) a later credit for the last batch's swap of the key
  wp_auto_lc 1
  iunfold mvcc.writerRes at HW
  icases HW with ⟨%ilog, HW⟩
  iNamedSuffix HW "W"
  -- the writer's view's bucket `mW`, thin of `ilog`'s (M2's item 15)
  iunfold mvcc.bucketViewL at HbvW
  icases HbvW with ⟨%mW, HbvW, #HblW⟩
  ihave #HthW := mvcc.bucketLog_thin γ ilog mW $$ HblW
  ihave #HcW' := HcertW
  ihave %Hpre : ⌜log <+: ilog ∨ ilog <+: log⌝ $$ []
  · iapply mvcc.idxCert_prefix $$ [Hcert HcertW]
    iframe Hcert HcertW
  iunfold mvcc.idxCert at HcW'
  icases HcW' with ⟨-, %HilWf, -⟩
  -- (F2, stage 2) the batch's session: the client's half of the backend's view, at `p0`
  imod mvcc.jobSess_open γ ilog (sint.Z rev) bs hcmpM Hrev1 $$ [HtrkW Hjc HcLb] with ⟨%p0, HPV, Hsess⟩
  · iframe HtrkW Hjc HcLb
  ispecialize HRng $$ []
  · ipureintro; trivial
  wp_bind (App (App (App (App (Val #(methods bt.ty _ bt.v)) (Val #bK)) (Val #lst)) (Val #endS)) (Val #_))
  iapply HRng $$ %(1 : Qp).half.half %mW %p0 %bK %lst %endS %bs %(u64Be (rev + W64 1))
    %scfg.CompactionBatchLimit' %(DFrac.own 1) %(DFrac.own 1) [] [Hlocked HbvW HPV HlastS HendS]
  · ipureintro
    refine ⟨Hcfgl.1, Hcfgl.2, ?_⟩
    intro hn
    have := congrArg List.length hn
    simp [u64Be_length] at this
  · iframe; iframe #
  inext
  -- (the backend-compaction stage, R2-3) the session ends in the range's token `U`, at the budget
  -- `limit + 1`: a delete or the `Meta` put spends one, `Unlock` takes any
  iintro %ks %vs ⟨HbvW, HPV, HlastS, HendS, %m', %Rd, %U, HU, #Hthin0, %Hpvx, #Hcap, #Hcap2, #Hpv,
    #HDelC, #HMetaC, #HUnlU⟩
  ihave #Hthin := mvcc.snapThin_trans (mvcc.bucketMap ilog) mW m' _ $$ [HthW Hthin0]
  · iframe HthW Hthin0
  ihave HbvW : mvcc.bucketViewL γ (1 : Qp).half.half ilog $$ [HbvW]
  · iunfold mvcc.bucketViewL; iexists mW; iframe HbvW; iexact HblW
  (try wp_auto)
  rename_i igo
  irename : (igo ↦ zero_val w64 : IProp GF) => Higo
  iunfold mvcc.snapThin at Hthin
  icases Hthin with ⟨%Hsub, -⟩
  (try simp only [List.foldl_nil] at Hsub)
  generalize hL : (mvcc.bucketRange m' bs (u64Be (rev + W64 1))).take
    (sint.Z scfg.CompactionBatchLimit').toNat = L
  have HLent : ∀ p ∈ L, ∃ (r : mvcc.Rev) (t : Bool), p.1 = mvcc.revBytes r t ∧ 0 ≤ sint.Z r.main ∧
      0 ≤ sint.Z r.sub ∧ sint.Z r.main ≤ sint.Z rev := by
    intro p hp
    rw [← hL] at hp
    exact mvcc.sc_entry HilWf.2.2 HilWf.2.1 Hsub bs rev Hrev.1 Hrz _ hp
  have HLmem0 : ∀ p ∈ L, m'.lookup p.1 = some p.2 := by
    intro p hp
    rw [← hL] at hp
    exact ((((mvcc.bucketRange_eq_iff m' bs _ _).1 rfl).2 p.1 p.2).1
      (by simpa using List.mem_of_mem_take hp)).1
  have HLent' : ∀ p ∈ L, ∃ (r : mvcc.Rev) (t : Bool), p.1 = mvcc.revBytes r t ∧
      0 ≤ sint.Z r.main ∧ 0 ≤ sint.Z r.sub ∧ sint.Z r.main ≤ sint.Z rev ∧
      sint.Z r.sub < 2 ^ 63 - 1 := by
    intro p hp
    obtain ⟨r, t, hk, h0, h1, h2⟩ := HLent p hp
    exact ⟨r, t, hk, h0, h1, h2, mvcc.sc_sub ilog HilWf.2.2 (Hsub _ _ (HLmem0 p hp)) r t hk⟩
  have HLsrt : (L.map Prod.fst).Pairwise go.GoStringLt := by
    rw [← hL]
    exact (((mvcc.bucketRange_eq_iff _ _ _ _).1 rfl).1).sublist
      (List.Sublist.map _ (List.take_sublist _ _))
  have HLmem : ∀ p ∈ L, m'.lookup p.1 = some p.2 ∧ go.GoStringLe bs p.1 := by
    intro p hp
    rw [← hL] at hp
    have := (((mvcc.bucketRange_eq_iff m' bs _ _).1 rfl).2 p.1 p.2).1
      (by simpa using List.mem_of_mem_take hp)
    exact ⟨this.1, this.2.1⟩
  have Hlt_le : ∀ {a b c : GoString}, go.GoStringLt a b → go.GoStringLe b c → go.GoStringLt a c := by
    intro a b c h1 h2
    rcases h2 with rfl | h2
    · exact h1
    · exact go.goStringLt_trans h1 h2
  iunfold mvcc.pairVals at Hpv
  icases Hpv with ⟨%kss, %vss, #Hks, #Hvs, %Hlens, #Hel⟩
  ihave %Hvl := ownSlice_len _ _ _ $$ Hvs
  ihave %Hkl := ownSlice_len _ _ _ $$ Hks
  have h00 : sint.nat (W64 0) = 0 := by decide
  ihave IH : iprop(∃ (n k kc : w64) (hv : kvHasher) (rv : Revision) (D : List GoString)
      (pn : mvcc.Bucket) (Db : List GoString),
      "i" ∷ i_ptr ↦ n ∗ "Higo" ∷ igo ↦ k ∗ "keyCompactions" ∷ keyCompactions_ptr ↦ kc ∗
      "h" ∷ (h_ptr ↦ hv ∗ ⌜mvcc.kvHasherOk hv⌝) ∗ "rev" ∷ rev_ptr ↦ rv ∗
      "Hlocked" ∷ (∃ c : Nat, U c ∗ ⌜L.length + 1 ≤ c + sint.nat n⌝) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ L.length⌝ ∗
      "%HD" ∷ ⌜sint.Z kc = D.length ∧ D.Nodup ∧ (∀ k ∈ D, mvcc.sc_space log (sint.Z rev) k) ∧
        (∀ k ∈ D, ∀ j (hj : j < L.length), sint.nat n ≤ j → go.GoStringLt k (L[j]).1) ∧
        (sint.Z n = 0 ∨ ∀ k ∈ D, go.GoStringLt k
          (mvcc.revBytes (mvcc.revOf ⟨rv.Main', rv.Sub' + W64 1⟩) false))⌝ ∗
      "HPV" ∷ mvcc.storePV γ pn ∗
      "%HPn" ∷ ⌜mvcc.sc_pnOk log (sint.Z rev) L (sint.nat n) p0 pn Db ∧
        (sint.nat n = 0 ∨ ∀ e, L[sint.nat n - 1]? = some e →
          ∃ (r : mvcc.Rev) (t : Bool), e.1 = mvcc.revBytes r t ∧ rv = mvcc.revVal r)⌝)
    $$ [i Higo keyCompactions h rev HU HPV]
  · iexists W64 0, _, _, _, _, D, p0, []
    simp only [named]
    ihave HU : iprop(∃ c : Nat, U c ∗ ⌜L.length + 1 ≤ c + sint.nat (W64 0)⌝) $$ [HU]
    · iexists _; iframe HU; ipureintro
      have : L.length ≤ (sint.Z scfg.CompactionBatchLimit').toNat := by
        rw [← hL]; exact List.length_take_le _ _
      have h0 : sint.nat (W64 0) = 0 := by decide
      rw [h0]; omega
    iframe
    ipureintro
    refine ⟨⟨by decide, by simp⟩, ⟨HD.1, HD.2.1, fun k hk => (HD.2.2 k hk).1, ?_, Or.inl (by decide)⟩,
      by rw [h00]; exact mvcc.sc_pnOk_zero _ _ _ _, Or.inl h00⟩
    intro k hk j hj _
    exact Hlt_le (HD.2.2 k hk).2 (HLmem _ (List.getElem_mem hj)).2
  wp_for IH
  wp_if_destruct
  · have hlen1 : kss.length = L.length := by simpa using Hlens.1
    have hlen2 : vss.length = L.length := by simpa using Hlens.2
    have Hlt : sint.nat n < L.length := by rw [← hlen1, Hkl.1]; word
    have Hbnd2 : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z ks.len := ⟨Hn.1, Hif⟩
    simp only [Hbnd2, and_self, ↓reduceIte]
    obtain ⟨e, He⟩ : ∃ e, L[sint.nat n]? = some e := ⟨_, List.getElem?_eq_getElem Hlt⟩
    icases (BigSepL.bigSepL_lookup_acc He).1 $$ Hel with ⟨⟨%ksl, %vsl, %Hkv, #Hksl, #Hvsl⟩, -⟩
    obtain ⟨r, t, Hk, Hr0, Hs0, Hrm⟩ := HLent e (List.mem_of_getElem? He)
    wp_apply wp_load_slice_index ks (sint.Z n) kss DFrac.discard ksl Hn.1 $$ [$Hks] as -
    · ipureintro; exact Hkv.1
    (try wp_auto)
    simp only [Hbnd2, and_self, ↓reduceIte]
    wp_apply wp_load_slice_index ks (sint.Z n) kss DFrac.discard ksl Hn.1 $$ [$Hks] as -
    · ipureintro; exact Hkv.1
    have Hkb : e.1 = mvcc.revBytes r false ++ (if t then [W8 116] else []) := by
      rw [Hk]; cases t <;> simp [mvcc.revBytes]
    -- (backend-cmp, 3.5; R2-3) the key slice read under the range's token
    icases Hlocked with ⟨%c, Hlocked, %Hc⟩
    ihave #Hcap' := Hcap $$ %c
    iunfold mvcc.rdCap at Hcap'
    icases Hcap' $$ %ksl %e.1 Hksl Hlocked with ⟨%dqk, Hkp, Hkback⟩
    wp_apply (h4 ksl r (if t then [W8 116] else []) dqk (by cases t <;> simp) Hr0 Hs0)
      $$ [Hkp] as Hkp
    · rw [← Hkb]; iexact Hkp
    ihave Hlocked := Hkback $$ [Hkp]
    · rw [Hkb]; iexact Hkp
    (try wp_auto)
    wp_apply (wp_map_lookup2 Revision.ty (go.GoType.StructType []) keep A (mvcc.revVal r) (DFrac.own 1))
      $$ [$Hkeep] as Hkeep
    (try wp_auto)
    obtain ⟨HnL, HeL⟩ := List.getElem?_eq_some_iff.1 He
    have Henotin : e.1 ∉ D := fun hm =>
      go.goStringLt_irrefl _ (by have := HD.2.2.2.1 e.1 hm (sint.nat n) HnL (Nat.le_refl _); rwa [HeL] at this)
    have Hesp : mvcc.sc_space log (sint.Z rev) e.1 :=
      mvcc.sc_mem log ilog rev Hrev.2 HilWf.2.1 Hpre Hsub (HLmem e (List.mem_of_getElem? He)).1 r t
        Hk Hrm
    wp_join iprop(∃ (kc' : w64) (D' : List GoString) (pn' : mvcc.Bucket) (Db' : List GoString),
        keyCompactions_ptr ↦ kc' ∗
        (∃ c' : Nat, U c' ∗ ⌜L.length + 1 ≤ c' + (sint.nat n + 1)⌝) ∗
        keys_ptr ↦ ks ∗ igo ↦ n ∗ tx_ptr ↦ GoInterface.ok bt ∗ mvcc.storePV γ pn' ∗
        ⌜(sint.Z kc' = D'.length ∧ D'.Nodup ∧ (∀ k ∈ D', mvcc.sc_space log (sint.Z rev) k) ∧
          ∀ k ∈ D', k = e.1 ∨ k ∈ D) ∧
          mvcc.sc_pnOk log (sint.Z rev) L (sint.nat n + 1) p0 pn' Db'⌝)
      with [keyCompactions Hlocked keys Higo tx HPV]
      as ⟨%kc', %D', %pn', %Db', keyCompactions, Hlocked, keys, Higo, tx, HPV, %HDP⟩
    · have hkp : (A !! mvcc.revVal r).isSome = true := by
        revert Hif; cases (A !! mvcc.revVal r).isSome <;> simp
      iexists kc, D, pn, Db
      ihave Hlocked : iprop(∃ cc : Nat, U cc ∗ ⌜L.length + 1 ≤ cc + (sint.nat n + 1)⌝) $$ [Hlocked]
      · iexists c; iframe Hlocked; ipureintro; omega
      iframe
      ipureintro
      exact ⟨⟨HD.1, HD.2.1, HD.2.2.1, fun k hk => Or.inr hk⟩,
        mvcc.sc_pnOk_keep He (mvcc.sc_kept log rev A HA r t e.1 Hk hkp) HPn.1⟩
    · (try wp_auto)
      simp only [Hbnd2, and_self, ↓reduceIte]
      wp_apply wp_load_slice_index ks (sint.Z n) kss DFrac.discard ksl Hn.1 $$ [$Hks] as -
      · ipureintro; exact Hkv.1
      have hkd : mvcc.KeyDel log (sint.Z rev) e.1 :=
        mvcc.sc_keyDel log rev A HA Hrev.2 r t e.1 Hk Hr0 Hrm
          (by revert Hif; cases (A !! mvcc.revVal r).isSome <;> simp)
      ihave #Hdk : mvcc.delKey γ e.1 $$ []
      · iunfold mvcc.delKey
        iexists (sint.Z rev), log
        iframe Hlb Hcert
        ipureintro
        exact ⟨by omega, hkd⟩
      (try wp_auto)
      wp_bind (App (App (Val #(methods bt.ty _ bt.v)) (Val #bK)) (Val #ksl))
      -- (Draft round 2) the key slice `keys[i]` passed lent, as the range returned it; (R2-3) one
      -- of the range's budget spent (`c ≥ 2`: a key left to read, and the `Meta` put's)
      obtain ⟨c'', rfl⟩ : ∃ c'', c = c'' + 1 := ⟨c - 1, by omega⟩
      iapply HDelC $$ %ksl %e.1 %c'' %pn [Hlocked HPV]
      · iframe Hlocked HPV; iframe #
      inext
      iintro ⟨Hlocked, HPV⟩
      (try wp_auto)
      wp_join_done
      -- the key deleted: one more in `D`, still fewer than the job's changes
      have Hnd' : (e.1 :: D).Nodup := List.nodup_cons.2 ⟨Henotin, HD.2.1⟩
      have Hsp' : ∀ k ∈ e.1 :: D, mvcc.sc_space log (sint.Z rev) k := by
        intro k hk
        rcases List.mem_cons.1 hk with rfl | hk
        · exact Hesp
        · exact HD.2.2.1 k hk
      have Hcnt := mvcc.sc_count log (sint.Z rev) _ Hnd' Hsp'
      have Hsm : ((log.take ((sint.Z rev).toNat + 1)).map List.length).sum < 2 ^ 62 := Hsmall
      rw [List.length_cons] at Hcnt
      have HDk := HD.1
      iexists kc + W64 1, e.1 :: D, GMap.delete e.1 pn, e.1 :: Db
      ihave Hlocked : iprop(∃ cc : Nat, U cc ∗ ⌜L.length + 1 ≤ cc + (sint.nat n + 1)⌝) $$ [Hlocked]
      · iexists c''; iframe Hlocked; ipureintro; omega
      iframe
      ipureintro
      refine ⟨⟨?_, Hnd', Hsp', fun k hk => ?_⟩, mvcc.sc_pnOk_del He hkd HPn.1⟩
      · rw [List.length_cons]; word
      · rcases List.mem_cons.1 hk with rfl | hk
        · exact Or.inl rfl
        · exact Or.inr hk
    (try wp_auto)
    simp only [Hbnd2, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index ks (sint.Z n) kss DFrac.discard ksl Hn.1 $$ [$Hks] as -
    · ipureintro; exact Hkv.1
    (try wp_auto)
    have Hbnd3 : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z vs.len := by
      refine ⟨Hn.1, ?_⟩; have := Hvl.1; rw [hlen2] at this; word
    simp only [Hbnd3, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index vs (sint.Z n) vss DFrac.discard vsl Hn.1 $$ [$Hvs] as -
    · ipureintro; exact Hkv.2
    (try wp_auto)
    icases h with ⟨h, %Hhv⟩
    -- (backend-cmp, 3.5; R2-3) the key and its value read together under the range's token
    icases Hlocked with ⟨%c', Hlocked, %Hc'⟩
    ihave #Hcap2' := Hcap2 $$ %c'
    iunfold mvcc.rdCap2 at Hcap2'
    icases Hcap2' $$ %ksl %vsl %e.1 %e.2 Hksl Hvsl Hlocked with ⟨%dqk, %dqv, Hkp, Hvp, Hkvback⟩
    wp_apply (h5 h_ptr hv keep (DFrac.own 1) A ksl vsl e.1 e.2 dqk dqv)
      $$ [$h $Hkeep $Hkp $Hvp] as ⟨⟨%hv2, h⟩, Hkeep, Hkp, Hvp⟩
    · iframe #
      ipureintro
      exact ⟨Hhv, r, _, Hkb, by cases t <;> simp, Hr0, Hs0⟩
    ihave Hlocked := Hkvback $$ Hkp Hvp
    (try wp_auto)
    wp_for_post
    iframe
    have Hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    ihave Hlocked : iprop(∃ cc : Nat, U cc ∗ ⌜L.length + 1 ≤ cc + sint.nat (n + W64 1)⌝) $$ [Hlocked]
    · iexists c'; iframe Hlocked; ipureintro; rw [Hn1]; exact Hc'
    obtain ⟨HD', HPn'⟩ := HDP
    iexists n + W64 1, n, kc', hv2, mvcc.revVal r, D', pn', Db'
    simp only [named]
    iframe
    ipureintro
    have Hsrt := List.pairwise_iff_getElem.1 HLsrt
    have Hnext : ∀ j (hj : j < L.length), sint.nat n < j → go.GoStringLt e.1 (L[j]).1 := by
      intro j hj hnj
      have := Hsrt (sint.nat n) j (by simpa using HnL) (by simpa using hj) hnj
      simpa [HeL] using this
    have Hsucc : go.GoStringLt e.1
        (mvcc.revBytes (mvcc.revOf ⟨(mvcc.revVal r).Main', (mvcc.revVal r).Sub' + W64 1⟩) false) := by
      rw [Hk]
      apply mvcc.RevOrder.revBytes_lt
      right
      simp only [mvcc.revOf, mvcc.revVal]
      refine ⟨?_, ?_⟩ <;> first | trivial | rfl | word
    refine ⟨⟨by word, by word⟩, ⟨HD'.1, HD'.2.1, HD'.2.2.1, ?_, Or.inr ?_⟩,
      by rw [Hn1]; exact HPn', Or.inr fun e' he' => ⟨r, t, ?_, rfl⟩⟩
    rotate_left 2
    · rw [Hn1, Nat.add_sub_cancel, He] at he'
      cases he'
      exact Hk
    · intro k hk j hj hnj
      rcases HD'.2.2.2 k hk with rfl | hk
      · exact Hnext j hj (by omega)
      · exact HD.2.2.2.1 k hk j hj (by omega)
    · intro k hk
      rcases HD'.2.2.2 k hk with rfl | hk
      · exact Hsucc
      · exact go.goStringLt_trans
          (by have := HD.2.2.2.1 k hk (sint.nat n) HnL (Nat.le_refl _); rwa [HeL] at this) Hsucc
  -- (R2-3) the range's token at the loop's end: one left at least, for the `Meta` put
  icases Hlocked with ⟨%c, HU, %Hc⟩
  have HnL' : sint.nat n ≤ L.length := Hn.2
  obtain ⟨c0, rfl⟩ : ∃ c0, c = c0 + 1 := ⟨c - 1, by omega⟩
  -- (F2, stage 2) the batch's deletes: compaction's among its keys, all of them (`batchOk`)
  have hlen1 : kss.length = L.length := by simpa using Hlens.1
  have HnE : sint.nat n = L.length := by
    have h1 := Hn.2
    rw [← hlen1, Hkl.1] at h1 ⊢
    word
  have HLt : L.take (sint.nat n) = L := List.take_of_length_le (by omega)
  have HPnL : mvcc.sc_pnOk log (sint.Z rev) L (sint.nat n) p0 pn Db := HPn.1
  unfold mvcc.sc_pnOk at HPnL
  rw [HLt] at HPnL
  have Hbok : ∀ cur' : mvcc.Rev,
      ((L.length < (sint.Z scfg.CompactionBatchLimit').toNat ∧ cur' = ⟨rev + W64 1, W64 0⟩) ∨
        (∃ (hne : L ≠ []) (r : mvcc.Rev) (t : Bool), (L.getLast hne).1 = mvcc.revBytes r t ∧
          cur' = ⟨r.main, r.sub + W64 1⟩)) →
      (∀ k x, p0.lookup k = some x → ∃ e ∈ mvcc.logEnts ilog 0 ilog.length, mvcc.entKey e = k) →
      mvcc.storePVx γ → sint.Z rev < ilog.length → mvcc.batchOk ilog (sint.Z rev) bs p0 pn cur' :=
    fun cur' hcase hkeys hx hil => mvcc.sc_batchOk log ilog rev A HA ⟨Hlwf.2.1, Hlwf.2.2⟩
      ⟨HilWf.2.1, HilWf.2.2⟩ Hpre Hrev.1 Hrz Hrev.2 hil bs m' p0 pn (Hpvx hx) _ L hL HLent' Db
      HPnL.2.1 HPnL.2.2 HPnL.1 hkeys cur' hcase
  -- the batch read: short (the last), or full
  wp_if_destruct
  · -- the last batch: `finishedCompactRev = rev`, the compaction finished
    (try wp_auto)
    have HshortL : L.length < (sint.Z scfg.CompactionBatchLimit').toNat := by
      rw [← hlen1, Hkl.1]; word
    -- (F2, stage 2) the session closed with the finished record's put
    ihave Hfc := mvcc.jobSess_fin γ ilog rev bs p0 pn ⟨rev + W64 1, W64 0⟩ hcmpM
      (fun hk hx hil => Hbok _ (Or.inl ⟨HshortL, rfl⟩) hk hx hil) $$ [Hsess HPV]
    · iframe Hsess HPV
    icases Hfc with ⟨%cv, Hck, Hfcl⟩
    -- (question 5's core stage, part (1)) the key in the batch lock's resource, swapped for the
    -- compaction keys' write right for the `Meta` put, and back
    iunfold mvcc.compactRes at HcresW
    icases HcresW with ⟨%sched, %fin, %nf, Hmeta, Hfin, %Hnf, Hmk⟩
    ihave Hmk := (mvcc.mwSlot_on γ hcmpM).1 $$ Hmk
    iunfold mvcc.mwSwap at Hswk
    imod Hswk $$ [Hmk Hlc1] with ⟨HMW, Hback⟩
    · iframe Hmk Hlc1
    wp_bind (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.UnsafeSetFinishedCompact))
      (Val #(GoInterface.ok bt))) (Val #rev))
    iapply (h6 bt iprop(U (c0 + 1) ∗ mvcc.kbMW γ.kb γ.bucket) iprop(U c0 ∗ mvcc.kbMW γ.kb γ.bucket)
      (mvcc.storeCK γ) cv rev Hrev.1) $$ [HU HMW Hck]
    · iframe HU HMW Hck; iframe #
      iapply HMetaC
    inext
    iintro ⟨⟨HU, HMW⟩, Hck⟩
    imod Hfcl $$ Hck with ⟨HtrkW, Hjob⟩
    imod Hback $$ HMW with ⟨Hmk, -⟩
    ihave Hmk := (mvcc.mwSlot_on γ hcmpM).2 $$ Hmk
    (try wp_auto)
    iunfold mvcc.metaCompact at Hmeta
    imod ghostVar_update (sched, some rev) γ.cmeta _ $$ Hmeta with Hmeta
    imod mono_nat_own_update (max nf (mvcc.crevN (sint.Z rev))) (Nat.le_max_left _ _) $$ Hfin
      with ⟨Hfin, #Hflb⟩
    ihave #Hdone : mvcc.compactedAt γ (sint.Z rev) $$ []
    · iunfold mvcc.compactedAt
      iapply monoNatLbOwn_le _ (Nat.le_max_right _ _) $$ Hflb
    wp_bind (App (Val #(methods bt.ty _ bt.v)) (Val #()))
    iapply HUnlU $$ %c0 [HU HwkW HwvW HbvW Hmeta Hfin Hmk HlgW HtrkW HP]
    · iframe HU HP
      iapply mvcc.storeW_put s γ
      iframe Hreg
      iunfold mvcc.writerRes
      iexists ilog
      simp only [named]
      iframe
      iframe #
      isplitr
      · ipureintro; exact HneW
      iunfold mvcc.compactRes
      iexists sched, some rev, _
      iunfold mvcc.metaCompact
      iframe
      ipureintro
      exact Nat.le_max_right _ _
    inext
    iintro -
    (try wp_auto)
    wp_apply time.wp_Since as %d2 -
    (try wp_auto)
    wp_apply HPause
    (try wp_auto)
    icases h with ⟨h, %Hhv⟩
    wp_apply h7 h_ptr hv $$ [$h] as %hash h
    · ipureintro; exact Hhv
    (try wp_auto)
    wp_apply HSize as %sz -
    wp_apply HSizeU as %szu -
    (try wp_auto)
    wp_apply h8 as %f0 -
    (try wp_auto)
    wp_apply time.wp_Since as %d3 -
    (try wp_auto)
    wp_apply h9 as %f1 -
    (try wp_auto)
    wp_apply h10 as %f2 -
    (try wp_auto)
    wp_apply h11 as %f3 -
    (try wp_auto)
    wp_apply h8 as %f4 -
    (try wp_auto)
    wp_apply h13 as %str5 -
    (try wp_auto)
    wp_apply h12 as %f5 -
    (try wp_auto)
    wp_apply h8 as %f6 -
    (try wp_auto)
    wp_apply h13 as %str7 -
    (try wp_auto)
    wp_apply h12 as %f7 -
    (try wp_auto)
    wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f0, f1, f2, f3, f4, f5, f6, f7]
    isplitr
    · ipureintro; rfl
    iintro %fsl ⟨-, -⟩
    (try wp_auto)
    wp_apply h14 lg _ _ $$ []
    · ipureintro; exact Hlgnn
    (try wp_auto)
    wp_for_post
    wp_apply time.wp_Now as %tn -
    (try wp_auto)
    wp_apply h16 as %un -
    (try wp_auto)
    wp_apply HLast
    (try wp_auto)
    have hkc0 : 0 ≤ sint.Z kc := by have := HD.1; omega
    ihave #HKA := HKeysAdd $$ %kc %hkc0
    wp_apply HKA
    (try wp_auto)
    wp_apply time.wp_Since as %d4 -
    (try wp_auto)
    wp_apply HTot
    (try wp_auto)
    wp_apply HUSR $$ [$HSRh] as HSR
    (try wp_auto)
    iapply HΦ
    iframe Htok
    isplitl [Hfclose Hfb Hfidx Hfsch Hfstop]
    · iapply Hfclose; iunfold mvcc.storeFields; simp only [named]; iframe
    isplitl [HRT HSR Hjob]
    · iapply (mvcc.compactJobResM_on γ.kb hcmpM).2; iframe HRT HSR Hjob
    ileft
    iframe Hdone
    ipureintro; rfl
  -- a full batch: committed, then the next one after the sleep, unless the store stops
  have HfullL : (sint.Z scfg.CompactionBatchLimit').toNat ≤ L.length := by
    rw [← hlen1, Hkl.1]; word
  have hne : L ≠ [] := by
    intro h; rw [h, List.length_nil] at HfullL; have := Hcfgl.1; omega
  have hgl : L[sint.nat n - 1]? = some (L.getLast hne) := by
    rw [HnE, ← List.getLast?_eq_getElem?, List.getLast?_eq_some_getLast hne]
  obtain ⟨rl, tl, Hkl', Hrv⟩ : ∃ (r : mvcc.Rev) (t : Bool),
      (L.getLast hne).1 = mvcc.revBytes r t ∧ rv = mvcc.revVal r := by
    rcases HPn.2 with h0 | h
    · exfalso; rw [HnE] at h0; exact hne (List.length_eq_zero_iff.1 h0)
    · exact h _ hgl
  subst Hrv
  obtain ⟨rl', tl', Hk', Hl0, Hl1, -, Hl3⟩ := HLent' _ (List.getLast_mem hne)
  obtain ⟨-, Hrl⟩ := mvcc.revBytes_inj _ _ _ _ (Hkl'.symm.trans Hk')
  subst rl'
  -- (F2, stage 2) the session closed at the next batch's cursor
  imod mvcc.jobSess_close γ ilog (sint.Z rev) bs p0 pn
    (mvcc.revOf { Main' := rl.main, Sub' := rl.sub + W64 1 }) hcmpM
    (fun hk hx hil => Hbok _ (Or.inr ⟨hne, rl, tl, Hkl', rfl⟩) hk hx hil)
    ⟨Hl0, by show 0 ≤ sint.Z (rl.sub + W64 1); word⟩ $$ [Hsess HPV] with ⟨HtrkW, Hjc⟩
  · iframe Hsess HPV
  wp_bind (App (Val #(methods bt.ty _ bt.v)) (Val #()))
  iapply HUnlU $$ %(c0 + 1) [HU HwkW HwvW HbvW HcresW HlgW HtrkW HP]
  · iframe HU HP
    iapply mvcc.storeW_put s γ
    iframe Hreg
    iunfold mvcc.writerRes
    iexists ilog
    simp only [named]
    iframe
    iframe #
    ipureintro; exact HneW
  inext
  iintro -
  -- (question 5's core stage) a receipt for `ForceCommit`'s write-back token
  wp_take_receipt as Hr2
  imod mvcc.kbWTSupply_take γ.kb $$ [$Hsup $Hr2] with Hwt2
  wp_apply (h15 _ lst bs (Or.inl Hbs)) $$ [$HlastS $HlastC] as %lst2 ⟨HlastS, HlastC⟩
  rw [List.drop_eq_nil_of_le (by omega : bs.length ≤ 17), List.append_nil]
  (try wp_auto)
  wp_apply HForce $$ %iprop(True) %iprop(True) [HRT Hwt2] as ⟨HRT, -⟩
  · iframe HRT Hwt2
    isplitr; · itrivial
    iapply mvcc.storeReq_true
  (try wp_auto)
  wp_apply time.wp_Since as %d5 -
  (try wp_auto)
  wp_apply HPause
  (try wp_auto)
  wp_apply +noauto time.wp_After as %tch %γt #Hbag
  wp_auto_lc 2
  ihave #Hstcc := Hstopch
  iunfold mvcc.isStopChan at Hstcc
  icases Hstcc with ⟨%γs, #Hstcc⟩
  ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, tch, γt
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hbag
    iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hbag
    inext
    iintro %tm' -
    wp_auto
    wp_for_post
    iframe
    have HDk := HD
    iexists lst2, _, kc, hv, D
    simp only [named]
    iframe
    ipureintro
    refine ⟨by rw [mvcc.revBytes_length]; rfl, HD.1, HD.2.1,
      fun k hk => ⟨HD.2.2.1 k hk, ?_⟩⟩
    rcases HD.2.2.2.2 with h0 | hlt
    · exfalso
      clear HDk
      exact absurd h0 (by omega)
    · exact hlt k hk
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, sstop, γs
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply ownBroadcastChan_is_chan $$ Hstcc
    iapply broadcast_chan_receive _ _ _ _ _ $$ Hstcc
    iintro ⟨-, #Hdone⟩
    wp_auto
    wp_apply (mvcc.wp_Errorf_errorfIs go!"interrupted due to stop signal" _ (by decide)) $$ []
      as %err #Herr
    · iframe #; iapply ownSlice_nil
    (try wp_auto)
    wp_for_post
    wp_apply time.wp_Now as %tn -
    (try wp_auto)
    wp_apply h16 as %un -
    (try wp_auto)
    wp_apply HLast
    (try wp_auto)
    have hkc0 : 0 ≤ sint.Z kc := by have := HD.1; omega
    ihave #HKA := HKeysAdd $$ %kc %hkc0
    wp_apply HKA
    (try wp_auto)
    wp_apply time.wp_Since as %d4 -
    (try wp_auto)
    wp_apply HTot
    (try wp_auto)
    wp_apply HUSR $$ [$HSRh] as HSR
    (try wp_auto)
    iapply HΦ
    iframe Htok
    isplitl [Hfclose Hfb Hfidx Hfsch Hfstop]
    · iapply Hfclose; iunfold mvcc.storeFields; simp only [named]; iframe
    ihave Hjob := mvcc.jobCurAt_kbJob γ.kb _ _ $$ Hjc
    isplitl [HRT HSR Hjob]
    · iapply (mvcc.compactJobResM_on γ.kb hcmpM).2; iframe HRT HSR Hjob
    iright
    iframe Herr
    iunfold mvcc.storeStopped
    iexists sstop, γs
    iframe Hdone
    iunfold mvcc.stopPayAt at Hpay
    icases Hpay with ⟨#Hx, -⟩
    iexact Hx
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end EtcdGrove
end Perennial

