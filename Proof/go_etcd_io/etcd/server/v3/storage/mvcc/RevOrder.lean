/-
The order of the bucket's keys (unit 5): the big-endian encoding is monotone, `revBytes` is
ordered by (main, sub), and a write transaction's next revision key is above every key of the
committed bucket and of its own pending puts (what the backend's safe-range discipline asks of
`UnsafeSeqPut`). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BucketLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc
namespace RevOrder

/-! ## The byte order -/

/-- The big-endian value of a byte list. -/
def beVal (l : List w8) : Nat := LittleEndian.combine l.reverse

theorem combine_append_single (l : List w8) (x : w8) :
    LittleEndian.combine (l ++ [x]) = LittleEndian.combine l + 256 ^ l.length * x.toNat := by
  induction l with
  | nil => simp [LittleEndian.combine]
  | cons b l ih =>
    simp only [List.cons_append, LittleEndian.combine, ih, List.length_cons, Nat.pow_succ]
    rw [Nat.mul_add]
    rw [show 256 * (256 ^ l.length * x.toNat) = 256 ^ l.length * 256 * x.toNat by
      rw [Nat.mul_comm 256 (256 ^ l.length * x.toNat), Nat.mul_assoc, Nat.mul_comm x.toNat 256,
        ← Nat.mul_assoc]]
    omega

theorem beVal_cons (x : w8) (l : List w8) :
    beVal (x :: l) = beVal l + 256 ^ l.length * x.toNat := by
  unfold beVal
  rw [List.reverse_cons, combine_append_single, List.length_reverse]

theorem beVal_lt (l : List w8) : beVal l < 256 ^ l.length := by
  have := LittleEndian.combine_bound l.reverse
  unfold beVal
  rw [List.length_reverse, Nat.pow_mul] at this
  simpa using this

/-- Same-length byte lists compare as their big-endian values. -/
theorem lex_of_beVal_lt : ∀ (a b : List w8), a.length = b.length → beVal a < beVal b →
    go.GoStringLt a b
  | [], [], _, h => by simp [beVal, LittleEndian.combine] at h
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl
  | x :: xs, y :: ys, hl, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    rw [beVal_cons, beVal_cons, ← hl] at h
    unfold go.GoStringLt
    have hxs := beVal_lt xs
    have hys := beVal_lt ys
    rw [← hl] at hys
    have hpos : 0 < 256 ^ xs.length := Nat.pow_pos (by decide)
    rcases Nat.lt_trichotomy x.toNat y.toNat with hlt | heq | hgt
    · exact List.Lex.rel (by simpa [uint.Z] using hlt)
    · have hxy : x = y := BitVec.eq_of_toNat_eq heq
      subst hxy
      exact List.Lex.cons (lex_of_beVal_lt xs ys hl (by omega))
    · exfalso
      have : 256 ^ xs.length * (y.toNat + 1) ≤ 256 ^ xs.length * x.toNat :=
        Nat.mul_le_mul_left _ hgt
      rw [Nat.mul_add, Nat.mul_one] at this
      omega

/-- A smaller prefix of the same length decides the order. -/
theorem lex_append_of_lex {p q : List w8} (h : go.GoStringLt p q) (hl : p.length = q.length)
    (x y : List w8) : go.GoStringLt (p ++ x) (q ++ y) := by
  unfold go.GoStringLt at *
  induction h with
  | nil => simp at hl
  | cons _ ih =>
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    exact List.Lex.cons (ih hl)
  | rel hr => exact List.Lex.rel hr

/-- An equal prefix: the rest decides the order. -/
theorem lex_prefix (p : List w8) {x y : List w8} (h : go.GoStringLt x y) :
    go.GoStringLt (p ++ x) (p ++ y) := by
  unfold go.GoStringLt at *
  induction p with
  | nil => exact h
  | cons a p ih => exact List.Lex.cons ih

theorem beVal_u64Be (a : w64) : beVal (u64Be a) = a.toNat := by
  unfold beVal u64Be
  rw [List.reverse_reverse, u64Le, u64LeDef, LittleEndian.combine_split]
  have := a.isLt
  omega

/-- **The big-endian encoding is monotone.** -/
theorem u64Be_lt (a b : w64) (h : uint.Z a < uint.Z b) (x y : List w8) :
    go.GoStringLt (u64Be a ++ x) (u64Be b ++ y) := by
  apply lex_append_of_lex _ (by simp [u64Be_length])
  apply lex_of_beVal_lt _ _ (by simp [u64Be_length])
  rw [beVal_u64Be, beVal_u64Be]
  have : (a.toNat : Int) < b.toNat := by simpa [uint.Z] using h
  omega

/-- An equal encoded prefix: the rest decides the order. -/
theorem u64Be_eq_lt (a : w64) {x y : List w8} (h : go.GoStringLt x y) :
    go.GoStringLt (u64Be a ++ x) (u64Be a ++ y) := lex_prefix _ h

/-- **`revBytes` is ordered by (main, sub)**, whatever the tombstone marks. -/
theorem revBytes_lt (r r' : Rev) (t t' : Bool)
    (h : uint.Z r.main < uint.Z r'.main ∨ (r.main = r'.main ∧ uint.Z r.sub < uint.Z r'.sub)) :
    go.GoStringLt (revBytes r t) (revBytes r' t') := by
  unfold revBytes
  simp only [List.append_assoc]
  rcases h with h | ⟨hm, hs⟩
  · exact u64Be_lt _ _ h _ _
  · rw [hm]
    apply u64Be_eq_lt
    apply lex_prefix [W8 95]
    exact u64Be_lt _ _ hs _ _

/-- A revision key has 17 or 18 bytes: a valid bbolt key. -/
theorem revBytes_keyOk (r : Rev) (t : Bool) :
    0 < (revBytes r t).length ∧ (revBytes r t).length ≤ 32768 := by
  rw [revBytes_length]; cases t <;> simp

/-! ## The bucket's keys -/

/-- A key of `bucketOfRev r before cs` is a revision key of `r` at a position of `cs`. -/
theorem mem_bucketOfRev {r : Nat} {before : List EtcdKv} {cs : List Change}
    {p : GoString × GoString} (h : p ∈ bucketOfRev r before cs) :
    ∃ (i : Nat) (t : Bool), i < cs.length ∧ p.1 = revBytes ⟨W64 r, W64 i⟩ t := by
  unfold bucketOfRev at h
  rw [List.mem_filterMap] at h
  obtain ⟨⟨c, i⟩, hi, hp⟩ := h
  rw [List.mem_zipIdx_iff_getElem?] at hi
  have hlt : i < cs.length := (List.getElem?_eq_some_iff.1 hi).1
  cases hk : changeKv (W64 r) before cs i with
  | none => rw [hk] at hp; simp at hp
  | some kv =>
    rw [hk] at hp
    simp only [Option.map_some, Option.some.injEq] at hp
    exact ⟨i, c.isDel, hlt, by rw [← hp]⟩

/-- **Every key of the bucket of `log`** is a revision key of an earlier revision. -/
theorem bucketMap_key (log : Log) (hcs : ∀ cs ∈ log, cs.length < 2 ^ 63) {k v : GoString}
    (h : (bucketMap log).lookup k = some v) :
    ∃ (r i : Nat) (t : Bool), r < log.length ∧ i < 2 ^ 63 ∧ k = revBytes ⟨W64 r, W64 i⟩ t := by
  unfold bucketMap at h
  rw [lookup_foldl_insert] at h
  cases hf : (bucketOf log).reverse.find? (fun p => decide (p.1 = k)) with
  | none =>
    rw [hf] at h
    have h0 : (GMap.empty : GMap GoString GoString) !! k = none := rfl
    rw [h0] at h; cases h
  | some p =>
    have hp := List.mem_reverse.1 (List.mem_of_find?_eq_some hf)
    have hk : p.1 = k := by simpa using List.find?_some hf
    unfold bucketOf at hp
    rw [List.mem_flatten] at hp
    obtain ⟨l, hl, hp⟩ := hp
    rw [List.mem_map] at hl
    obtain ⟨⟨cs, r⟩, hz, rfl⟩ := hl
    rw [List.mem_zipIdx_iff_getElem?] at hz
    simp only at hz
    have hr : r < log.length := (List.getElem?_eq_some_iff.1 hz).1
    have hcl := hcs cs (List.mem_of_getElem? hz)
    obtain ⟨i, t, hi, hpi⟩ := mem_bucketOfRev hp
    have hi' : i < cs.length := hi
    exact ⟨r, i, t, hr, by omega, by rw [← hk, hpi]⟩

/-- **Every pending put's key** is of the pending revision, at an earlier position. -/
theorem pendPuts_key (ilog : Log) (pend : List Change) {p : GoString × GoString}
    (h : p ∈ pendPuts ilog pend) :
    ∃ (i : Nat) (t : Bool), i < pend.length ∧ p.1 = revBytes ⟨W64 ilog.length, W64 i⟩ t :=
  mem_bucketOfRev h

theorem uint_Z_W64_of_lt {n : Nat} (h : n < 2 ^ 64) : uint.Z (W64 (n : Int)) = n := by
  unfold W64; simp [uint.Z]; omega

/-- **The next revision key is above the committed bucket's keys.** -/
theorem bucketMap_lt_next (ilog : Log) (pend : List Change) (t : Bool)
    (hlen : ilog.length < 2 ^ 63) (hcs : ∀ cs ∈ ilog, cs.length < 2 ^ 63)
    {k v : GoString} (h : (bucketMap ilog).lookup k = some v) :
    go.GoStringLt k (revBytes ⟨W64 ilog.length, W64 pend.length⟩ t) := by
  obtain ⟨r, i, t', hr, -, rfl⟩ := bucketMap_key ilog hcs h
  apply revBytes_lt
  left
  simp only
  rw [uint_Z_W64_of_lt (by omega), uint_Z_W64_of_lt (by omega)]
  omega

/-- **The next revision key is above the pending puts' keys.** -/
theorem pendPuts_lt_next (ilog : Log) (pend : List Change) (t : Bool)
    (hplen : pend.length < 2 ^ 63) {p : GoString × GoString} (h : p ∈ pendPuts ilog pend) :
    go.GoStringLt p.1 (revBytes ⟨W64 ilog.length, W64 pend.length⟩ t) := by
  obtain ⟨i, t', hi, hp⟩ := pendPuts_key ilog pend h
  rw [hp]
  apply revBytes_lt
  right
  refine ⟨rfl, ?_⟩
  simp only
  rw [uint_Z_W64_of_lt (by omega), uint_Z_W64_of_lt (by omega)]
  omega

end RevOrder
end mvcc
end EtcdGrove
end Perennial
