/- Lean-first (no Rocq counterpart).

# `etcd/dist`: a valid net address makes a plain peer URL

A deployment's addresses are the net extension's valid ones (`Net.addrOk`: the canonical `a.b.c.d:p`);
etcd's peer URLs are `http://` and the address, and rafthttp's specs take them plain
(`types.plainPeerURL`: `http://host:port`, host bytes then one `:` then digits). Pure: the address's
parse (`Net.parseAddr`, through `Net.splitBy` and `Net.decNat`) gives exactly that shape. Used by
`putget_safe`'s member boot (`etcd_putget_dist.member_boot`) and, for every member, by `etcd_safe`.
A valid address is also a plain endpoint of `clientv3.New` (`plainEndpoint`: no `://`, no `unix:`
prefix; `addrOk_plainEndpoint`, for `putget_safe`'s client boot): its bytes are digits, `.` and `:`.
-/
module

public import GooseLang.Ext.Net.Impl
public import Proof.go_etcd_io.etcd.client.pkg.v3.types.URLs
public import Proof.go_etcd_io.etcd.client.v3.InvClientNew

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

/-- `splitBy` returns at least one piece. -/
theorem splitBy_ne_nil (sep : w8) : ∀ (s cur : GoString), Net.splitBy sep s cur ≠ []
  | [], cur => by simp [Net.splitBy]
  | d :: s, cur => by
    simp only [Net.splitBy]
    by_cases hd : d.toNat = sep.toNat
    · rw [if_pos hd]; simp
    · rw [if_neg hd]; exact splitBy_ne_nil sep s (d :: cur)

/-- Every byte of the current piece and of the rest is a separator or in a piece. -/
theorem splitBy_cover (sep : w8) : ∀ (s cur : GoString) (c : w8), (c ∈ cur ∨ c ∈ s) →
    c.toNat = sep.toNat ∨ ∃ p ∈ Net.splitBy sep s cur, c ∈ p
  | [], cur, c, h => by
    right
    refine ⟨cur.reverse, by simp [Net.splitBy], ?_⟩
    rcases h with h | h
    · exact List.mem_reverse.2 h
    · simp at h
  | d :: s, cur, c, h => by
    simp only [Net.splitBy]
    by_cases hd : d.toNat = sep.toNat
    · rw [if_pos hd]
      rcases h with h | h
      · exact Or.inr ⟨cur.reverse, by simp, List.mem_reverse.2 h⟩
      · rcases List.mem_cons.1 h with rfl | h
        · exact Or.inl hd
        · rcases splitBy_cover sep s [] c (Or.inr h) with h' | ⟨p, hp, hc⟩
          · exact Or.inl h'
          · exact Or.inr ⟨p, List.mem_cons_of_mem _ hp, hc⟩
    · rw [if_neg hd]
      apply splitBy_cover sep s (d :: cur) c
      rcases h with h | h
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · rcases List.mem_cons.1 h with rfl | h
        · exact Or.inl (by simp)
        · exact Or.inr h

/-- One piece: no separator in the rest. -/
theorem splitBy_one (sep : w8) : ∀ (s cur y : GoString), Net.splitBy sep s cur = [y] →
    y = cur.reverse ++ s ∧ ∀ c ∈ s, c.toNat ≠ sep.toNat
  | [], cur, y, h => by
    simp only [Net.splitBy, List.cons.injEq, and_true] at h
    subst h; simp
  | d :: s, cur, y, h => by
    simp only [Net.splitBy] at h
    by_cases hd : d.toNat = sep.toNat
    · rw [if_pos hd] at h
      simp only [List.cons.injEq] at h
      exact absurd h.2 (splitBy_ne_nil sep s [])
    · rw [if_neg hd] at h
      obtain ⟨h1, h2⟩ := splitBy_one sep s (d :: cur) y h
      refine ⟨by simp [h1], ?_⟩
      intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact hd
      · exact h2 c hc

/-- Two pieces: the rest is the first piece's remainder, one separator, then the second piece. -/
theorem splitBy_two (sep : w8) : ∀ (s cur x y : GoString), Net.splitBy sep s cur = [x, y] →
    ∃ u d, s = u ++ d :: y ∧ d.toNat = sep.toNat ∧ x = cur.reverse ++ u ∧
      ∀ c ∈ u, c.toNat ≠ sep.toNat
  | [], cur, x, y, h => by simp [Net.splitBy] at h
  | d :: s, cur, x, y, h => by
    simp only [Net.splitBy] at h
    by_cases hd : d.toNat = sep.toNat
    · rw [if_pos hd] at h
      simp only [List.cons.injEq] at h
      obtain ⟨hx, hy⟩ := h
      obtain ⟨hy1, -⟩ := splitBy_one sep s [] y hy
      simp only [List.reverse_nil, List.nil_append] at hy1
      exact ⟨[], d, by simp [hy1], hd, by simp [hx], by simp⟩
    · rw [if_neg hd] at h
      obtain ⟨u, e, hs, he, hx, hu⟩ := splitBy_two sep s (d :: cur) x y h
      refine ⟨d :: u, e, by simp [hs], he, by simp [hx], ?_⟩
      intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact hd
      · exact hu c hc

/-- A value of digits has only digits. -/
theorem digitsVal_digits : ∀ (s : GoString) (acc n : Nat), Net.digitsVal s acc = some n →
    ∀ c ∈ s, Net.isDigit c = true
  | [], _, _, _ => by simp
  | c :: s, acc, n, h => by
    simp only [Net.digitsVal] at h
    by_cases hc : Net.isDigit c = true
    · rw [if_pos hc] at h
      intro c' hc'
      rcases List.mem_cons.1 hc' with rfl | hc'
      · exact hc
      · exact digitsVal_digits s _ n h c' hc'
    · rw [if_neg hc] at h; simp at h

/-- A canonical numeral is non-empty and all digits. -/
theorem decNat_digits : ∀ (s : GoString) (n : Nat), Net.decNat s = some n →
    s ≠ [] ∧ ∀ c ∈ s, Net.isDigit c = true
  | [], n, h => by simp [Net.decNat] at h
  | [c], n, h => ⟨by simp, digitsVal_digits [c] 0 n (by simpa only [Net.decNat] using h)⟩
  | c :: d :: s, n, h => by
    refine ⟨by simp, ?_⟩
    simp only [Net.decNat] at h
    by_cases h0 : c.toNat = 48
    · rw [if_pos h0] at h; simp at h
    · rw [if_neg h0] at h; exact digitsVal_digits _ 0 n h

/-- The shape of a parsed address: `ip:p`, the IP four numerals between dots, the port a numeral. -/
theorem parseAddr_some {a : GoString} {r : Nat × Nat × Nat × Nat × Nat} (h : Net.parseAddr a = some r) :
    ∃ ip p, Net.splitBy 58 a [] = [ip, p] ∧
      (∃ x1 x2 x3 x4, Net.splitBy 46 ip [] = [x1, x2, x3, x4] ∧
        (∃ n, Net.decNat x1 = some n) ∧ (∃ n, Net.decNat x2 = some n) ∧
        (∃ n, Net.decNat x3 = some n) ∧ (∃ n, Net.decNat x4 = some n)) ∧
      ∃ n, Net.decNat p = some n := by
  unfold Net.parseAddr at h
  split at h
  · rename_i ip p hsp
    split at h
    · rename_i x1 x2 x3 x4 hsp2
      split at h
      · rename_i n1 n2 n3 n4 np h1 h2 h3 h4 h5
        exact ⟨ip, p, hsp, ⟨x1, x2, x3, x4, hsp2, ⟨n1, h1⟩, ⟨n2, h2⟩, ⟨n3, h3⟩, ⟨n4, h4⟩⟩, ⟨np, h5⟩⟩
      · simp at h
    · simp at h
  · simp at h

/-- The index of the first separator is the length of a separator-free prefix. -/
theorem idxOf_sep (u p : GoString) (x : w8) (h : ∀ c ∈ u, c ≠ x) : (u ++ x :: p).idxOf x = u.length := by
  induction u with
  | nil => simp
  | cons c u ih =>
    have hc : c ≠ x := h c (by simp)
    have := ih (fun c' hc' => h c' (by simp [hc']))
    simp [List.idxOf_cons, hc, this]

/-- **A valid address is `host:port`** (`types.plainHostPort`). -/
theorem addrOk_plainHostPort {a : GoString} (h : Net.addrOk a = true) : types.plainHostPort a := by
  have hp : ∃ r, Net.parseAddr a = some r := by
    unfold Net.addrOk at h
    split at h
    · exact ⟨_, by assumption⟩
    · simp at h
  obtain ⟨r, hr⟩ := hp
  obtain ⟨ip, p, hsp, ⟨x1, x2, x3, x4, hsp2, ⟨n1, h1⟩, ⟨n2, h2⟩, ⟨n3, h3⟩, ⟨n4, h4⟩⟩, ⟨np, hpn⟩⟩ :=
    parseAddr_some hr
  obtain ⟨u, d, ha, hd, hu, hnc⟩ := splitBy_two 58 a [] ip p hsp
  simp only [List.reverse_nil, List.nil_append] at hu
  subst hu
  have hd' : d = (58 : w8) := BitVec.eq_of_toNat_eq hd
  subst hd'
  have hip : ∀ c ∈ ip, types.hostByte c := by
    intro c hc
    rcases splitBy_cover 46 ip [] c (Or.inr hc) with h46 | ⟨q, hq, hcq⟩
    · unfold types.hostByte
      exact Or.inr (Or.inr (Or.inr (Or.inl (by simpa using h46))))
    · rw [hsp2] at hq
      have hdig : Net.isDigit c = true := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl
        · exact (decNat_digits _ _ h1).2 c hcq
        · exact (decNat_digits _ _ h2).2 c hcq
        · exact (decNat_digits _ _ h3).2 c hcq
        · exact (decNat_digits _ _ h4).2 c hcq
      unfold Net.isDigit at hdig
      unfold types.hostByte
      exact Or.inl (by simpa using hdig)
  have hipne : ip ≠ [] := by
    rintro rfl
    simp [Net.splitBy] at hsp2
  obtain ⟨hpne, hpd⟩ := decNat_digits p np hpn
  subst ha
  have hidx : (ip ++ (58 : w8) :: p).idxOf (58 : w8) = ip.length :=
    idxOf_sep ip p 58 (fun c hc hc58 => hnc c hc (by rw [hc58]))
  unfold types.plainHostPort
  simp only [hidx]
  refine ⟨List.length_pos_iff.2 hipne, ?_, ?_, ?_⟩
  · simp only [List.length_append, List.length_cons]
    have := List.length_pos_iff.2 hpne
    omega
  · rw [List.take_left' rfl]
    exact hip
  · have hdrop : (ip ++ (58 : w8) :: p).drop (ip.length + 1) = p := by simp
    rw [hdrop]
    intro c hc
    have := hpd c hc
    unfold Net.isDigit at this
    unfold types.digitByte
    simpa using this

/-- **A valid address's peer URL is plain**: `http://a` for `Net.addrOk a` (`types.plainPeerURL`). -/
theorem addrOk_plainPeerURL {a : GoString} (h : Net.addrOk a = true) :
    types.plainPeerURL (go!"http://" ++ a) := by
  refine ⟨List.isPrefixOf_iff_prefix.2 (List.prefix_append _ _), ?_⟩
  have hdrop : (go!"http://" ++ a : List w8).drop 7 = a := by simp
  rw [hdrop]
  exact addrOk_plainHostPort h

/-- **Every byte of a valid address is a digit, `.` or `:`.** -/
theorem addrOk_bytes {a : GoString} (h : Net.addrOk a = true) :
    ∀ c ∈ a, c.toNat = 58 ∨ c.toNat = 46 ∨ Net.isDigit c = true := by
  have hp : ∃ r, Net.parseAddr a = some r := by
    unfold Net.addrOk at h
    split at h
    · exact ⟨_, by assumption⟩
    · simp at h
  obtain ⟨r, hr⟩ := hp
  obtain ⟨ip, p, hsp, ⟨x1, x2, x3, x4, hsp2, ⟨n1, h1⟩, ⟨n2, h2⟩, ⟨n3, h3⟩, ⟨n4, h4⟩⟩, ⟨np, hpn⟩⟩ :=
    parseAddr_some hr
  intro c hc
  rcases splitBy_cover 58 a [] c (Or.inr hc) with h58 | ⟨q, hq, hcq⟩
  · exact Or.inl (by simpa using h58)
  rw [hsp] at hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with hq | hq
  · subst hq
    rcases splitBy_cover 46 _ [] c (Or.inr hcq) with h46 | ⟨q', hq', hcq'⟩
    · exact Or.inr (Or.inl (by simpa using h46))
    · rw [hsp2] at hq'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
      right; right
      rcases hq' with rfl | rfl | rfl | rfl
      · exact (decNat_digits _ _ h1).2 c hcq'
      · exact (decNat_digits _ _ h2).2 c hcq'
      · exact (decNat_digits _ _ h3).2 c hcq'
      · exact (decNat_digits _ _ h4).2 c hcq'
  · subst hq
    exact Or.inr (Or.inr ((decNat_digits _ _ hpn).2 c hcq))

/-- **A valid address is a plain endpoint** (`clientv3.New`'s premise `plainEndpoint`): it has no
`/` (so no `://`) and no `u` (so no `unix:`/`unixs:` prefix). -/
theorem addrOk_plainEndpoint {a : GoString} (h : Net.addrOk a = true) : plainEndpoint a := by
  have hb := addrOk_bytes h
  refine ⟨fun hi => ?_, fun hi => ?_, fun hi => ?_⟩
  · have hm : (47 : w8) ∈ a := hi.subset (by decide)
    rcases hb _ hm with h1 | h1 | h1 <;> revert h1 <;> decide
  · have hm : (117 : w8) ∈ a := hi.subset (by decide)
    rcases hb _ hm with h1 | h1 | h1 <;> revert h1 <;> decide
  · have hm : (117 : w8) ∈ a := hi.subset (by decide)
    rcases hb _ hm with h1 | h1 | h1 <;> revert h1 <;> decide

/-! ## A valid address is short (fmt stage 1, 2026-11-24)

Its octets are at most `255` and its port at most `65535`, each a canonical numeral (no leading
zero), so the address has at most `3 * 4 + 3 + 1 + 5 = 21` bytes; `etcdstart.addrFits` (etcd's URL
length bound, `NewServer`'s `etcdURLsFit`) follows. -/

/-- The pieces of `splitBy` and its separators make up the string (and the current piece). -/
theorem splitBy_length (sep : w8) : ∀ (s cur : GoString),
    ((Net.splitBy sep s cur).map List.length).sum + (Net.splitBy sep s cur).length =
      s.length + cur.length + 1
  | [], cur => by simp [Net.splitBy]
  | d :: s, cur => by
    simp only [Net.splitBy]
    by_cases hd : d.toNat = sep.toNat
    · rw [if_pos hd]
      have := splitBy_length sep s []
      simp only [List.map_cons, List.sum_cons, List.length_cons, List.length_reverse,
        List.length_nil] at this ⊢
      omega
    · rw [if_neg hd]
      have := splitBy_length sep s (d :: cur)
      simp only [List.length_cons] at this ⊢
      omega

/-- A value of digits after `acc` is at least `acc` shifted by the digits. -/
theorem digitsVal_ge : ∀ (s : GoString) (acc n : Nat), Net.digitsVal s acc = some n →
    acc * 10 ^ s.length ≤ n
  | [], acc, n, h => by simp [Net.digitsVal] at h; simp [h]
  | c :: s, acc, n, h => by
    simp only [Net.digitsVal] at h
    by_cases hc : Net.isDigit c = true
    · rw [if_pos hc] at h
      have := digitsVal_ge s _ n h
      simp only [List.length_cons, Nat.pow_succ]
      have h2 : acc * (10 ^ s.length * 10) ≤ (acc * 10 + (c.toNat - 48)) * 10 ^ s.length := by
        rw [Nat.add_mul, Nat.mul_comm (10 ^ s.length) 10, ← Nat.mul_assoc]
        exact Nat.le_add_right _ _
      omega
    · rw [if_neg hc] at h; simp at h

/-- A canonical numeral of a value below `10 ^ k` has at most `k` digits. -/
theorem decNat_length_le : ∀ (s : GoString) (n k : Nat), Net.decNat s = some n → n < 10 ^ k →
    1 ≤ k → s.length ≤ k
  | [], _, _, h, _, _ => by simp [Net.decNat] at h
  | [_], _, _, _, _, hk => by simpa using hk
  | c :: d :: s, n, k, h, hn, _ => by
    simp only [Net.decNat] at h
    by_cases h0 : c.toNat = 48
    · rw [if_pos h0] at h; simp at h
    · rw [if_neg h0] at h
      have hdig := digitsVal_digits _ 0 n h c (by simp)
      have h' : Net.digitsVal (d :: s) (0 * 10 + (c.toNat - 48)) = some n := by
        rw [Net.digitsVal, if_pos hdig] at h; exact h
      have hge := digitsVal_ge _ _ n h'
      unfold Net.isDigit at hdig
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hdig
      have h1 : 1 ≤ 0 * 10 + (c.toNat - 48) := by omega
      have hlt : 10 ^ (d :: s).length < 10 ^ k :=
        Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_mul_of_pos_left _ h1) hge) hn
      have := (Nat.pow_lt_pow_iff_right (by omega)).1 hlt
      simp only [List.length_cons] at this ⊢
      omega

/-- **A valid address has at most 21 bytes**: four octets of at most three digits, a port of at
most five, three dots and a colon. -/
theorem addrOk_length_le {a : GoString} (h : Net.addrOk a = true) : a.length ≤ 21 := by
  unfold Net.addrOk at h
  split at h
  · rename_i n1 n2 n3 n4 np hr
    have hb : n1 < 224 ∧ n2 ≤ 255 ∧ n3 ≤ 255 ∧ n4 ≤ 255 ∧ np ≤ 65535 := by
      simp only [Net.portOk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
      omega
    unfold Net.parseAddr at hr
    split at hr
    · rename_i ip p hsp
      split at hr
      · rename_i x1 x2 x3 x4 hsp2
        split at hr
        · rename_i m1 m2 m3 m4 mp e1 e2 e3 e4 e5
          simp only [Option.some.injEq, Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hr
          have l1 := splitBy_length 58 a []
          have l2 := splitBy_length 46 ip []
          rw [hsp] at l1
          rw [hsp2] at l2
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
            List.length_nil] at l1 l2
          have k1 := decNat_length_le x1 _ 3 e1 (by omega) (by omega)
          have k2 := decNat_length_le x2 _ 3 e2 (by omega) (by omega)
          have k3 := decNat_length_le x3 _ 3 e3 (by omega) (by omega)
          have k4 := decNat_length_le x4 _ 3 e4 (by omega) (by omega)
          have k5 := decNat_length_le p _ 5 e5 (by omega) (by omega)
          omega
        · simp at hr
      · simp at hr
    · simp at hr
  · simp at h

end etcd_dist
end EtcdGrove
end Perennial
