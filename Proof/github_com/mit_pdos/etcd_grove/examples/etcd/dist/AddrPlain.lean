/- Lean-first (no Rocq counterpart).

# `etcd/dist`: a valid net address makes a plain peer URL

A deployment's addresses are the net extension's valid ones (`Net.addrOk`: the canonical `a.b.c.d:p`);
etcd's peer URLs are `http://` and the address, and rafthttp's specs take them plain
(`types.plainPeerURL`: `http://host:port`, host bytes then one `:` then digits). Pure: the address's
parse (`Net.parseAddr`, through `Net.splitBy` and `Net.decNat`) gives exactly that shape. Used by
`putget_safe`'s member boot (`etcd_putget_dist.member_boot`) and, for every member, by `etcd_safe`.
-/
module

public import GooseLang.Ext.Net.Impl
public import Proof.go_etcd_io.etcd.client.pkg.v3.types.URLs

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

end etcd_dist
end EtcdGrove
end Perennial
