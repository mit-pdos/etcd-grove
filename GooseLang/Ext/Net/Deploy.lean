/-
Facts about the net extension's valid addresses (`Impl.lean`'s `addrOk`, D20), proved, not
trusted: a valid address is at most 21 bytes long (`addrOk_length`: `255.255.255.255:65535`), so
the valid addresses are finitely many (`addrSpace`, the domain of the network's per-address ghost
state, `Ghost.lean`), and none is a wildcard (`addrOk_wildPort`: a listener at a valid address takes
only the connections dialed to it, `lisAccepts_addrOk`).

Until v3.4 (2026-11-20) this file held the deployment's plan and its well-formedness
(`PlanWellFormed`, a premise of every theorem); the plan went (`notes/net-tcp.md`, v3.4), and with
it the premise: a program shows `addrOk` of each address it listens at or dials.
-/
module

public import GooseLang.Ext.Net.Impl

@[expose] public section

namespace Perennial

namespace Net

/-! ## The length of a valid address -/

theorem splitBy_len (sep : w8) : ∀ (s cur : GoString),
    ((splitBy sep s cur).map List.length).sum + (splitBy sep s cur).length =
      s.length + cur.length + 1
  | [], cur => by simp [splitBy]
  | c :: s, cur => by
    unfold splitBy
    split
    · have := splitBy_len sep s []
      simp only [List.map_cons, List.sum_cons, List.length_cons, List.length_reverse,
        List.length_nil] at this ⊢
      omega
    · have := splitBy_len sep s (c :: cur)
      simp only [List.length_cons] at this ⊢
      omega

theorem digitsVal_ge : ∀ (s : GoString) (acc n : Nat), digitsVal s acc = some n →
    acc * 10 ^ s.length ≤ n
  | [], acc, n, h => by simp [digitsVal] at h; simp [h]
  | c :: s, acc, n, h => by
    unfold digitsVal at h
    split at h
    · have := digitsVal_ge s _ n h
      rw [List.length_cons, Nat.pow_succ]
      calc acc * (10 ^ s.length * 10) = (acc * 10) * 10 ^ s.length := by
            rw [Nat.mul_comm (10 ^ s.length) 10, Nat.mul_assoc]
        _ ≤ (acc * 10 + (c.toNat - 48)) * 10 ^ s.length :=
            Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
        _ ≤ n := this
    · cases h

/-- A canonical numeral of `k ≥ 2` digits is at least `10 ^ (k - 1)`. -/
theorem decNat_ge {x : GoString} {n : Nat} (h : decNat x = some n) :
    x.length ≤ 1 ∨ 10 ^ (x.length - 1) ≤ n := by
  match x, h with
  | [], h => simp [decNat] at h
  | [_], _ => exact .inl (by simp)
  | c :: d :: s, h =>
    right
    simp only [decNat] at h
    split at h
    · cases h
    · rename_i hc
      unfold digitsVal at h
      split at h
      · rename_i hd
        have := digitsVal_ge (d :: s) _ n h
        simp only [List.length_cons, Nat.add_sub_cancel] at this ⊢
        simp only [isDigit, Bool.and_eq_true, decide_eq_true_eq] at hd
        have h1 : 1 ≤ 0 * 10 + (c.toNat - 48) := by omega
        calc 10 ^ (s.length + 1) = 1 * 10 ^ (s.length + 1) := (Nat.one_mul _).symm
          _ ≤ (0 * 10 + (c.toNat - 48)) * 10 ^ (s.length + 1) := Nat.mul_le_mul_right _ h1
          _ ≤ n := this
      · cases h

theorem decNat_len {x : GoString} {n k : Nat} (h : decNat x = some n) (hn : n < 10 ^ k) :
    x.length ≤ k ∨ x.length ≤ 1 := by
  rcases decNat_ge h with h1 | h1
  · exact .inr h1
  · left
    have : 10 ^ (x.length - 1) < 10 ^ k := Nat.lt_of_le_of_lt h1 hn
    have := (Nat.pow_lt_pow_iff_right (by decide : 1 < 10)).mp this
    omega

theorem parseAddr_some {a : GoString} {n1 n2 n3 n4 p : Nat}
    (h : parseAddr a = some (n1, n2, n3, n4, p)) :
    ∃ ip ps x1 x2 x3 x4, splitBy 58 a [] = [ip, ps] ∧ splitBy 46 ip [] = [x1, x2, x3, x4] ∧
      decNat x1 = some n1 ∧ decNat x2 = some n2 ∧ decNat x3 = some n3 ∧ decNat x4 = some n4 ∧
      decNat ps = some p := by
  unfold parseAddr at h
  split at h
  · split at h
    · split at h
      · rename_i _ ip ps hs _ x1 x2 x3 x4 hs' _ _ _ _ _ m1 m2 m3 m4 mp h1 h2 h3 h4 h5
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
        exact ⟨ip, ps, x1, x2, x3, x4, hs, hs', h1, h2, h3, h4, h5⟩
      · cases h
    · cases h
  · cases h

/-- A valid address is at most 21 bytes long (`255.255.255.255:65535`). -/
theorem addrOk_length {a : GoString} (h : addrOk a = true) : a.length ≤ 21 := by
  unfold addrOk at h
  cases hp : parseAddr a with
  | none => rw [hp] at h; cases h
  | some t =>
    obtain ⟨n1, n2, n3, n4, port⟩ := t
    rw [hp] at h
    simp only [portOk, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at h
    obtain ⟨ip, ps, x1, x2, x3, x4, hs, hs', h1, h2, h3, h4, h5⟩ := parseAddr_some hp
    have la := splitBy_len 58 a []
    have li := splitBy_len 46 ip []
    rw [hs] at la; rw [hs'] at li
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at la li
    have e1 := decNat_len (k := 3) h1
      (by rw [show (10 : Nat) ^ 3 = 1000 from rfl]; omega)
    have e2 := decNat_len (k := 3) h2
      (by rw [show (10 : Nat) ^ 3 = 1000 from rfl]; omega)
    have e3 := decNat_len (k := 3) h3
      (by rw [show (10 : Nat) ^ 3 = 1000 from rfl]; omega)
    have e4 := decNat_len (k := 3) h4
      (by rw [show (10 : Nat) ^ 3 = 1000 from rfl]; omega)
    have e5 := decNat_len (k := 5) h5
      (by rw [show (10 : Nat) ^ 5 = 100000 from rfl]; omega)
    omega

/-! ## A valid address is not a wildcard -/

theorem stripPrefix_some : ∀ {p a r : GoString}, stripPrefix p a = some r → a = p ++ r
  | [], a, r, h => by simp [stripPrefix] at h; simp [h]
  | _ :: _, [], _, h => by simp [stripPrefix] at h
  | c :: p, x :: a, r, h => by
    simp only [stripPrefix] at h
    split at h
    · rename_i hc; subst hc; rw [stripPrefix_some h]; rfl
    · cases h

theorem splitBy_prefix (sep : w8) : ∀ (s cur x : GoString) (rest : List GoString),
    splitBy sep s cur = x :: rest → ∃ t, cur.reverse ++ s = x ++ t
  | [], cur, x, rest, h => by
    simp only [splitBy, List.cons.injEq] at h
    exact ⟨[], by rw [← h.1]⟩
  | c :: s, cur, x, rest, h => by
    unfold splitBy at h
    split at h
    · simp only [List.cons.injEq] at h
      exact ⟨c :: s, by rw [← h.1]⟩
    · obtain ⟨t, ht⟩ := splitBy_prefix sep s (c :: cur) x rest h
      exact ⟨t, by rw [← ht]; simp⟩

/-- A canonical numeral of a positive number starts with a nonzero digit. -/
theorem decNat_head {x : GoString} {n : Nat} (h : decNat x = some n) (hn : 1 ≤ n) :
    ∃ c t, x = c :: t ∧ isDigit c = true ∧ c.toNat ≠ 48 := by
  match x, h with
  | [], h => simp [decNat] at h
  | [c], h =>
    simp only [decNat, digitsVal] at h
    split at h
    · rename_i hc
      simp only [Option.some.injEq] at h
      refine ⟨c, [], rfl, hc, fun e => ?_⟩
      rw [e] at h; omega
    · cases h
  | c :: d :: t, h =>
    simp only [decNat] at h
    split at h
    · cases h
    · rename_i hc
      unfold digitsVal at h
      split at h
      · rename_i hd
        exact ⟨c, d :: t, rfl, hd, hc⟩
      · cases h

/-- A valid address starts with a nonzero digit (its first octet's). -/
theorem addrOk_head {a : GoString} (h : addrOk a = true) :
    ∃ c t, a = c :: t ∧ isDigit c = true ∧ c.toNat ≠ 48 := by
  unfold addrOk at h
  cases hp : parseAddr a with
  | none => rw [hp] at h; cases h
  | some q =>
    obtain ⟨n1, n2, n3, n4, port⟩ := q
    rw [hp] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨ip, ps, x1, x2, x3, x4, hs, hs', h1, -, -, -, -⟩ := parseAddr_some hp
    obtain ⟨c, t, rfl, hc, h0⟩ := decNat_head h1 h.1.1.1.1.1
    obtain ⟨u, hu⟩ := splitBy_prefix 58 a [] ip [ps] hs
    obtain ⟨v, hv⟩ := splitBy_prefix 46 ip [] (c :: t) [x2, x3, x4] hs'
    simp only [List.reverse_nil, List.nil_append] at hu hv
    subst hv
    exact ⟨c, t ++ v ++ u, by rw [hu]; simp, hc, h0⟩

/-- No valid address is a wildcard spelling. -/
theorem addrOk_wildPort {a : GoString} (h : addrOk a = true) : wildPort a = none := by
  obtain ⟨c, t, rfl, hc, h0⟩ := addrOk_head h
  unfold wildPort
  have e1 : stripPrefix go!":" (c :: t) = none := by
    cases h1 : stripPrefix go!":" (c :: t) with
    | none => rfl
    | some r =>
      have := stripPrefix_some h1
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at this
      rw [this.1] at hc; exact absurd hc (by decide)
  have e2 : stripPrefix go!"0.0.0.0:" (c :: t) = none := by
    cases h1 : stripPrefix go!"0.0.0.0:" (c :: t) with
    | none => rfl
    | some r =>
      have := stripPrefix_some h1
      simp only [List.cons_append, List.cons.injEq] at this
      rw [this.1] at h0; exact absurd rfl h0
  have e3 : stripPrefix go!"[::]:" (c :: t) = none := by
    cases h1 : stripPrefix go!"[::]:" (c :: t) with
    | none => rfl
    | some r =>
      have := stripPrefix_some h1
      simp only [List.cons_append, List.cons.injEq] at this
      rw [this.1] at hc; exact absurd hc (by decide)
  rw [e1, e2, e3]; rfl

/-- A listener at a valid address takes only the connections dialed to it. -/
theorem lisAccepts_addrOk {la a : GoString} (h : addrOk la = true) : lisAccepts la a ↔ la = a := by
  unfold lisAccepts
  rw [addrOk_wildPort h]
  simp

/-! ## The valid addresses, finitely many -/

/-- Every byte. -/
def allBytes : List w8 := (List.range 256).map (BitVec.ofNat 8)

theorem mem_allBytes (c : w8) : c ∈ allBytes := by
  unfold allBytes
  refine List.mem_map.mpr ⟨c.toNat, List.mem_range.mpr c.isLt, ?_⟩
  simp

/-- Every byte string of at most `n` bytes. -/
def strsUpTo : Nat → List GoString
  | 0 => [[]]
  | n + 1 => [] :: allBytes.flatMap (fun c => (strsUpTo n).map (c :: ·))

theorem mem_strsUpTo : ∀ (n : Nat) (s : GoString), s.length ≤ n → s ∈ strsUpTo n
  | 0, [], _ => by simp [strsUpTo]
  | n + 1, [], _ => by simp [strsUpTo]
  | n + 1, c :: s, h => by
    simp only [strsUpTo, List.mem_cons, List.mem_flatMap, List.mem_map]
    exact .inr ⟨c, mem_allBytes c, s, mem_strsUpTo n s (by simp at h; omega), rfl⟩
  | 0, _ :: _, h => by simp at h

/-- The valid addresses are finitely many (`addrOk_length`). -/
theorem addrs_finite : ∃ l : List GoString, ∀ a, a ∈ l ↔ addrOk a = true :=
  ⟨(strsUpTo 21).filter addrOk, fun a => by
    rw [List.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨mem_strsUpTo 21 a (addrOk_length h), h⟩⟩⟩

/-- The valid addresses, as a list (chosen: it is never computed). -/
noncomputable def addrList : List GoString := Classical.choose addrs_finite

theorem mem_addrList {a : GoString} : a ∈ addrList ↔ addrOk a = true :=
  Classical.choose_spec addrs_finite a

/-- The map from every valid address to `v`. -/
noncomputable def addrSpace {V : Type} (v : V) : GMap GoString V :=
  GMap.ofList (addrList.map (·, v))

theorem ofList_map_const_mem {V : Type} (v : V) : ∀ (l : List GoString) (a : GoString),
    a ∈ l → (GMap.ofList (l.map (·, v))) !! a = some v
  | [], _, h => absurd h List.not_mem_nil
  | x :: l, a, h => by
    simp only [List.map_cons, GMap.ofList]
    by_cases hx : x = a
    · subst hx; exact GMap.lookup_insert _ _ _
    · rw [GMap.lookup_insert_ne _ _ hx]
      exact ofList_map_const_mem v l a ((List.mem_cons.mp h).resolve_left (fun e => hx e.symm))

theorem ofList_map_const_not_mem {V : Type} (v : V) : ∀ (l : List GoString) (a : GoString),
    a ∉ l → (GMap.ofList (l.map (·, v))) !! a = none
  | [], _, _ => rfl
  | x :: l, a, h => by
    simp only [List.map_cons, GMap.ofList]
    have hx : x ≠ a := fun e => h (e ▸ List.mem_cons_self)
    rw [GMap.lookup_insert_ne _ _ hx]
    exact ofList_map_const_not_mem v l a (fun hm => h (List.mem_cons_of_mem _ hm))

theorem addrSpace_lookup_ok {V : Type} (v : V) {a : GoString} (h : addrOk a = true) :
    (addrSpace v) !! a = some v :=
  ofList_map_const_mem v addrList a (mem_addrList.mpr h)

theorem addrSpace_lookup_isSome {V : Type} (v : V) (a : GoString) :
    ((addrSpace v) !! a).isSome = addrOk a := by
  cases h : addrOk a
  · have : a ∉ addrList := fun hm => by rw [mem_addrList.mp hm] at h; cases h
    show ((GMap.ofList (addrList.map (·, v))) !! a).isSome = false
    rw [ofList_map_const_not_mem v addrList a this]; rfl
  · rw [addrSpace_lookup_ok v h]; rfl

theorem addrSpace_lookup_some {V : Type} {v w : V} {a : GoString}
    (h : (addrSpace v) !! a = some w) : w = v := by
  cases ha : addrOk a
  · have := addrSpace_lookup_isSome v a; rw [h, ha] at this; cases this
  · rw [addrSpace_lookup_ok v ha] at h; exact (Option.some.inj h).symm

/-- Valid and not: a few spellings. -/
example : addrOk go!"127.0.0.1:7101" = true := by decide
example : addrOk go!"10.0.0.5:7001" = true := by decide
example : addrOk go!":7101" = false := by decide
example : addrOk go!"localhost:7101" = false := by decide
example : addrOk go!"127.0.0.01:7101" = false := by decide
example : addrOk go!"127.0.0.1:40000" = false := by decide
example : addrOk go!"127.0.0.1:0" = false := by decide
example : addrOk go!"0.1.2.3:7101" = false := by decide
example : addrOk go!"224.0.0.1:7101" = false := by decide
example : wildOk go!":7101" = true := by decide
example : wildOk go!"0.0.0.0:7101" = true := by decide
example : wildOk go!"[::]:7101" = true := by decide
example : wildOk go!":07101" = false := by decide
example : wildOk go!":40000" = false := by decide

end Net

end Perennial
