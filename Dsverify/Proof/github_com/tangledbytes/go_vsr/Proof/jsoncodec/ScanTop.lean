/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/jsoncodec/ScanTop.lean (lab master 915f964;
notes/dsv-vr.md).
-/
/-
The scanner on a whole value (at the top) and on a prefix of one (it asks for more).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.jsoncodec.ScanLemmas

@[expose] public section

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace VsrJson

open Perennial

theorem prefix_app {p a b : List w8} (h : p <+: a ++ b) :
    p <+: a ∨ ∃ b', p = a ++ b' ∧ b' <+: b := by
  obtain ⟨t, ht⟩ := h
  rcases List.append_eq_append_iff.1 ht with ⟨a', h1, h2⟩ | ⟨bs, h1, h2⟩
  · left; exact ⟨a', h1.symm⟩
  · right; exact ⟨bs, h1, ⟨t, h2.symm⟩⟩

theorem goL_spaces (ws cs : List w8) (hws : ∀ c ∈ ws, spB c = true) (i : Nat) (stk : List w8)
    (st : Nat) (eOK eof : Bool) :
    goL (ws ++ cs) i stk st eOK eof = goL cs (i + ws.length) stk st eOK eof := by
  induction ws generalizing i with
  | nil => simp
  | cons c ws ih =>
    simp only [List.cons_append]
    rw [goL_space (hc := hws c (by simp)), ih (fun x hx => hws x (by simp [hx]))]
    congr 1; simp; omega

theorem first_ne (v : JV) : ∃ c r, ser v = c :: r ∧ spB c = false ∧ c ≠ 93#8 := by
  cases v with
  | num n =>
    obtain ⟨d, ds, hdn⟩ : ∃ d ds, decN n = d :: ds := by
      cases h : decN n with
      | nil => exact absurd h (decN_ne_nil n)
      | cons d ds => exact ⟨d, ds, rfl⟩
    have hdd : isDig d = true := decN_digits n d (by rw [hdn]; simp)
    obtain ⟨hsp, -, -, h3, -, -⟩ := isDig_ne d hdd
    exact ⟨d, ds, by rw [ser_num, hdn], hsp, h3⟩
  | str s => exact ⟨_, _, ser_str s, by decide, by decide⟩
  | obj ms => exact ⟨_, _, ser_obj ms, by decide, by decide⟩
  | arr vs => exact ⟨_, _, ser_arr vs, by decide, by decide⟩

/-- A whole value at the top: done at its end. -/
theorem top_v (v : JV) (hv : v.ok) (rest : List w8) (i : Nat) (eOK eof : Bool)
    (hd : v.depth ≤ maxDepth) (ht : termOK v rest) :
    goL (ser v ++ rest) i [] 0 eOK eof = (0, i + (ser v).length) := by
  match v with
  | .num n =>
    obtain ⟨c, r, rfl, hc⟩ := ht
    obtain ⟨d, ds, hdn⟩ : ∃ d ds, decN n = d :: ds := by
      cases h : decN n with
      | nil => exact absurd h (decN_ne_nil n)
      | cons d ds => exact ⟨d, ds, rfl⟩
    have hdd : isDig d = true := decN_digits n d (by rw [hdn]; simp)
    obtain ⟨hsp, h1, h2, h3, h34, -⟩ := isDig_ne d hdd
    have hnum := numL_full n c r hc i (eof && ([] : List w8).isEmpty)
    rw [ser_num, hdn] at *
    simp only [List.cons_append]
    rw [goL_scalar (hs := hsp) (hc1 := h1) (hc2 := h2) (hc3 := h3)]
    simp only [scalarL, h34, hdd, or_true, if_true, if_false, ite_false, ite_true]
    simp only [List.cons_append] at hnum
    rw [hnum]
    simp
  | .str s =>
    have hs : ∀ c ∈ s, okB c := by simpa [JV.ok] using hv
    rw [ser_str]
    simp only [List.cons_append, List.append_assoc, List.singleton_append, List.nil_append]
    rw [goL_scalar (hs := by decide) (hc1 := by decide) (hc2 := by decide) (hc3 := by decide)]
    simp only [scalarL, if_true, ite_true, strL_full s _ hs]
    simp; omega
  | .obj ms =>
    have hms : ms.ok := by simpa [JV.ok] using hv
    have hdep : JV.depth (.obj ms) = ms.depth + 1 := by simp [JV.depth]
    rw [ser_obj]
    simp only [List.cons_append, List.append_assoc, List.singleton_append, List.nil_append]
    rw [goL_open (hc := by decide) (hd := by simp only [List.length_nil]; omega)]
    simp only [if_true, ite_true]
    rw [full_ms ms hms rest (i + 1) [] eof (by simp; omega)]
    simp [closeR]; omega
  | .arr vs =>
    have hvs : vs.ok := by simpa [JV.ok] using hv
    have hdep : JV.depth (.arr vs) = vs.depth + 1 := by simp [JV.depth]
    rw [ser_arr]
    simp only [List.cons_append, List.append_assoc, List.singleton_append, List.nil_append]
    rw [goL_open (hc := by decide) (hd := by simp only [List.length_nil]; omega)]
    simp only [show (91#8 : w8) ≠ 123#8 by decide, if_false, ite_false]
    rw [full_vs vs hvs rest (i + 1) [] eof (by simp; omega)]
    simp [closeR]; omega

/-- A member (key, colon, value) and what follows `T`, from state 2: any strict prefix asks
for more, given that the value's prefixes do and `T`'s strict prefixes do (from state 1). -/
theorem part_mem (eof : Bool) (k : List w8) (v : JV) (T : List w8) (stk : List w8) (hk : ∀ c ∈ k, okB c)
    (hv : v.ok) (hstk : stk ≠ []) (hd : stk.length + v.depth ≤ maxDepth) (hT : termOK v T)
    (hvp : ∀ p, p <+: ser v → ∀ j eOK, (goL p j stk 0 eOK eof).1 = 1)
    (hTp : ∀ t, t <+: T → t ≠ T → ∀ j, (goL t j stk 1 false eof).1 = 1)
    (q : List w8) (hq : q <+: 34#8 :: (k ++ 34#8 :: 58#8 :: (ser v ++ T)))
    (hne : q ≠ 34#8 :: (k ++ 34#8 :: 58#8 :: (ser v ++ T))) (i : Nat) (eOK : Bool) :
    (goL q i stk 2 eOK eof).1 = 1 := by
  rcases List.prefix_cons_iff.1 hq with rfl | ⟨q1, rfl, hq1⟩
  · rw [goL_nil]
  rw [goL_key]
  have e1 : k ++ 34#8 :: 58#8 :: (ser v ++ T) = (k ++ [34#8]) ++ (58#8 :: (ser v ++ T)) := by simp
  rw [e1] at hq1
  rcases prefix_app hq1 with h | ⟨b, rfl, hb⟩
  · rcases prefix_app h with h' | ⟨b', rfl, hb'⟩
    · have hok : ∀ c ∈ q1, okB c := fun c hc => hk c (h'.subset hc)
      simp [strL_part q1 hok]
    · rcases List.prefix_cons_iff.1 hb' with rfl | ⟨w, rfl, hnil⟩
      · simp only [List.append_nil]
        simp [strL_part k hk]
      · have hw : w = [] := by simpa using hnil
        subst hw
        have := strL_full k [] hk (i + 1)
        simp only [this]
        rw [show i + 1 + k.length + 1 - i - 1 = k.length + 1 by omega]
        simp only [List.drop_append, List.length_cons]
        rw [List.drop_eq_nil_of_le (by simp)]
        simp [goL_nil]
  · rcases List.prefix_cons_iff.1 hb with rfl | ⟨b2, rfl, hb2⟩
    · simp only [List.append_nil]
      have := strL_full k [] hk (i + 1)
      try simp only [List.append_assoc, List.singleton_append] at this ⊢
      simp only [this]
      rw [show i + 1 + k.length + 1 - i - 1 = k.length + 1 by omega]
      simp only [List.drop_append, List.length_cons]
      rw [List.drop_eq_nil_of_le (by simp)]
      simp [goL_nil]
    have := strL_full k (58#8 :: b2) hk (i + 1)
    try simp only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] at this ⊢
    simp only [this]
    try simp only [ne_eq, not_true_eq_false, if_false, ite_false]
    rw [show i + 1 + k.length + 1 - i - 1 = k.length + 1 by omega]
    rw [show (k ++ 34#8 :: 58#8 :: b2).drop (k.length + 1) = 58#8 :: b2 by simp [List.drop_append]]
    rw [goL_colon]
    rcases prefix_app hb2 with h | ⟨t, rfl, ht⟩
    · exact hvp b2 h _ _
    · by_cases htT : t = T
      · subst htT; simp at hne
      · rcases t with _ | ⟨c, t'⟩
        · simp only [List.append_nil]; exact hvp _ (List.prefix_refl _) _ _
        · rw [full_v v hv _ _ _ _ _ hstk hd ?_]
          · exact hTp _ ht htT _
          · cases v with
            | num n =>
              obtain ⟨c0, r0, rfl, hc0⟩ := hT
              rw [List.cons_prefix_cons] at ht
              exact ⟨c, t', rfl, by rw [ht.1]; exact hc0⟩
            | _ => trivial

/-- An element and what follows `T`, from state 0: any strict prefix asks for more. -/
theorem part_elem (eof : Bool) (v : JV) (T : List w8) (stk : List w8)
    (hv : v.ok) (hstk : stk ≠ []) (hd : stk.length + v.depth ≤ maxDepth) (hT : termOK v T)
    (hvp : ∀ p, p <+: ser v → ∀ j eOK, (goL p j stk 0 eOK eof).1 = 1)
    (hTp : ∀ t, t <+: T → t ≠ T → ∀ j, (goL t j stk 1 false eof).1 = 1)
    (q : List w8) (hq : q <+: ser v ++ T) (hne : q ≠ ser v ++ T) (i : Nat) (eOK : Bool) :
    (goL q i stk 0 eOK eof).1 = 1 := by
  rcases prefix_app hq with h | ⟨t, rfl, ht⟩
  · exact hvp q h _ _
  · by_cases htT : t = T
    · subst htT; simp at hne
    · rcases t with _ | ⟨c, t'⟩
      · simp only [List.append_nil]; exact hvp _ (List.prefix_refl _) _ _
      · rw [full_v v hv _ _ _ _ _ hstk hd ?_]
        · exact hTp _ ht htT _
        · cases v with
          | num n =>
            obtain ⟨c0, r0, rfl, hc0⟩ := hT
            rw [List.cons_prefix_cons] at ht
            exact ⟨c, t', rfl, by rw [ht.1]; exact hc0⟩
          | _ => trivial

theorem termOK_msT (v : JV) (ms : JMs) : termOK v (serMsT ms ++ [125#8]) := by
  cases v <;> simp [termOK]
  cases ms <;> simp [serMsT] <;> first | exact numEnd_comma | exact numEnd_rb

theorem termOK_vsT (v : JV) (vs : JVs) : termOK v (serVsT vs ++ [93#8]) := by
  cases v <;> simp [termOK]
  cases vs <;> simp [serVsT] <;> first | exact numEnd_comma | exact numEnd_rs

theorem decN_head48 (n : Nat) (p : List w8) (hp : p <+: decN n) (h : p.head? = some 48#8) :
    p.length = 1 := by
  by_cases hn : n = 0
  · subst hn; rw [decN_zero] at hp
    rcases List.prefix_cons_iff.1 hp with rfl | ⟨t, rfl, ht⟩
    · simp at h
    · rw [List.prefix_nil] at ht; subst ht; rfl
  · obtain ⟨c, r, hdn, hc⟩ := decN_head n hn
    rw [hdn] at hp
    rcases List.prefix_cons_iff.1 hp with rfl | ⟨t, rfl, ht⟩
    · simp at h
    · simp at h; exact absurd h hc

mutual
theorem part_v (eof : Bool) (v : JV) (hv : v.ok) (stk : List w8) (hd : stk.length + v.depth ≤ maxDepth)
    (hn : ∀ n, v = .num n → (eof && stk.isEmpty) = false) (p : List w8) (hp : p <+: ser v) (hne : stk ≠ [] ∨ p ≠ ser v) (i : Nat) (eOK : Bool) :
    (goL p i stk 0 eOK eof).1 = 1 := by
  match v with
  | .num n =>
    rcases p with _ | ⟨d, p'⟩
    · rw [goL_nil]
    have hdd : isDig d = true := decN_digits n d (hp.subset (by simp))
    obtain ⟨hsp, h1, h2, h3, h34, h45⟩ := isDig_ne d hdd
    rw [goL_scalar (hs := hsp) (hc1 := h1) (hc2 := h2) (hc3 := h3)]
    have hnum := numL_part (d :: p') (by simp) (fun c hc => decN_digits n c (hp.subset hc))
      (decN_head48 n _ hp) i
    rw [← hn n rfl] at hnum
    simp only [scalarL, h34, hdd, or_true, if_true, if_false, ite_false, ite_true, hnum]
    simp
  | .str s =>
    have hs : ∀ c ∈ s, okB c := by simpa [JV.ok] using hv
    rw [ser_str] at hp hne
    rcases List.prefix_cons_iff.1 hp with rfl | ⟨q, rfl, hq⟩
    · rw [goL_nil]
    rw [goL_scalar (hs := by decide) (hc1 := by decide) (hc2 := by decide) (hc3 := by decide)]
    simp only [scalarL, if_true, ite_true]
    rcases prefix_app hq with h | ⟨b, rfl, hb⟩
    · have hok : ∀ c ∈ q, okB c := fun c hc => hs c (h.subset hc)
      simp [strL_part q hok]
    · rcases List.prefix_cons_iff.1 hb with rfl | ⟨w, rfl, hw⟩
      · simp [strL_part s hs]
      · rw [List.prefix_nil] at hw; subst hw
        have hstk : stk ≠ [] := by
          rcases hne with h | h
          · exact h
          · simp at h
        simp only [strL_full s [] hs (i + 1), hstk]
        simp only [ne_eq, not_true_eq_false, if_false, ite_false]
        rw [show i + 1 + s.length + 1 - i - 1 = s.length + 1 by omega]
        simp only [List.drop_append, List.length_cons]
        rw [List.drop_eq_nil_of_le (by simp)]
        simp [goL_nil]
  | .obj ms =>
    have hms : ms.ok := by simpa [JV.ok] using hv
    have hdep : JV.depth (.obj ms) = ms.depth + 1 := by simp [JV.depth]
    by_cases hfull : p = ser (.obj ms)
    · have hstk : stk ≠ [] := by
        rcases hne with h | h
        · exact h
        · exact absurd hfull h
      subst hfull
      have := full_v (.obj ms) hv [] i stk eOK eof hstk hd trivial
      rw [List.append_nil] at this
      rw [this, goL_nil]
    rw [ser_obj] at hp hfull
    rcases List.prefix_cons_iff.1 hp with rfl | ⟨q, rfl, hq⟩
    · rw [goL_nil]
    rw [goL_open (hc := by decide) (hd := by omega)]
    simp only [if_true, ite_true]
    exact part_ms eof ms hms stk (by omega) q hq (by intro h; apply hfull; rw [h]; simp) _ _
  | .arr vs =>
    have hvs : vs.ok := by simpa [JV.ok] using hv
    have hdep : JV.depth (.arr vs) = vs.depth + 1 := by simp [JV.depth]
    by_cases hfull : p = ser (.arr vs)
    · have hstk : stk ≠ [] := by
        rcases hne with h | h
        · exact h
        · exact absurd hfull h
      subst hfull
      have := full_v (.arr vs) hv [] i stk eOK eof hstk hd trivial
      rw [List.append_nil] at this
      rw [this, goL_nil]
    rw [ser_arr] at hp hfull
    rcases List.prefix_cons_iff.1 hp with rfl | ⟨q, rfl, hq⟩
    · rw [goL_nil]
    rw [goL_open (hc := by decide) (hd := by omega)]
    simp only [show (91#8 : w8) ≠ 123#8 by decide, if_false, ite_false]
    exact part_vs eof vs hvs stk (by omega) q hq (by intro h; apply hfull; rw [h]; simp) _

theorem part_ms (eof : Bool) (ms : JMs) (hms : ms.ok) (stk0 : List w8)
    (hd : stk0.length + 1 + ms.depth ≤ maxDepth) (q : List w8)
    (hq : q <+: serMs ms ++ [125#8]) (hne : q ≠ serMs ms ++ [125#8]) (i : Nat) (eOK : Bool) :
    (goL q i (123#8 :: stk0) 2 eOK eof).1 = 1 := by
  match ms with
  | .nil =>
    rw [serMs_nil] at hq hne
    rcases List.prefix_cons_iff.1 hq with rfl | ⟨w, rfl, hw⟩
    · rw [goL_nil]
    · rw [List.prefix_nil] at hw; subst hw; simp at hne
  | .cons k v ms' =>
    simp only [JMs.ok] at hms
    simp only [JMs.depth] at hd
    rw [serMs_cons] at hq hne
    simp only [List.cons_append, List.append_assoc] at hq hne
    exact part_mem eof k v _ _ hms.1 hms.2.1 (by simp) (by simp; omega) (termOK_msT v ms')
      (fun p hp j e => part_v eof v hms.2.1 _ (by simp; omega) (by simp) p hp (Or.inl (by simp)) j e)
      (fun t ht htne j => part_msT eof ms' hms.2.2 stk0 (by omega) t ht htne j) q hq hne i eOK

theorem part_msT (eof : Bool) (ms : JMs) (hms : ms.ok) (stk0 : List w8)
    (hd : stk0.length + 1 + ms.depth ≤ maxDepth) (t : List w8)
    (ht : t <+: serMsT ms ++ [125#8]) (hne : t ≠ serMsT ms ++ [125#8]) (i : Nat) :
    (goL t i (123#8 :: stk0) 1 false eof).1 = 1 := by
  match ms with
  | .nil =>
    rw [serMsT_nil] at ht hne
    rcases List.prefix_cons_iff.1 ht with rfl | ⟨w, rfl, hw⟩
    · rw [goL_nil]
    · rw [List.prefix_nil] at hw; subst hw; simp at hne
  | .cons k v ms' =>
    simp only [JMs.ok] at hms
    simp only [JMs.depth] at hd
    rw [serMsT_cons] at ht hne
    simp only [List.cons_append, List.append_assoc] at ht hne
    rcases List.prefix_cons_iff.1 ht with rfl | ⟨w, rfl, hw⟩
    · rw [goL_nil]
    rw [goL_comma]
    simp only [if_true, ite_true]
    exact part_mem eof k v _ _ hms.1 hms.2.1 (by simp) (by simp; omega) (termOK_msT v ms')
      (fun p hp j e => part_v eof v hms.2.1 _ (by simp; omega) (by simp) p hp (Or.inl (by simp)) j e)
      (fun t ht htne j => part_msT eof ms' hms.2.2 stk0 (by omega) t ht htne j) w hw
      (by intro h; apply hne; rw [h]) _ _

theorem part_vs (eof : Bool) (vs : JVs) (hvs : vs.ok) (stk0 : List w8)
    (hd : stk0.length + 1 + vs.depth ≤ maxDepth) (q : List w8)
    (hq : q <+: serVs vs ++ [93#8]) (hne : q ≠ serVs vs ++ [93#8]) (i : Nat) :
    (goL q i (91#8 :: stk0) 0 true eof).1 = 1 := by
  match vs with
  | .nil =>
    rw [serVs_nil] at hq hne
    rcases List.prefix_cons_iff.1 hq with rfl | ⟨w, rfl, hw⟩
    · rw [goL_nil]
    · rw [List.prefix_nil] at hw; subst hw; simp at hne
  | .cons v vs' =>
    simp only [JVs.ok] at hvs
    simp only [JVs.depth] at hd
    rw [serVs_cons] at hq hne
    simp only [List.append_assoc] at hq hne
    exact part_elem eof v _ _ hvs.1 (by simp) (by simp; omega) (termOK_vsT v vs')
      (fun p hp j e => part_v eof v hvs.1 _ (by simp; omega) (by simp) p hp (Or.inl (by simp)) j e)
      (fun t ht htne j => part_vsT eof vs' hvs.2 stk0 (by omega) t ht htne j) q hq hne i true

theorem part_vsT (eof : Bool) (vs : JVs) (hvs : vs.ok) (stk0 : List w8)
    (hd : stk0.length + 1 + vs.depth ≤ maxDepth) (t : List w8)
    (ht : t <+: serVsT vs ++ [93#8]) (hne : t ≠ serVsT vs ++ [93#8]) (i : Nat) :
    (goL t i (91#8 :: stk0) 1 false eof).1 = 1 := by
  match vs with
  | .nil =>
    rw [serVsT_nil] at ht hne
    rcases List.prefix_cons_iff.1 ht with rfl | ⟨w, rfl, hw⟩
    · rw [goL_nil]
    · rw [List.prefix_nil] at hw; subst hw; simp at hne
  | .cons v vs' =>
    simp only [JVs.ok] at hvs
    simp only [JVs.depth] at hd
    rw [serVsT_cons] at ht hne
    simp only [List.cons_append, List.append_assoc] at ht hne
    rcases List.prefix_cons_iff.1 ht with rfl | ⟨w, rfl, hw⟩
    · rw [goL_nil]
    rw [goL_comma]
    simp only [show (91#8 : w8) ≠ 123#8 by decide, if_false, ite_false]
    exact part_elem eof v _ _ hvs.1 (by simp) (by simp; omega) (termOK_vsT v vs')
      (fun p hp j e => part_v eof v hvs.1 _ (by simp; omega) (by simp) p hp (Or.inl (by simp)) j e)
      (fun t ht htne j => part_vsT eof vs' hvs.2 stk0 (by omega) t ht htne j) w hw
      (by intro h; apply hne; rw [h]) _ _
end

end VsrJson
