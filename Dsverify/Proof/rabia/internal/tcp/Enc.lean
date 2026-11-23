/- (Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/tcp/Enc.lean`, run `rabia-r1wake-1`.) -/
module

public import Dsverify.Proof.rabia.Core.Model

@[expose] public section

namespace Perennial.rabia.model

/-! ## Varints -/

theorem varint_ne_nil (n : Nat) : varint n ≠ [] := by
  rw [varint]; split <;> simp

theorem varint_eq (n : Nat) : varint n =
    if n < 128 then [BitVec.ofNat 8 n] else BitVec.ofNat 8 (n % 128 + 128) :: varint (n / 128) := by
  rw [varint]; simp

theorem varint_cons (n : Nat) :
    ∃ c r, varint n = c :: r ∧ (c.toNat < 128 ↔ n < 128) := by
  rw [varint]; split
  · refine ⟨_, _, rfl, ?_⟩; simp [BitVec.toNat_ofNat]; omega
  · refine ⟨_, _, rfl, ?_⟩; simp [BitVec.toNat_ofNat]; omega

theorem varint_inj {a b : Nat} {x y : List w8} (h : varint a ++ x = varint b ++ y) :
    a = b ∧ x = y := by
  induction a using Nat.strongRecOn generalizing b with
  | _ a ih =>
    rw [varint_eq a, varint_eq b] at h
    by_cases ha : a < 128 <;> by_cases hb : b < 128 <;> simp [ha, hb] at h
    · obtain ⟨h1, h2⟩ := h
      have := congrArg BitVec.toNat h1
      simp [BitVec.toNat_ofNat] at this
      exact ⟨by omega, h2⟩
    · have := congrArg BitVec.toNat h.1
      simp [BitVec.toNat_ofNat] at this; omega
    · have := congrArg BitVec.toNat h.1
      simp [BitVec.toNat_ofNat] at this; omega
    · obtain ⟨h1, h2⟩ := h
      have := congrArg BitVec.toNat h1
      simp [BitVec.toNat_ofNat] at this
      obtain ⟨e1, e2⟩ := ih (a / 128) (by omega) h2
      exact ⟨by omega, e2⟩

/-! ## Tag bounds -/

/-- The list is empty or starts with a byte `≥ k`. -/
def TagGe (k : Nat) (l : List w8) : Prop := ∀ c, l.head? = some c → k ≤ c.toNat

theorem tagGe_nil (k : Nat) : TagGe k [] := by simp [TagGe]

theorem tagGe_cons {k : Nat} {c : w8} (l : List w8) (h : k ≤ c.toNat) : TagGe k (c :: l) := by
  simp [TagGe, h]

theorem tagGe_append {k : Nat} {l r : List w8} (hl : TagGe k l) (hr : TagGe k r) :
    TagGe k (l ++ r) := by
  cases l with
  | nil => simpa using hr
  | cons c l => simpa [TagGe] using hl

theorem tagGe_encScalar {k : Nat} {t : w8} (n : Nat) (h : k ≤ t.toNat) :
    TagGe k (encScalar t n) := by
  unfold encScalar; split
  · exact tagGe_nil k
  · exact tagGe_cons _ h

theorem tagGe_encBytes {k : Nat} {t : w8} (bs : List w8) (h : k ≤ t.toNat) :
    TagGe k (encBytes t bs) := by
  unfold encBytes; exact tagGe_cons _ h

theorem tagGe_encPacked {k : Nat} {t : w8} (ns : List w32) (h : k ≤ t.toNat) :
    TagGe k (encPacked t ns) := by
  unfold encPacked; split
  · exact tagGe_nil k
  · exact tagGe_encBytes _ h

theorem tagGe_flatMap_encBytes {k : Nat} {t : w8} (l : List (List w8)) (h : k ≤ t.toNat) :
    TagGe k (l.flatMap (encBytes t)) := by
  induction l with
  | nil => exact tagGe_nil k
  | cons c l ih => rw [List.flatMap_cons]; exact tagGe_append (tagGe_encBytes _ h) ih

theorem tagGe_null {k : Nat} (b : Bool) (h : k ≤ 0x20) :
    TagGe k (if b then [(0x20 : w8), 1] else []) := by
  cases b
  · exact tagGe_nil k
  · exact tagGe_cons _ (by simpa using h)

theorem tagGe_obj {k : Nat} (o : Option ObjV) (h : k ≤ 0x22) :
    TagGe k (match o with | none => [] | some o => encBytes 0x22 (encObj o)) := by
  cases o
  · exact tagGe_nil k
  · exact tagGe_encBytes _ (by simpa using h)

theorem tagGe_lt {k : Nat} {t : w8} {l : List w8} (h : TagGe k (t :: l)) : k ≤ t.toNat :=
  h t rfl

/-- Discharges `TagGe` side goals of the field-parsing lemmas. -/
local macro "tag_ge" : tactic => `(tactic| (
  repeat (first
    | apply tagGe_append
    | apply tagGe_nil
    | (apply tagGe_encScalar; decide)
    | (apply tagGe_encPacked; decide)
    | (apply tagGe_flatMap_encBytes; decide)
    | (apply tagGe_null; decide)
    | (apply tagGe_obj; decide))))

/-! ## Field parsing -/

theorem encScalar_inj {t : w8} {a b : Nat} {x y : List w8}
    (h : encScalar t a ++ x = encScalar t b ++ y)
    (hx : TagGe (t.toNat + 1) x) (hy : TagGe (t.toNat + 1) y) : a = b ∧ x = y := by
  unfold encScalar at h
  by_cases ha : a = 0 <;> by_cases hb : b = 0
  · simp only [ha, hb, ↓reduceIte] at h; exact ⟨by omega, h⟩
  · simp only [ha, hb, ↓reduceIte] at h; subst h; have := tagGe_lt hx; omega
  · simp only [ha, hb, ↓reduceIte] at h; subst h; have := tagGe_lt hy; omega
  · simp only [ha, hb, ↓reduceIte] at h
    simp only [List.cons_append, List.cons.injEq, true_and] at h
    exact varint_inj h

theorem encBytes_inj {t : w8} {a b x y : List w8}
    (h : encBytes t a ++ x = encBytes t b ++ y) : a = b ∧ x = y := by
  unfold encBytes at h
  simp only [List.cons_append, List.cons.injEq, true_and, List.append_assoc] at h
  obtain ⟨hl, h⟩ := varint_inj h
  exact List.append_inj h hl

theorem flatMap_varint_inj {l1 l2 : List w32}
    (h : (l1.flatMap fun n => varint n.toNat) = l2.flatMap fun n => varint n.toNat) :
    l1 = l2 := by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => rfl
    | cons b l2 =>
      simp only [List.flatMap_nil, List.flatMap_cons] at h
      exact absurd (List.append_eq_nil_iff.mp h.symm).1 (varint_ne_nil _)
  | cons a l1 ih =>
    cases l2 with
    | nil =>
      simp only [List.flatMap_nil, List.flatMap_cons] at h
      exact absurd (List.append_eq_nil_iff.mp h).1 (varint_ne_nil _)
    | cons b l2 =>
      simp only [List.flatMap_cons] at h
      obtain ⟨h1, h2⟩ := varint_inj h
      rw [BitVec.eq_of_toNat_eq h1, ih h2]

theorem encPacked_inj {t : w8} {a b : List w32} {x y : List w8}
    (h : encPacked t a ++ x = encPacked t b ++ y)
    (hx : TagGe (t.toNat + 1) x) (hy : TagGe (t.toNat + 1) y) : a = b ∧ x = y := by
  unfold encPacked at h
  by_cases ha : a = [] <;> by_cases hb : b = [] <;> simp only [ha, hb, ↓reduceIte,
    List.nil_append] at h
  · exact ⟨by rw [ha, hb], h⟩
  · subst h; unfold encBytes at hx; have := tagGe_lt hx; omega
  · rw [← h] at hy; unfold encBytes at hy; have := tagGe_lt hy; omega
  · obtain ⟨h1, h2⟩ := encBytes_inj h
    exact ⟨flatMap_varint_inj h1, h2⟩

theorem flatMap_encBytes_inj {t : w8} {l1 l2 : List (List w8)}
    (h : l1.flatMap (encBytes t) = l2.flatMap (encBytes t)) : l1 = l2 := by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => rfl
    | cons b l2 => simp [encBytes] at h
  | cons a l1 ih =>
    cases l2 with
    | nil => simp [encBytes] at h
    | cons b l2 =>
      simp only [List.flatMap_cons] at h
      obtain ⟨h1, h2⟩ := encBytes_inj h
      rw [h1, ih h2]

theorem null_inj {p q : Bool} {x y : List w8}
    (h : (if p then [(0x20 : w8), 1] else []) ++ x = (if q then [(0x20 : w8), 1] else []) ++ y)
    (hx : TagGe 0x21 x) (hy : TagGe 0x21 y) : p = q ∧ x = y := by
  cases p <;> cases q <;> simp at h
  · exact ⟨rfl, h⟩
  · subst h; have := tagGe_lt hx; simp at this
  · subst h; have := tagGe_lt hy; simp at this
  · exact ⟨rfl, h⟩

theorem enumNat_inj {a b : w32} (h : enumNat a = enumNat b) : a = b := by
  unfold enumNat at h
  have h' := BitVec.eq_of_toNat_eq h
  have key : ∀ a b : BitVec 32, BitVec.signExtend 64 a = BitVec.signExtend 64 b → a = b := by
    -- bit by bit (no `bv_decide`: its native-code axiom would enter the trust base)
    intro a b h
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    have := congrArg (fun x => x.getLsbD i) h
    simp only [BitVec.getLsbD_signExtend] at this
    simpa [hi, show i < 64 by omega] using this
  exact key a b h'

/-! ## Records -/

theorem encObj_inj {a b : ObjV} (h : encObj a = encObj b) : a = b := by
  unfold encObj at h
  simp only [List.append_assoc] at h
  obtain ⟨h1, h⟩ := encScalar_inj h (by tag_ge) (by tag_ge)
  obtain ⟨h2, h⟩ := encScalar_inj h (by tag_ge) (by tag_ge)
  obtain ⟨h3, h⟩ := encScalar_inj h (by tag_ge) (by tag_ge)
  obtain ⟨h4, h⟩ := null_inj h (by tag_ge) (by tag_ge)
  obtain ⟨h5, h⟩ := encPacked_inj h (by tag_ge) (by tag_ge)
  obtain ⟨h6, h⟩ := encPacked_inj h (by tag_ge) (by tag_ge)
  have h7 := flatMap_encBytes_inj h
  cases a; cases b
  simp only at h1 h2 h3 h4 h5 h6 h7
  rw [BitVec.eq_of_toNat_eq h1, BitVec.eq_of_toNat_eq h2, BitVec.eq_of_toNat_eq h3, h4, h5, h6,
    h7]

theorem encCmd_inj {a b : CmdV} (h : encCmd a = encCmd b) : a = b := by
  unfold encCmd at h
  simp only [List.append_assoc] at h
  obtain ⟨h1, h⟩ := encScalar_inj h (by tag_ge) (by tag_ge)
  obtain ⟨h2, h⟩ := encScalar_inj h (by tag_ge) (by tag_ge)
  obtain ⟨h3, h⟩ := encScalar_inj h (by tag_ge) (by tag_ge)
  have h4 := flatMap_encBytes_inj h
  cases a; cases b
  simp only at h1 h2 h3 h4
  rw [BitVec.eq_of_toNat_eq h1, BitVec.eq_of_toNat_eq h2, BitVec.eq_of_toNat_eq h3, h4]

theorem encMsg_inj {a b : MsgV} (h : encMsg a = encMsg b) : a = b := by
  unfold encMsg at h
  simp only [List.append_assoc] at h
  obtain ⟨h1, h⟩ := encScalar_inj h (by tag_ge) (by tag_ge)
  obtain ⟨h2, h⟩ := encScalar_inj h (by tag_ge) (by tag_ge)
  obtain ⟨h3, h⟩ := encScalar_inj h (by tag_ge) (by tag_ge)
  have h4 : a.obj = b.obj := by
    revert h
    cases a.obj <;> cases b.obj <;> simp [encBytes]
    intro h
    rw [encObj_inj (varint_inj h).2]
  cases a; cases b
  simp only at h1 h2 h3 h4
  rw [enumNat_inj h1, BitVec.eq_of_toNat_eq h2, BitVec.eq_of_toNat_eq h3, h4]

/-! ## Frames -/

theorem frame_length (bs : List w8) : (frame bs).length = 4 + bs.length := by
  simp [frame]; omega

theorem frame_app_inj {a b x y : List w8} (ha : a.length < 2^32) (hb : b.length < 2^32)
    (h : frame a ++ x = frame b ++ y) : a = b ∧ x = y := by
  simp only [frame, List.cons_append, List.nil_append, List.cons.injEq] at h
  obtain ⟨e0, e1, e2, e3, h⟩ := h
  have e0 := congrArg BitVec.toNat e0
  have e1 := congrArg BitVec.toNat e1
  have e2 := congrArg BitVec.toNat e2
  have e3 := congrArg BitVec.toNat e3
  simp only [BitVec.toNat_ofNat] at e0 e1 e2 e3
  have hl : a.length = b.length := by omega
  exact List.append_inj h hl

theorem frame_prefix_inj {a b y : List w8} (ha : a.length < 2^32) (hb : b.length < 2^32)
    (h : frame a <+: frame b ++ y) : a = b := by
  obtain ⟨t, ht⟩ := h
  exact (frame_app_inj ha hb ht).1

theorem frames_next {L : List (List w8)} {j : Nat} {bs X : List w8}
    (hL : ∀ p ∈ L, p.length < 2^32) (hbs : bs.length < 2^32)
    (h : frames (L.take j) ++ frame bs ++ X <+: frames L) : L[j]? = some bs := by
  induction L generalizing j with
  | nil =>
    simp only [List.take_nil, frames, List.flatMap_nil, List.nil_append,
      List.prefix_nil] at h
    simp [frame] at h
  | cons p L ih =>
    cases j with
    | zero =>
      simp only [List.take_zero, frames, List.flatMap_nil, List.nil_append,
        List.flatMap_cons] at h
      obtain ⟨t, ht⟩ := h
      simp only [List.append_assoc] at ht
      have := (frame_app_inj hbs (hL p (by simp)) ht).1
      simp [this]
    | succ j =>
      simp only [List.take_succ_cons, frames, List.flatMap_cons, List.append_assoc] at h
      rw [List.prefix_append_right_inj] at h
      simp only [List.getElem?_cons_succ]
      apply ih (fun q hq => hL q (by simp [hq]))
      simpa only [frames, List.append_assoc] using h

theorem frames_next_pre {pre : List w8} {L : List (List w8)} {j : Nat} {bs X : List w8}
    (hL : ∀ p ∈ L, p.length < 2^32) (hbs : bs.length < 2^32)
    (h : pre ++ frames (L.take j) ++ frame bs ++ X <+: pre ++ frames L) : L[j]? = some bs := by
  simp only [List.append_assoc] at h
  rw [List.prefix_append_right_inj] at h
  exact frames_next hL hbs (by simpa only [List.append_assoc] using h)

end Perennial.rabia.model
