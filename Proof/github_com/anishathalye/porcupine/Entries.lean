/-
Lean-first (no Rocq counterpart).

# Porcupine: the order of `byTime` and the entries of `makeEntries` (2026-10-14)

`entryLt a b` is `byTime.Less` on two Go entries (`checker.go`): an earlier time (signed,
`int64`), or at the same time a call before a return. It is a strict weak order (two entries
are incomparable iff they have the same time and kind), as `sort.Sort` needs.

`makeEntries` builds `rawEntries ops` (a call and a return entry per operation, with its index
as id) and sorts it; `entriesFor_of_perm` shows that any permutation of `rawEntries ops`
sorted by `entryLt` satisfies `EntriesFor (histOf ops)`.
-/
module

public import Proof.github_com.anishathalye.porcupine.Defs
public import Perennial.Proof.slices.SortBasics

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace github_com.anishathalye.porcupine

open Theory

section entries
variable [GooseExts]

/-- `byTime.Less` on two entries (see the file header). -/
def entryLt (a b : entry) : Bool :=
  if a.time' = b.time' then (!a.kind' && b.kind') else decide (sint.Z a.time' < sint.Z b.time')

theorem entryLt_iff (a b : entry) :
    entryLt a b = true ↔
      sint.Z a.time' < sint.Z b.time' ∨
        (sint.Z a.time' = sint.Z b.time' ∧ a.kind' = false ∧ b.kind' = true) := by
  unfold entryLt
  have hz : a.time' = b.time' ↔ sint.Z a.time' = sint.Z b.time' := by
    constructor
    · intro h; rw [h]
    · intro h; exact BitVec.toInt_inj.mp h
  by_cases h : a.time' = b.time'
  · simp only [h, ↓reduceIte]
    cases a.kind' <;> cases b.kind' <;> simp
  · have h' : sint.Z a.time' ≠ sint.Z b.time' := fun e => h (hz.mpr e)
    simp only [h, ↓reduceIte, decide_eq_true_eq]
    constructor
    · intro hh; exact Or.inl hh
    · rintro (hh | hh)
      · exact hh
      · exact absurd hh.1 h'

/-- `byTime.Less` is a strict weak order. -/
theorem entryLt_swo : slices.StrictWeakOrder (fun a b : entry => entryLt a b = true) := by
  simp only [entryLt_iff]
  exact {
    strict_weak_order_irrefl := fun _ h => by
      rcases h with h | h
      · exact Int.lt_irrefl _ h
      · rw [h.2.1] at h; exact Bool.false_ne_true h.2.2
    strict_weak_order_trans := fun a b c h1 h2 => by
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
      · exact Or.inl (Int.lt_trans h1 h2)
      · exact Or.inl (by omega)
      · exact Or.inl (by omega)
      · rw [h1.2.2] at h2; exact absurd h2.2.1 (by simp)
    strict_weak_order_equiv := {
      refl := fun a => ⟨fun h => by
          rcases h with h | h
          · exact Int.lt_irrefl _ h
          · rw [h.2.1] at h; exact Bool.false_ne_true h.2.2,
        fun h => by
          rcases h with h | h
          · exact Int.lt_irrefl _ h
          · rw [h.2.1] at h; exact Bool.false_ne_true h.2.2⟩
      symm := fun h => ⟨h.2, h.1⟩
      trans := fun {a b c} h1 h2 => by
        obtain ⟨h1a, h1b⟩ := h1
        obtain ⟨h2a, h2b⟩ := h2
        simp only [not_or, not_and] at h1a h1b h2a h2b
        have tab : sint.Z a.time' = sint.Z b.time' := by omega
        have tbc : sint.Z b.time' = sint.Z c.time' := by omega
        have kab : a.kind' = b.kind' := by
          cases ha : a.kind' <;> cases hb : b.kind' <;> simp_all
        have kbc : b.kind' = c.kind' := by
          cases hb : b.kind' <;> cases hc : c.kind' <;> simp_all
        simp only [not_or, not_and]
        refine ⟨⟨by omega, fun _ h => ?_⟩, ⟨by omega, fun _ h => ?_⟩⟩
        · rw [← kbc, ← kab, h]; exact Bool.false_ne_true
        · rw [kab, kbc, h]; exact Bool.false_ne_true } }

/-! ## The entries `makeEntries` builds -/

/-- The call entry of operation `o`, numbered `k`. -/
def callE (o : Operation) (k : Nat) : entry :=
  ⟨false, o.Input', W64 (k : Int), o.Call', o.ClientId', o.Metadata'⟩

/-- The return entry of operation `o`, numbered `k`. -/
def retE (o : Operation) (k : Nat) : entry :=
  ⟨true, o.Output', W64 (k : Int), o.Return', o.ClientId', o.Metadata'⟩

/-- `makeEntries`' list before the sort: a call and a return entry per operation, numbered by
its index. -/
def rawEntries (ops : List Operation) : List entry :=
  ops.zipIdx.flatMap fun p => [callE p.1 p.2, retE p.1 p.2]

theorem rawEntries_nil : rawEntries [] = [] := rfl

theorem rawEntries_snoc (l : List Operation) (o : Operation) :
    rawEntries (l ++ [o]) = rawEntries l ++ [callE o l.length, retE o l.length] := by
  unfold rawEntries
  rw [List.zipIdx_append, List.flatMap_append, List.zipIdx_singleton]
  simp

theorem rawEntries_length (ops : List Operation) : (rawEntries ops).length = 2 * ops.length := by
  simp [rawEntries, List.length_flatMap, List.map_const', List.sum_replicate_nat]; omega

theorem mem_rawEntries {ops : List Operation} {e : entry} :
    e ∈ rawEntries ops ↔ ∃ k o, ops[k]? = some o ∧ (e = callE o k ∨ e = retE o k) := by
  unfold rawEntries
  simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨⟨o, k⟩, hm, he⟩
    exact ⟨k, o, List.mem_zipIdx_iff_getElem?.1 hm, he⟩
  · rintro ⟨k, o, hk, he⟩
    exact ⟨(o, k), List.mem_zipIdx_iff_getElem?.2 hk, he⟩

theorem sintZ_W64_small {k : Nat} (h : (k : Int) < 2 ^ 60) : sint.Z (W64 (k : Int)) = k := by
  word

theorem entryOf_callE (o : Operation) {k : Nat} (hk : (k : Int) < 2 ^ 60) :
    entryOf (callE o k) = ⟨false, k⟩ := by
  simp only [entryOf, callE, sintZ_W64_small hk, Int.toNat_natCast]

theorem entryOf_retE (o : Operation) {k : Nat} (hk : (k : Int) < 2 ^ 60) :
    entryOf (retE o k) = ⟨true, k⟩ := by
  simp only [entryOf, retE, sintZ_W64_small hk, Int.toNat_natCast]

/-- What an entry of `rawEntries ops` carries. -/
theorem rawEntries_facts {ops : List Operation} {e : entry} (hn : (ops.length : Int) < 2 ^ 60)
    (he : e ∈ rawEntries ops) :
    ∃ (k : Nat) (o : Operation), ops[k]? = some o ∧ sint.Z e.id' = k ∧
      (if e.kind' then e.value' = o.Output' ∧ e.time' = o.Return'
       else e.value' = o.Input' ∧ e.time' = o.Call') := by
  obtain ⟨k, o, hk, he⟩ := mem_rawEntries.1 he
  have hlt : k < ops.length := (List.getElem?_eq_some_iff.1 hk).1
  have hz : sint.Z (W64 (k : Int)) = k := sintZ_W64_small (by omega)
  refine ⟨k, o, hk, ?_, ?_⟩
  · rcases he with rfl | rfl <;> exact hz
  · rcases he with rfl | rfl <;> simp [callE, retE]

theorem histOf_getElem? (ops : List Operation) (k : Nat) :
    (histOf ops)[k]? = (ops[k]?).map opOf := by
  simp [histOf]

/-- An entry's abstract time is its Go time. -/
theorem timeOf_entryOf {ops : List Operation} {e : entry} (hn : (ops.length : Int) < 2 ^ 60)
    (he : e ∈ rawEntries ops) :
    timeOf (histOf ops) (entryOf e) = sint.Z e.time' := by
  obtain ⟨k, o, hk, hid, hv⟩ := rawEntries_facts hn he
  unfold timeOf entryOf
  simp only [hid, Int.toNat_natCast, histOf_getElem?, hk, Option.map_some]
  cases hkd : e.kind' <;> simp only [hkd, ↓reduceIte] at hv ⊢ <;> rw [hv.2] <;> rfl

/-- On entries of `rawEntries ops`, `Theory.Less` is `byTime.Less`. -/
theorem less_entryOf {ops : List Operation} {a b : entry} (hn : (ops.length : Int) < 2 ^ 60)
    (ha : a ∈ rawEntries ops) (hb : b ∈ rawEntries ops) :
    Less (histOf ops) (entryOf a) (entryOf b) ↔ entryLt a b = true := by
  rw [entryLt_iff]
  unfold Less
  rw [timeOf_entryOf hn ha, timeOf_entryOf hn hb]
  rfl

/-- A sorted permutation of `rawEntries ops` is what `makeEntries` promises. -/
theorem entriesFor_of_sorted {ops : List Operation} {es : List entry} (hok : HistOk ops)
    (hp : (rawEntries ops).Perm es)
    (hs : ∀ (i j : Nat) (a b : entry), es[i]? = some a → es[j]? = some b → i < j →
      entryLt b a = false) :
    EntriesFor (histOf ops) es := by
  obtain ⟨hn, hcr⟩ := hok
  have hmem : ∀ e, e ∈ es → e ∈ rawEntries ops := fun e h => hp.symm.subset h
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [← hp.length_eq, rawEntries_length]; simp [histOf]
  · rw [List.pairwise_map, List.pairwise_iff_getElem]
    intro i j hi hj hij hl
    have ha := List.getElem_mem hi
    have hb := List.getElem_mem hj
    rw [less_entryOf hn (hmem _ hb) (hmem _ ha)] at hl
    rw [hs i j _ _ (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem hj) hij] at hl
    exact Bool.false_ne_true hl
  · intro e
    constructor
    · intro he
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he
      obtain ⟨k, o, hk, hid, -⟩ := rawEntries_facts hn (hmem x hx)
      simp only [entryOf, hid, Int.toNat_natCast, histOf, List.length_map]
      exact (List.getElem?_eq_some_iff.1 hk).1
    · intro he
      simp only [histOf, List.length_map] at he
      obtain ⟨o, ho⟩ : ∃ o, ops[e.id]? = some o := ⟨_, List.getElem?_eq_getElem he⟩
      have hz : (e.id : Int) < 2 ^ 60 := by omega
      let x := if e.isRet then retE o e.id else callE o e.id
      have hx : x ∈ rawEntries ops := by
        rw [mem_rawEntries]; refine ⟨e.id, o, ho, ?_⟩
        by_cases h : e.isRet <;> simp [x, h]
      refine List.mem_map.2 ⟨x, hp.subset hx, ?_⟩
      cases e with
      | mk r k =>
        cases r
        · exact entryOf_callE o hz
        · exact entryOf_retE o hz
  · intro o ho
    simp only [histOf, List.mem_map] at ho
    obtain ⟨o', ho', rfl⟩ := ho
    exact hcr o' ho'
  · intro e he
    obtain ⟨k, o, hk, hid, hv⟩ := rawEntries_facts hn (hmem e he)
    refine ⟨by omega, opOf o, ?_, ?_⟩
    · rw [hid, Int.toNat_natCast, histOf_getElem?, hk]; rfl
    · cases hkd : e.kind' <;> simp only [hkd, ↓reduceIte] at hv ⊢ <;>
        exact ⟨hv.1, by rw [hv.2]; rfl⟩

end entries

end github_com.anishathalye.porcupine
end Perennial
