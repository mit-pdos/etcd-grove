/-
Lemmas of the proof of the trace's logger (`logInfo`; traceutil-log, 2026-11-23). Lean-first (no
Rocq counterpart).

**Regions** (`logInfo`'s first loop): `logInfo` merges a subtrace's fields into its steps' with
`t.steps[j].fields = append(tstep.fields, t.steps[j].fields...)`. When `tstep.fields` has spare
capacity, the append writes it in place, so several steps' fields may share one array, and a later
append overwrites what an earlier step's fields show
(`nonissues/etcd-traceutil-subtrace-fields-aliasing.md`). The proof owns the arrays, not the steps'
slices: a region `(R, m)` (`R` a slice whose length is its capacity) holds some fields whose first
`m` are formattable (`regionOwn`), and every step's fields slice is `R[0:l]` of some region, `l ≤ m`
(`sliceIn`). An append in place writes formattable fields into `R[l:l+k]`, keeping that
(`wp_region_append`); one that reallocates makes a new region.
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.traceutil.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode _root_.Perennial.go_etcd_io.etcd.pkg.v3


section pure
variable [GooseExts] [go_gctx : GoGlobalContext] [GoSemanticsFunctions]

theorem traceutil.fieldsWf_iff_mem {l : List traceutil.Field} :
    traceutil.fieldsWf l ↔ ∀ f ∈ l, traceutil.fieldsWf [f] := by
  unfold traceutil.fieldsWf _root_.Perennial.fmt.ArgsWf
  constructor
  · intro h f hf ii hi
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hi
    exact h ii (by rw [hi]; exact List.mem_map_of_mem hf)
  · intro h ii hi
    obtain ⟨f, hf, he⟩ := List.mem_map.1 hi
    exact h f hf ii (by simp [he])

theorem traceutil.fieldsWf_of_subset {l l' : List traceutil.Field} (h : traceutil.fieldsWf l)
    (hs : ∀ x ∈ l', x ∈ l) : traceutil.fieldsWf l' :=
  traceutil.fieldsWf_iff_mem.2 fun f hf => traceutil.fieldsWf_iff_mem.1 h f (hs f hf)

/-- Writing formattable fields `w` at `[a, a + |w|)` of `cs`, `a ≤ m`, the first `m` formattable:
the first `max m (a + |w|)` are. -/
theorem traceutil.fieldsWf_write (cs w : List traceutil.Field) (a m : Nat) (ha : a ≤ m)
    (hcs : a + w.length ≤ cs.length) (hwf : traceutil.fieldsWf (cs.take m))
    (hw : traceutil.fieldsWf w) :
    traceutil.fieldsWf ((cs.take a ++ w ++ cs.drop (a + w.length)).take (max m (a + w.length))) := by
  apply traceutil.fieldsWf_of_subset (l := cs.take m ++ w)
  · exact traceutil.fieldsWf_iff_mem.2 fun f hf => by
      rcases List.mem_append.1 hf with h | h
      · exact traceutil.fieldsWf_iff_mem.1 hwf f h
      · exact traceutil.fieldsWf_iff_mem.1 hw f h
  intro x hx
  have hl1 : (cs.take a ++ w).length = a + w.length := by
    simp only [List.length_append, List.length_take]; omega
  rw [List.take_append, hl1] at hx
  rcases List.mem_append.1 hx with h | h
  · have h := List.mem_of_mem_take h
    rcases List.mem_append.1 h with h | h
    · exact List.mem_append_left _ (List.take_subset_take_left _ ha h)
    · exact List.mem_append_right _ h
  · apply List.mem_append_left
    by_cases hm : a + w.length ≤ m
    · rw [List.take_drop] at h
      have h := List.mem_of_mem_drop h
      have : a + w.length + (max m (a + w.length) - (a + w.length)) = m := by omega
      rwa [this] at h
    · exfalso
      have : max m (a + w.length) - (a + w.length) = 0 := by omega
      rw [this] at h
      simp at h

/-- A region after a write of formattable fields `w` at `[a, a + |w|)`, `a ≤ m`: its first
`max m (a + |w|)` fields are formattable. -/
theorem traceutil.region_write_ok (cs w : List traceutil.Field) (a m : Nat) (ha : a ≤ m)
    (hm : m ≤ cs.length) (hcs : a + w.length ≤ cs.length) (hwf : traceutil.fieldsWf (cs.take m))
    (hw : traceutil.fieldsWf w) :
    max m (a + w.length) ≤ (cs.take a ++ w ++ cs.drop (a + w.length)).length ∧
    traceutil.fieldsWf ((cs.take a ++ w ++ cs.drop (a + w.length)).take (max m (a + w.length))) := by
  refine ⟨?_, traceutil.fieldsWf_write cs w a m ha hcs hwf hw⟩
  simp only [List.length_append, List.length_take, List.length_drop]
  omega

theorem traceutil.fieldsWf_subslice0 {cs : List traceutil.Field} {l m : Nat} (hl : l ≤ m)
    (h : traceutil.fieldsWf (cs.take m)) : traceutil.fieldsWf (subslice 0 l cs) := by
  apply traceutil.fieldsWf_of_subset h
  intro x hx
  simp only [subslice, List.drop_zero] at hx
  exact List.take_subset_take_left _ hl hx

/-- The slice `sl` is `R[0:l]` of the region `r = (R, m)`, `l ≤ m`. -/
def traceutil.inRegion (r : GoSlice × Nat) (sl : GoSlice) : Prop :=
  ∃ l : w64, sl = slice.slice r.1 traceutil.Field (W64 0) l ∧ 0 ≤ sint.Z l ∧
    sint.Z l ≤ sint.Z r.1.len ∧ sint.nat l ≤ r.2

/-- The slice `sl` is in one of the regions `regs`. -/
def traceutil.sliceIn (regs : List (GoSlice × Nat)) (sl : GoSlice) : Prop :=
  ∃ (k : Nat) (r : GoSlice × Nat), regs[k]? = some r ∧ traceutil.inRegion r sl

/-- `regs'` keeps every region of `regs`, at an index, with at least as many formattable fields. -/
def traceutil.regsLe (regs regs' : List (GoSlice × Nat)) : Prop :=
  ∀ (k : Nat) (r : GoSlice × Nat), regs[k]? = some r → ∃ m', regs'[k]? = some (r.1, m') ∧ r.2 ≤ m'

theorem traceutil.list_set_self {A : Type} {l : List A} {k : Nat} {x : A} (h : l[k]? = some x) :
    l.set k x = l := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_set]
  split
  · subst_vars; rw [h]; simp [(List.getElem?_eq_some_iff.1 h).1]
  · rfl

theorem traceutil.regsLe_refl (regs : List (GoSlice × Nat)) : traceutil.regsLe regs regs :=
  fun _ r h => ⟨r.2, by rw [h], Nat.le_refl _⟩

theorem traceutil.regsLe_trans {r1 r2 r3 : List (GoSlice × Nat)} (h1 : traceutil.regsLe r1 r2)
    (h2 : traceutil.regsLe r2 r3) : traceutil.regsLe r1 r3 := by
  intro k r h
  obtain ⟨m', h', hm⟩ := h1 k r h
  obtain ⟨m'', h'', hm'⟩ := h2 k (r.1, m') h'
  exact ⟨m'', h'', Nat.le_trans hm hm'⟩

theorem traceutil.regsLe_snoc (regs : List (GoSlice × Nat)) (r : GoSlice × Nat) :
    traceutil.regsLe regs (regs ++ [r]) := by
  intro k r' h
  refine ⟨r'.2, ?_, Nat.le_refl _⟩
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 h).1, h]

theorem traceutil.regsLe_set {regs : List (GoSlice × Nat)} {k : Nat} {R : GoSlice} {m m' : Nat}
    (hk : regs[k]? = some (R, m)) (hm : m ≤ m') : traceutil.regsLe regs (regs.set k (R, m')) := by
  intro k' r h
  by_cases hkk : k = k'
  · subst hkk
    rw [hk] at h
    cases h
    refine ⟨m', ?_, hm⟩
    rw [List.getElem?_set_self (List.getElem?_eq_some_iff.1 hk).1]
  · refine ⟨r.2, ?_, Nat.le_refl _⟩
    rw [List.getElem?_set_ne hkk, h]

theorem traceutil.inRegion_mono {r : GoSlice × Nat} {m' : Nat} {sl : GoSlice}
    (h : traceutil.inRegion r sl) (hm : r.2 ≤ m') : traceutil.inRegion (r.1, m') sl := by
  obtain ⟨l, h1, h2, h3, h4⟩ := h
  exact ⟨l, h1, h2, h3, Nat.le_trans h4 hm⟩

theorem traceutil.sliceIn_mono {regs regs' : List (GoSlice × Nat)} {sl : GoSlice}
    (h : traceutil.regsLe regs regs') (hs : traceutil.sliceIn regs sl) :
    traceutil.sliceIn regs' sl := by
  obtain ⟨k, r, hk, hr⟩ := hs
  obtain ⟨m', hk', hm⟩ := h k r hk
  exact ⟨k, _, hk', traceutil.inRegion_mono hr hm⟩

theorem traceutil.sliceIn_cons {regs : List (GoSlice × Nat)} {sl : GoSlice} (r : GoSlice × Nat)
    (hs : traceutil.sliceIn regs sl) : traceutil.sliceIn (r :: regs) sl := by
  obtain ⟨k, r', hk, hr⟩ := hs
  exact ⟨k + 1, r', by simpa using hk, hr⟩

theorem traceutil.steps_in_mono {s2 : List traceutil.step} {r r' : List (GoSlice × Nat)}
    (hle : traceutil.regsLe r r') (h : ∀ st ∈ s2, traceutil.sliceIn r st.fields') :
    ∀ st ∈ s2, traceutil.sliceIn r' st.fields' :=
  fun st hst => traceutil.sliceIn_mono hle (h st hst)

theorem traceutil.steps_set_in {s2 : List traceutil.step} {r r' : List (GoSlice × Nat)}
    (hle : traceutil.regsLe r r') (h : ∀ st ∈ s2, traceutil.sliceIn r st.fields') (k : Nat)
    (x : traceutil.step) (hx : traceutil.sliceIn r' x.fields') :
    ∀ st ∈ s2.set k x, traceutil.sliceIn r' st.fields' := by
  intro st hst
  rcases List.mem_or_eq_of_mem_set hst with h' | h'
  · exact traceutil.sliceIn_mono hle (h st h')
  · subst h'; exact hx

end pure

section regions
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.traceutil.Assumptions]

/-- **A region** `r = (R, m)`: the array of `R`, all of it (`len(R) = cap(R)`), holding some fields
`cs` whose first `m` are formattable. -/
def traceutil.regionOwn (r : GoSlice × Nat) : IProp GF :=
  iprop(∃ cs : List traceutil.Field, r.1 ↦* cs ∗
    ⌜r.1.len = r.1.cap ∧ r.2 ≤ cs.length ∧ traceutil.fieldsWf (cs.take r.2)⌝)

/-- A slice owned with its capacity, its fields formattable, is `R[0:len]` of a region. -/
theorem traceutil.region_of_owned (sl : GoSlice) (vs : List traceutil.Field)
    (hwf : traceutil.fieldsWf vs) :
    (sl ↦* vs ∗ ownSliceCap traceutil.Field sl (DFrac.own 1) : IProp GF) ⊢
      traceutil.regionOwn (slice.slice sl traceutil.Field (W64 0) sl.cap, vs.length) ∗
      ⌜traceutil.inRegion (slice.slice sl traceutil.Field (W64 0) sl.cap, vs.length) sl⌝ := by
  iintro ⟨Hs, Hcap⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  ihave %Hcw := ownSliceCap_wf _ _ $$ Hcap
  icases ownSlice_slice_into_capacity (W64 0) sl.cap sl vs $$ [Hs Hcap] with ⟨%vc, -, H, -⟩
  · iframe; ipureintro
    have h1 : sint.Z (W64 0) ≤ sint.Z sl.cap := by have := Hcw; word
    have h2 : sint.Z sl.len ≤ sint.Z sl.cap := by have := Hcw; word
    exact ⟨by decide, h1, h2, Int.le_refl _⟩
  simp only [show sint.nat (W64 0) = 0 from rfl, List.drop_zero]
  isplitl
  · unfold traceutil.regionOwn
    iexists _
    iframe
    ipureintro
    refine ⟨by simp [slice.slice], by simp, ?_⟩
    rw [List.take_left]; exact hwf
  · ipureintro
    refine ⟨sl.len, ?_, Hlen.2, ?_, ?_⟩
    · rw [slice_slice sl (W64 0) sl.cap (W64 0) sl.len ⟨by decide, by decide⟩]
      simp only [show W64 0 + W64 0 = W64 0 by rfl, show W64 0 + sl.len = sl.len by word]
      exact slice_slice_trivial sl
    · simp only [slice.slice]; word
    · simp only; omega

/-- An owned fields slice is in a region. -/
theorem traceutil.ownFields_region (sl : GoSlice) :
    traceutil.ownFields (GF := GF) sl ⊢ ∃ r, traceutil.regionOwn r ∗ ⌜traceutil.inRegion r sl⌝ := by
  iintro Hf
  iunfold traceutil.ownFields at Hf
  icases Hf with ⟨%fs, Hs, Hcap, %Hwf⟩
  iexists _
  iapply traceutil.region_of_owned sl fs Hwf $$ [Hs Hcap]
  iframe

/-- **The steps' fields, as regions** (at `logInfo`'s start: one region per step). -/
theorem traceutil.regions_of_steps (ss : List traceutil.step) :
    ([∗list] st ∈ ss, traceutil.ownFields (GF := GF) st.fields') ⊢
      ∃ regs, ([∗list] r ∈ regs, traceutil.regionOwn r) ∗
        ⌜∀ st ∈ ss, traceutil.sliceIn regs st.fields'⌝ := by
  induction ss with
  | nil =>
    iintro -
    iexists []
    isplitl
    · iapply (BigSepL.bigSepL_nil_intro (PROP := IProp GF) (P := iprop(emp)))
      itrivial
    · ipureintro; intro st h; simp at h
  | cons st ss ih =>
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨H1, H2⟩
    icases traceutil.ownFields_region _ $$ H1 with ⟨%r, Hr, %Hr⟩
    icases ih $$ H2 with ⟨%regs, Hregs, %Hregs⟩
    iexists r :: regs
    isplitl
    · iapply BigSepL.bigSepL_cons.2
      iframe
    ipureintro
    intro st' h
    rcases List.mem_cons.1 h with h | h
    · subst h; exact ⟨0, r, rfl, Hr⟩
    · exact traceutil.sliceIn_cons r (Hregs st' h)


/-- The part `[a, b)` of an owned slice, and a way back with other elements there. -/
theorem traceutil.ownSlice_sub_acc (R : GoSlice) (cs : List traceutil.Field) (a b : w64)
    (h : 0 ≤ sint.Z a ∧ sint.Z a ≤ sint.Z b ∧ sint.Z b ≤ sint.Z R.len) :
    (R ↦* cs : IProp GF) ⊢
      slice.slice R traceutil.Field a b ↦* subslice (sint.nat a) (sint.nat b) cs ∗
      (∀ vs', ⌜vs'.length = sint.nat b - sint.nat a⌝ -∗
        slice.slice R traceutil.Field a b ↦* vs' -∗
        R ↦* (cs.take (sint.nat a) ++ vs' ++ cs.drop (sint.nat b))) := by
  obtain ⟨h0, h1, h2⟩ := h
  iintro Hs
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  icases (ownSlice_split_all a R _ cs ⟨h0, by omega⟩).1 $$ Hs with ⟨H1, H2⟩
  icases (ownSlice_split b R _ (cs.drop (sint.nat a)) a R.len ⟨h0, h1, h2⟩).1 $$ H2
    with ⟨H2, H3⟩
  have hsub : (cs.drop (sint.nat a)).take (sint.nat b - sint.nat a) =
      subslice (sint.nat a) (sint.nat b) cs := by
    simp only [subslice, List.drop_take]
  rw [hsub]
  iframe H2
  iintro %vs' %hl H2
  have hac : sint.nat a ≤ cs.length := by rw [Hlen.1]; word
  have hla : (cs.take (sint.nat a)).length = sint.nat a - sint.nat (W64 0) := by
    rw [List.length_take]; simp only [show sint.nat (W64 0) = 0 from rfl]; omega
  ihave H23 := ownSlice_combine b R _ vs' ((cs.drop (sint.nat a)).drop (sint.nat b - sint.nat a))
    a R.len ⟨hl, h0, h1, h2⟩ $$ H2 H3
  ihave H := ownSlice_combine a R _ (cs.take (sint.nat a)) _ (W64 0) R.len
    ⟨hla, by decide, h0, by word⟩ $$ H1 H23
  have hab : sint.nat a ≤ sint.nat b := by word
  rw [List.drop_drop, show sint.nat a + (sint.nat b - sint.nat a) = sint.nat b by omega,
    ← List.append_assoc] at *
  iapply (ownSlice_trivial_slice R _ _).2 $$ H

/-- **Reading a slice of a region**: its fields are formattable. -/
theorem traceutil.region_read (regs : List (GoSlice × Nat)) (sl : GoSlice)
    (hsl : traceutil.sliceIn regs sl) :
    ([∗list] r ∈ regs, traceutil.regionOwn (GF := GF) r) ⊢
      ∃ fs, sl ↦* fs ∗ ⌜traceutil.fieldsWf fs⌝ ∗
        (sl ↦* fs -∗ [∗list] r ∈ regs, traceutil.regionOwn r) := by
  obtain ⟨k, r, hk, l, rfl, hl0, hl1, hlm⟩ := hsl
  iintro Hregs
  icases (BigSepL.bigSepL_lookup_acc hk).1 $$ Hregs with ⟨Hr, Hback⟩
  iunfold traceutil.regionOwn at Hr
  icases Hr with ⟨%cs, Hs, %Hr⟩
  icases traceutil.ownSlice_sub_acc r.1 cs (W64 0) l ⟨by decide, hl0, hl1⟩ $$ Hs with ⟨Hl, Hw⟩
  iexists _
  iframe Hl
  isplitr
  · ipureintro
    apply traceutil.fieldsWf_of_subset Hr.2.2
    intro x hx
    simp only [subslice, show sint.nat (W64 0) = 0 from rfl, List.drop_zero] at hx
    exact List.take_subset_take_left _ hlm hx
  iintro Hl
  ihave %Hlen := ownSlice_len _ _ _ $$ Hl
  ihave Hs := Hw $$ %_ %(by rw [Hlen.1]; simp [slice.slice]; rfl) Hl
  rw [show List.take (sint.nat (W64 0)) cs ++ subslice (sint.nat (W64 0)) (sint.nat l) cs ++
      cs.drop (sint.nat l) = cs by
        simp only [subslice, show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.drop_zero,
          List.nil_append, List.take_append_drop]] at *
  ihave H := Hback $$ %r [Hs]
  · iunfold traceutil.regionOwn
    iexists cs
    iframe
    ipureintro; exact Hr
  rw [traceutil.list_set_self hk] at *
  iexact H


/-- The empty region (a placeholder while a region is out of the list). -/
theorem traceutil.regionOwn_nil : ⊢ traceutil.regionOwn (GF := GF) (slice.nil, 0) := by
  iunfold traceutil.regionOwn
  iexists []
  isplitl
  · iapply ownSlice_nil
  · ipureintro; exact ⟨rfl, Nat.le_refl _, traceutil.fieldsWf_nil⟩

/-- **`append(T, S...)` of two slices of regions** (`logInfo`'s merge of a subtrace's fields): in
place, into `T`'s region (`S` in the same region or another), or into a new region. -/
theorem traceutil.wp_region_append (regs : List (GoSlice × Nat)) (T S : GoSlice)
    (hT : traceutil.sliceIn regs T) (hS : traceutil.sliceIn regs S) :
    {{ ([∗list] r ∈ regs, traceutil.regionOwn (GF := GF) r) }}
      (App (App (Val #(functions go.append [go.GoType.SliceType traceutil.Field.ty])) (Val #T))
        (Val #S))
    {{ (s' : GoSlice), RET #s'; ∃ regs', ([∗list] r ∈ regs', traceutil.regionOwn r) ∗
        ⌜traceutil.regsLe regs regs' ∧ traceutil.sliceIn regs' s'⌝ }} := by
  obtain ⟨kT, rT, hkT, lT, rfl, hT0, hT1, hTm⟩ := hT
  obtain ⟨kS, rS, hkS, lS, rfl, hS0, hS1, hSm⟩ := hS
  iintro %Φ Hregs HΦ
  have hTl : (slice.slice rT.1 traceutil.Field (W64 0) lT).len = lT := by simp [slice.slice]
  have hTc : (slice.slice rT.1 traceutil.Field (W64 0) lT).cap = rT.1.cap := by simp [slice.slice]
  have hSl : (slice.slice rS.1 traceutil.Field (W64 0) lS).len = lS := by simp [slice.slice]
  by_cases hfit : sint.Z lT + sint.Z lS ≤ sint.Z rT.1.cap
  · iapply wp_slice_append_fits _ _ _ ⟨by rw [hTl]; exact hT0, by rw [hSl]; exact hS0⟩
      (by rw [hTl, hSl, hTc]; exact hfit)
    rw [hTl, hSl, slice_slice rT.1 (W64 0) lT lT (lT + lS) ⟨by word, by word⟩,
      show W64 0 + lT = lT by word, show W64 0 + (lT + lS) = lT + lS by word]
    have hss : slice.slice (slice.slice rT.1 traceutil.Field (W64 0) lT) traceutil.Field (W64 0)
        (lT + lS) = slice.slice rT.1 traceutil.Field (W64 0) (lT + lS) := by
      rw [slice_slice rT.1 (W64 0) lT (W64 0) (lT + lS) ⟨by decide, by decide⟩]
      simp only [show W64 0 + W64 0 = W64 0 from rfl, show W64 0 + (lT + lS) = lT + lS by word]
    rw [hss]
    have hnat : sint.nat (lT + lS) = sint.nat lT + sint.nat lS := by word
    by_cases hk : kT = kS
    · subst hk
      rw [hkT] at hkS
      cases hkS
      icases (BigSepL.bigSepL_lookup_acc hkT).1 $$ Hregs with ⟨Hr, Hback⟩
      iunfold traceutil.regionOwn at Hr
      icases Hr with ⟨%cs, Hs, %Hr⟩
      ihave %Hlen := ownSlice_len _ _ _ $$ Hs
      have hlen : sint.Z (lT + lS) ≤ sint.Z rT.1.len := by rw [Hr.1]; word
      wp_apply +noauto wp_slice_copy_within rT.1 cs lT (lT + lS) (W64 0) lS
        ⟨hT0, by word, hlen⟩ ⟨by decide, hS0, hS1⟩ $$ Hs with %n ⟨%Hn, Hs⟩
      isplitl []
      · ipureintro; exact isPanic_intoVal _
      have hcl : sint.nat (lT + lS) ≤ cs.length := by rw [Hlen.1]; word
      have hw : (subslice 0 (sint.nat lS) cs).length = sint.nat lS := by
        simp only [subslice, List.length_drop, List.length_take]; omega
      have heq : List.take (sint.nat lT) cs ++
          ((subslice 0 (sint.nat lS) cs).take (sint.nat (lT + lS) - sint.nat lT) ++
            (subslice (sint.nat lT) (sint.nat (lT + lS)) cs).drop (sint.nat lS - 0)) ++
          cs.drop (sint.nat (lT + lS)) =
          cs.take (sint.nat lT) ++ subslice 0 (sint.nat lS) cs ++
            cs.drop (sint.nat lT + (subslice 0 (sint.nat lS) cs).length) := by
        rw [hw, hnat, Nat.sub_zero,
          show sint.nat lT + sint.nat lS - sint.nat lT = sint.nat lS by omega,
          List.take_of_length_le (l := subslice 0 (sint.nat lS) cs) (i := sint.nat lS) (by omega),
          List.drop_of_length_le (l := subslice (sint.nat lT) (sint.nat lT + sint.nat lS) cs)
            (i := sint.nat lS) (by simp only [subslice, List.length_drop, List.length_take]; omega),
          List.append_nil]
      rw [heq]
      have hok := traceutil.region_write_ok cs (subslice 0 (sint.nat lS) cs) (sint.nat lT) rT.2 hTm
        Hr.2.1 (by rw [hw]; omega) Hr.2.2 (traceutil.fieldsWf_subslice0 hSm Hr.2.2)
      rw [hw] at hok
      ihave Hregs := Hback $$ %(rT.1, max rT.2 (sint.nat lT + sint.nat lS)) [Hs]
      · iunfold traceutil.regionOwn
        iexists _
        iframe
        ipureintro
        rw [hw]
        exact ⟨Hr.1, hok⟩
      imodintro
      iapply HΦ
      iexists _
      iframe
      ipureintro
      refine ⟨traceutil.regsLe_set hkT (Nat.le_max_left _ _), kT,
        (rT.1, max rT.2 (sint.nat lT + sint.nat lS)), ?_, lT + lS, rfl, by word, hlen,
        by rw [hnat]; exact Nat.le_max_right _ _⟩
      rw [List.getElem?_set_self (List.getElem?_eq_some_iff.1 hkT).1]
    · icases (BigSepL.bigSepL_lookup_acc hkT).1 $$ Hregs with ⟨Hr, Hback⟩
      ihave Hregs := Hback $$ %(slice.nil, 0) []
      · iapply traceutil.regionOwn_nil
      have hS' : traceutil.sliceIn (regs.set kT (slice.nil, 0))
          (slice.slice rS.1 traceutil.Field (W64 0) lS) :=
        ⟨kS, rS, by rw [List.getElem?_set_ne hk]; exact hkS, lS, rfl, hS0, hS1, hSm⟩
      icases traceutil.region_read _ _ hS' $$ Hregs with ⟨%fsS, HS, %HwfS, HbackS⟩
      iunfold traceutil.regionOwn at Hr
      icases Hr with ⟨%cs, Hs, %Hr⟩
      ihave %Hlen := ownSlice_len _ _ _ $$ Hs
      have hlen : sint.Z (lT + lS) ≤ sint.Z rT.1.len := by rw [Hr.1]; word
      icases traceutil.ownSlice_sub_acc rT.1 cs lT (lT + lS) ⟨hT0, by word, hlen⟩ $$ Hs
        with ⟨HT, HTw⟩
      ihave %HlS := ownSlice_len _ _ _ $$ HS
      ihave %HlT := ownSlice_len _ _ _ $$ HT
      wp_apply +noauto wp_slice_copy _ _ _ fsS (DFrac.own 1) $$ [HT HS] with %n ⟨%Hn, HT, HS⟩
      · iframe
      isplitl []
      · ipureintro; exact isPanic_intoVal _
      have hfl : fsS.length = sint.nat lS := by rw [HlS.1]; simp [slice.slice]
      have hsl : (subslice (sint.nat lT) (sint.nat (lT + lS)) cs).length = sint.nat lS := by
        rw [HlT.1]; simp [slice.slice]; word
      rw [hsl, ← hfl, List.take_length,
        List.drop_of_length_le (l := subslice (sint.nat lT) (sint.nat (lT + lS)) cs)
          (i := fsS.length) (by omega), List.append_nil]
      ihave Hs := HTw $$ %fsS %(by rw [hfl, hnat]; omega) HT
      ihave Hregs := HbackS $$ HS
      have hcl : sint.nat (lT + lS) ≤ cs.length := by rw [Hlen.1]; word
      rw [show sint.nat (lT + lS) = sint.nat lT + fsS.length by rw [hfl, hnat]] at *
      have hok := traceutil.region_write_ok cs fsS (sint.nat lT) rT.2 hTm Hr.2.1 (by omega) Hr.2.2 HwfS
      have hkT' : (regs.set kT (slice.nil, 0))[kT]? = some (slice.nil, 0) :=
        List.getElem?_set_self (List.getElem?_eq_some_iff.1 hkT).1
      icases (BigSepL.bigSepL_lookup_acc hkT').1 $$ Hregs with ⟨-, Hback2⟩
      ihave Hregs := Hback2 $$ %(rT.1, max rT.2 (sint.nat lT + fsS.length)) [Hs]
      · iunfold traceutil.regionOwn
        iexists _
        iframe
        ipureintro
        exact ⟨Hr.1, hok⟩
      rw [List.set_set] at *
      imodintro
      iapply HΦ
      iexists _
      iframe
      ipureintro
      refine ⟨traceutil.regsLe_set hkT (Nat.le_max_left _ _), kT,
        (rT.1, max rT.2 (sint.nat lT + fsS.length)), ?_, lT + lS, rfl, by word, hlen,
        by
          show sint.nat (lT + lS) ≤ max rT.2 (sint.nat lT + fsS.length)
          have h1 : sint.nat (lT + lS) = sint.nat lT + sint.nat lS := by word
          omega⟩
      rw [List.getElem?_set_self (List.getElem?_eq_some_iff.1 hkT).1]
  · iapply wp_slice_append_grow _ _ _ ⟨by rw [hTl]; exact hT0, by rw [hSl]; exact hS0⟩
      (by rw [hTl, hSl, hTc]; omega)
    iintro %nsl %Hov Hnew Hncap
    rw [hTl, hSl] at *
    ihave %Hnl := ownSlice_len _ _ _ $$ Hnew
    simp only [List.length_replicate] at Hnl
    icases traceutil.region_read regs _ ⟨kT, rT, hkT, lT, rfl, hT0, hT1, hTm⟩ $$ Hregs
      with ⟨%fsT, HT, %HwfT, HbT⟩
    ihave %HlT := ownSlice_len _ _ _ $$ HT
    wp_apply +noauto wp_slice_copy nsl _ _ fsT (DFrac.own 1) $$ [Hnew HT] with %n' ⟨%Hn', Hnew, HT⟩
    · iframe
    isplitl []
    · ipureintro; exact isPanic_intoVal _
    ihave Hregs := HbT $$ HT
    icases (ownSlice_slice lT (lT + lS) nsl _ _ ⟨hT0, by word, by word⟩).1 $$ Hnew
      with ⟨Hnew1, Hnew2, -⟩
    icases traceutil.region_read regs _ ⟨kS, rS, hkS, lS, rfl, hS0, hS1, hSm⟩ $$ Hregs
      with ⟨%fsS, HS, %HwfS, HbS⟩
    ihave %HlS := ownSlice_len _ _ _ $$ HS
    wp_apply +noauto wp_slice_copy _ _ _ fsS (DFrac.own 1) $$ [Hnew2 HS] with %n'' ⟨%Hn'', Hnew2, HS⟩
    · iframe
    ihave Hregs := HbS $$ HS
    have hfT : fsT.length = sint.nat lT := by rw [HlT.1]; simp [slice.slice]
    have hfS : fsS.length = sint.nat lS := by rw [HlS.1]; simp [slice.slice]
    have hN : sint.nat (lT + lS) = fsT.length + fsS.length := by rw [hfT, hfS]; word
    have ha : (fsT.take (List.replicate (sint.nat (lT + lS)) (zero_val traceutil.Field)).length ++
        (List.replicate (sint.nat (lT + lS)) (zero_val traceutil.Field)).drop fsT.length).take
          (sint.nat lT) = fsT := by
      rw [List.length_replicate, List.take_of_length_le (l := fsT) (i := sint.nat (lT + lS)) (by omega),
        show sint.nat lT = fsT.length from hfT.symm, List.take_left]
    have hb : (subslice (sint.nat lT) (sint.nat (lT + lS))
        (fsT.take (List.replicate (sint.nat (lT + lS)) (zero_val traceutil.Field)).length ++
          (List.replicate (sint.nat (lT + lS)) (zero_val traceutil.Field)).drop fsT.length)).length =
        fsS.length := by
      simp only [subslice, List.length_drop, List.length_take, List.length_append,
        List.length_replicate]
      omega
    rw [ha, hb, List.take_length, List.drop_of_length_le (i := fsS.length) (by omega),
      List.append_nil]
    have hnl : nsl.len = lT + lS := by word
    have hs : slice.slice nsl traceutil.Field (W64 0) (lT + lS) = nsl := by
      rw [← hnl]; exact (slice_slice_trivial nsl).symm
    ihave H := ownSlice_combine lT nsl _ fsT fsS (W64 0) (lT + lS)
      ⟨by rw [hfT]; rfl, by decide, hT0, by word⟩ $$ Hnew1 Hnew2
    rw [hs]
    isplitl []
    · ipureintro; exact isPanic_intoVal _
    icases traceutil.region_of_owned nsl (fsT ++ fsS) (traceutil.fieldsWf_append HwfT HwfS)
      $$ [H Hncap] with ⟨Hr, %Hin⟩
    · iframe
    imodintro
    iapply HΦ
    iexists _
    isplitl
    · iapply BigSepL.bigSepL_snoc.2
      iframe
    ipureintro
    exact ⟨traceutil.regsLe_snoc _ _, regs.length, _, by simp, Hin⟩

end regions

end EtcdGrove
end Perennial
