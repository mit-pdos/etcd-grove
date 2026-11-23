/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/X/Sort.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit X: `nodeArray` (`epaxos-exec.go`) as a `sort.Interface`

`Len`, `Less` (G4's total order: `Seq`, then `Leader`, then `Slot`) and `Swap` over a slice of
instance pointers whose instances are held by the EPaxos handler's heap at a fixed state.
-/
module

public import Dsverify.Proof.gryff.X.Defs
public import Dsverify.Proof.gryff.X.Pure
public import Perennial.Proof.sort.Link

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.X

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net
open Perennial.gryff.model (RState Copy committedCopy)
open Perennial.gryff.replica (XS Node keyLt)
open Perennial.gryff.replica2 (Repl2Names)

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [π : NetProtoGS]
variable [sem : go.Semantics] [gryff_sem : src.gryff.Assumptions]

set_option goose.wp.extras true

/-- The sort key's order at state `s`. -/
def keyR (s : RState) (a b : Node) : Prop := keyLt (keyS s a) (keyS s b)

theorem keyR_swo (s : RState) : slices.StrictWeakOrder (keyR s) where
  strict_weak_order_irrefl _ := keyLt_irrefl _
  strict_weak_order_trans _ _ _ h1 h2 := keyLt_trans h1 h2
  strict_weak_order_equiv := by
    refine ⟨fun x => ⟨keyLt_irrefl _, keyLt_irrefl _⟩, fun h => ⟨h.2, h.1⟩, ?_⟩
    intro x y z ⟨h1, h2⟩ ⟨h3, h4⟩
    have e1 : keyS s x = keyS s y := Classical.byContradiction fun hne => by
      rcases keyLt_total hne with h | h
      · exact h1 h
      · exact h2 h
    have e2 : keyS s y = keyS s z := Classical.byContradiction fun hne => by
      rcases keyLt_total hne with h | h
      · exact h3 h
      · exact h4 h
    unfold keyR; rw [e1, e2]; exact ⟨keyLt_irrefl _, keyLt_irrefl _⟩

/-- The sorter's state: the slice `sl` holds the pointers of the nodes `l` (by `M`), whose
instances, at state `s`, are committed. -/
def naOwn (ρ : Repl2Names) (xs : XS) (s : RState) (M : GMap Node Loc) (sl : GoSlice)
    (l : List Node) : IProp GF :=
  iprop(∃ ptrs : List Loc, sl ↦* ptrs ∗ instsG ρ xs s M ∗
    ⌜ptrs.length = l.length ∧ (∀ (i : Nat) (n : Node), l[i]? = some n →
      ∃ p, ptrs[i]? = some p ∧ M.lookup n = some p) ∧
      ∀ n ∈ l, (committedCopy s n).isSome⌝)

theorem instsG_acc (ρ : Repl2Names) (xs : XS) (s : RState) (M : GMap Node Loc) (n : Node)
    (p : Loc) (hp : M.lookup n = some p) :
    instsG (GF := GF) ρ xs s M ⊣⊢ (∃ c, ⌜s.inst (BitVec.ofInt 32 n.1) (BitVec.ofInt 32 n.2) = some c⌝ ∗
      copyRepG ρ xs n p c) ∗ ([∗map] n' ↦ p' ∈ delete M n, ∃ c,
        ⌜s.inst (BitVec.ofInt 32 n'.1) (BitVec.ofInt 32 n'.2) = some c⌝ ∗ copyRepG ρ xs n' p' c) :=
  by unfold instsG; exact BigSepM.bigSepM_delete (show get? M n = some p from hp)

/-- Reading an instance's `Seq` (the instance space at state `s`). -/
theorem wp_load_Seq (ρ : Repl2Names) (xs : XS) (s : RState) (M : GMap Node Loc) (n : Node)
    (p : Loc) (c : Copy) (hp : M.lookup n = some p)
    (hc : s.inst (BitVec.ofInt 32 n.1) (BitVec.ofInt 32 n.2) = some c) :
    {{ instsG (GF := GF) ρ xs s M }}
      (App (Val (GoInstruction (GoLoad go.int32)))
        (Val #(p.[src.gryff.Instance, go!"Seq"])))
    {{ RET #(c.seq); instsG ρ xs s M }} := by
  wp_start as H
  icases (instsG_acc ρ xs s M n p hp).1 $$ H with ⟨⟨%c', %hc', Hc⟩, Hrest⟩
  rw [hc] at hc'; cases hc'
  icases (copyRepG_open ..).1 $$ Hc with ⟨%iv, Hp, Hcm, Hlb, %Hf⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hp with ⟨Hp, %Hnn⟩
  iStructNamed Hp
  wp_apply IntoValTyped.wp_load (t := go.int32) _ _ _ $$ Seq as Seq
  ihave Hp : p ↦ iv $$ [-HΦ Hrest Hcm Hlb]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iFrameNamed
  rw [Hf.2.2.1]
  iapply HΦ
  iapply (instsG_acc ρ xs s M n p hp).2
  iframe Hrest
  iexists c
  isplitr; · ipureintro; exact hc
  iapply (copyRepG_open ..).2
  iexists iv; iframe; ipureintro; exact Hf

/-- Reading an instance's `Leader` (the instance space at state `s`). -/
theorem wp_load_Leader (ρ : Repl2Names) (xs : XS) (s : RState) (M : GMap Node Loc) (n : Node)
    (p : Loc) (c : Copy) (hp : M.lookup n = some p)
    (hc : s.inst (BitVec.ofInt 32 n.1) (BitVec.ofInt 32 n.2) = some c) :
    {{ instsG (GF := GF) ρ xs s M }}
      (App (Val (GoInstruction (GoLoad go.int32)))
        (Val #(p.[src.gryff.Instance, go!"Leader"])))
    {{ RET #(W32 n.1); instsG ρ xs s M }} := by
  wp_start as H
  icases (instsG_acc ρ xs s M n p hp).1 $$ H with ⟨⟨%c', %hc', Hc⟩, Hrest⟩
  rw [hc] at hc'; cases hc'
  icases (copyRepG_open ..).1 $$ Hc with ⟨%iv, Hp, Hcm, Hlb, %Hf⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hp with ⟨Hp, %Hnn⟩
  iStructNamed Hp
  wp_apply IntoValTyped.wp_load (t := go.int32) _ _ _ $$ Leader as Leader
  ihave Hp : p ↦ iv $$ [-HΦ Hrest Hcm Hlb]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iFrameNamed
  have := Hf.2.2.2.2.2.2.2.2.1; rw [show iv.Leader' = W32 n.1 by apply BitVec.eq_of_toInt_eq; rw [← this]; word]
  iapply HΦ
  iapply (instsG_acc ρ xs s M n p hp).2
  iframe Hrest
  iexists c
  isplitr; · ipureintro; exact hc
  iapply (copyRepG_open ..).2
  iexists iv; iframe; ipureintro; exact Hf

/-- Reading an instance's `Slot` (the instance space at state `s`). -/
theorem wp_load_Slot (ρ : Repl2Names) (xs : XS) (s : RState) (M : GMap Node Loc) (n : Node)
    (p : Loc) (c : Copy) (hp : M.lookup n = some p)
    (hc : s.inst (BitVec.ofInt 32 n.1) (BitVec.ofInt 32 n.2) = some c) :
    {{ instsG (GF := GF) ρ xs s M }}
      (App (Val (GoInstruction (GoLoad go.int32)))
        (Val #(p.[src.gryff.Instance, go!"Slot"])))
    {{ RET #(W32 n.2); instsG ρ xs s M }} := by
  wp_start as H
  icases (instsG_acc ρ xs s M n p hp).1 $$ H with ⟨⟨%c', %hc', Hc⟩, Hrest⟩
  rw [hc] at hc'; cases hc'
  icases (copyRepG_open ..).1 $$ Hc with ⟨%iv, Hp, Hcm, Hlb, %Hf⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hp with ⟨Hp, %Hnn⟩
  iStructNamed Hp
  wp_apply IntoValTyped.wp_load (t := go.int32) _ _ _ $$ Slot as Slot
  ihave Hp : p ↦ iv $$ [-HΦ Hrest Hcm Hlb]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iFrameNamed
  have := Hf.2.2.2.2.2.2.2.2.2.1; rw [show iv.Slot' = W32 n.2 by apply BitVec.eq_of_toInt_eq; rw [← this]; word]
  iapply HΦ
  iapply (instsG_acc ρ xs s M n p hp).2
  iframe Hrest
  iexists c
  isplitr; · ipureintro; exact hc
  iapply (copyRepG_open ..).2
  iexists iv; iframe; ipureintro; exact Hf

theorem naOwn_open (ρ : Repl2Names) (xs : XS) (s : RState) (M : GMap Node Loc) (sl : GoSlice)
    (l : List Node) :
    naOwn (GF := GF) ρ xs s M sl l ⊣⊢ ∃ ptrs : List Loc, sl ↦* ptrs ∗ instsG ρ xs s M ∗
      ⌜ptrs.length = l.length ∧ (∀ (i : Nat) (n : Node), l[i]? = some n →
        ∃ p, ptrs[i]? = some p ∧ M.lookup n = some p) ∧
        ∀ n ∈ l, (committedCopy s n).isSome⌝ := .rfl

theorem wp_nodeArray_Len (ρ : Repl2Names) (xs : XS) (s : RState) (M : GMap Node Loc)
    (sl : GoSlice) (l : List Node) :
    {{ naOwn (GF := GF) ρ xs s M sl l }}
      (App (Val #(methods src.gryff.nodeArray.ty go!"Len" #sl)) (Val #()))
    {{ RET #(W64 l.length); naOwn ρ xs s M sl l }} := by
  wp_start as H
  icases (naOwn_open ..).1 $$ H with ⟨%ptrs, Hs, Hi, %Hf⟩
  ihave %Hl := ownSlice_len _ _ _ $$ Hs
  try wp_auto
  have : sl.len = W64 l.length := by
    have := Hl.1; rw [Hf.1] at this; word
  rw [this]
  iapply HΦ
  iapply (naOwn_open ..).2
  iexists ptrs; iframe; ipureintro; exact Hf

theorem wp_nodeArray_Less (ρ : Repl2Names) (xs : XS) (s : RState) (M : GMap Node Loc)
    (sl : GoSlice) (l : List Node) (i j : w64) (a b : Node) (hi : 0 ≤ sint.Z i) (hj : 0 ≤ sint.Z j)
    (ha : l[sint.nat i]? = some a) (hb : l[sint.nat j]? = some b) :
    {{ naOwn (GF := GF) ρ xs s M sl l }}
      (App (App (Val #(methods src.gryff.nodeArray.ty go!"Less" #sl)) (Val #i)) (Val #j))
    {{ (r : Bool), RET #r; naOwn ρ xs s M sl l ∗ ⌜r = true ↔ keyR s a b⌝ }} := by
  wp_start as H
  icases (naOwn_open ..).1 $$ H with ⟨%ptrs, Hs, Hi, %Hf⟩
  ihave %Hl := ownSlice_len _ _ _ $$ Hs
  obtain ⟨pa, hpa, hMa⟩ := Hf.2.1 _ a ha
  obtain ⟨pb, hpb, hMb⟩ := Hf.2.1 _ b hb
  have hil : sint.Z i < sint.Z sl.len := by
    have h1 := (List.getElem?_eq_some_iff.1 ha).1; have h2 := Hl.1; have h3 := Hf.1
    simp only [sint.nat, sint.Z] at *; omega
  have hjl : sint.Z j < sint.Z sl.len := by
    have h1 := (List.getElem?_eq_some_iff.1 hb).1; have h2 := Hl.1; have h3 := Hf.1
    simp only [sint.nat, sint.Z] at *; omega
  try wp_auto
  obtain ⟨ca, hca⟩ := Option.isSome_iff_exists.1 (Hf.2.2 a (List.mem_of_getElem? ha))
  obtain ⟨cb, hcb⟩ := Option.isSome_iff_exists.1 (Hf.2.2 b (List.mem_of_getElem? hb))
  have hia := (committedCopy_inst hca).1
  have hib := (committedCopy_inst hcb).1
  have hba := committedCopy_box (show (committedCopy s a).isSome by rw [hca]; rfl)
  have hbb := committedCopy_box (show (committedCopy s b).isSome by rw [hcb]; rfl)
  rw [keyR, keyS_of hca, keyS_of hcb]
  have ha1 : sint.Z (W32 a.1) = a.1 := by obtain ⟨h0, h1, -, -⟩ := hba; word
  have ha2 : sint.Z (W32 a.2) = a.2 := by obtain ⟨-, -, h0, h1⟩ := hba; word
  have hb1 : sint.Z (W32 b.1) = b.1 := by obtain ⟨h0, h1, -, -⟩ := hbb; word
  have hb2 : sint.Z (W32 b.2) = b.2 := by obtain ⟨-, -, h0, h1⟩ := hbb; word
  rw [ite_eq_left (show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len from ⟨hi, hil⟩)]
  wp_apply wp_load_slice_index (t := go.GoType.PointerType src.gryff.Instance.ty) sl (sint.Z i)
    ptrs _ pa hi $$ [$Hs] as Hs
  · ipureintro; exact hpa
  wp_apply wp_load_Seq ρ xs s M a pa ca hMa hia $$ [$Hi] as Hi
  rw [ite_eq_left (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len from ⟨hj, hjl⟩)]
  wp_apply wp_load_slice_index (t := go.GoType.PointerType src.gryff.Instance.ty) sl (sint.Z j)
    ptrs _ pb hj $$ [$Hs] as Hs
  · ipureintro; exact hpb
  wp_apply wp_load_Seq ρ xs s M b pb cb hMb hib $$ [$Hi] as Hi
  try wp_auto
  wp_if_destruct
  · -- same `Seq`
    rw [ite_eq_left (show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len from ⟨hi, hil⟩)]
    wp_apply wp_load_slice_index (t := go.GoType.PointerType src.gryff.Instance.ty) sl (sint.Z i)
      ptrs _ pa hi $$ [$Hs] as Hs
    · ipureintro; exact hpa
    wp_apply wp_load_Leader ρ xs s M a pa ca hMa hia $$ [$Hi] as Hi
    try wp_auto
    rw [ite_eq_left (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len from ⟨hj, hjl⟩)]
    wp_apply wp_load_slice_index (t := go.GoType.PointerType src.gryff.Instance.ty) sl (sint.Z j)
      ptrs _ pb hj $$ [$Hs] as Hs
    · ipureintro; exact hpb
    wp_apply wp_load_Leader ρ xs s M b pb cb hMb hib $$ [$Hi] as Hi
    try wp_auto
    wp_if_destruct
    · -- same `Leader`
      rw [ite_eq_left (show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len from ⟨hi, hil⟩)]
      wp_apply wp_load_slice_index (t := go.GoType.PointerType src.gryff.Instance.ty) sl (sint.Z i)
        ptrs _ pa hi $$ [$Hs] as Hs
      · ipureintro; exact hpa
      wp_apply wp_load_Slot ρ xs s M a pa ca hMa hia $$ [$Hi] as Hi
      try wp_auto
      rw [ite_eq_left (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len from ⟨hj, hjl⟩)]
      wp_apply wp_load_slice_index (t := go.GoType.PointerType src.gryff.Instance.ty) sl (sint.Z j)
        ptrs _ pb hj $$ [$Hs] as Hs
      · ipureintro; exact hpb
      wp_apply wp_load_Slot ρ xs s M b pb cb hMb hib $$ [$Hi] as Hi
      try wp_auto
      iapply HΦ
      iframe
      isplitl
      · iapply (naOwn_open ..).2; iexists ptrs; iframe; ipureintro; exact Hf
      ipureintro
      rename_i hseq
      have e1 : a.1 = b.1 := by rw [← ha1, ← hb1, Hif]
      rw [ha2, hb2]; unfold keyLt; simp only [decide_eq_true_eq, hseq, true_and, Int.lt_irrefl, false_or]
      constructor <;> intro h <;> omega
    · -- different `Leader`
      rw [ite_eq_left (show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len from ⟨hi, hil⟩)]
      wp_apply wp_load_slice_index (t := go.GoType.PointerType src.gryff.Instance.ty) sl (sint.Z i)
        ptrs _ pa hi $$ [$Hs] as Hs
      · ipureintro; exact hpa
      wp_apply wp_load_Leader ρ xs s M a pa ca hMa hia $$ [$Hi] as Hi
      try wp_auto
      rw [ite_eq_left (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len from ⟨hj, hjl⟩)]
      wp_apply wp_load_slice_index (t := go.GoType.PointerType src.gryff.Instance.ty) sl (sint.Z j)
        ptrs _ pb hj $$ [$Hs] as Hs
      · ipureintro; exact hpb
      wp_apply wp_load_Leader ρ xs s M b pb cb hMb hib $$ [$Hi] as Hi
      try wp_auto
      iapply HΦ
      iframe
      isplitl
      · iapply (naOwn_open ..).2; iexists ptrs; iframe; ipureintro; exact Hf
      ipureintro
      rename_i hseq
      have e1 : a.1 ≠ b.1 := fun e => Hif (by rw [e])
      rw [ha1, hb1]; unfold keyLt; simp only [decide_eq_true_eq, hseq, true_and, Int.lt_irrefl, false_or]
      constructor <;> intro h <;> omega
  · -- different `Seq`
    rw [ite_eq_left (show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len from ⟨hi, hil⟩)]
    wp_apply wp_load_slice_index (t := go.GoType.PointerType src.gryff.Instance.ty) sl (sint.Z i)
      ptrs _ pa hi $$ [$Hs] as Hs
    · ipureintro; exact hpa
    wp_apply wp_load_Seq ρ xs s M a pa ca hMa hia $$ [$Hi] as Hi
    try wp_auto
    rw [ite_eq_left (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len from ⟨hj, hjl⟩)]
    wp_apply wp_load_slice_index (t := go.GoType.PointerType src.gryff.Instance.ty) sl (sint.Z j)
      ptrs _ pb hj $$ [$Hs] as Hs
    · ipureintro; exact hpb
    wp_apply wp_load_Seq ρ xs s M b pb cb hMb hib $$ [$Hi] as Hi
    try wp_auto
    iapply HΦ
    iframe
    isplitl
    · iapply (naOwn_open ..).2; iexists ptrs; iframe; ipureintro; exact Hf
    ipureintro
    have : sint.Z ca.seq ≠ sint.Z cb.seq := fun e => Hif (BitVec.eq_of_toInt_eq e)
    unfold keyLt; simp only [decide_eq_true_eq]; omega

theorem swap_rel {l : List Node} {ptrs : List Loc} {M : GMap Node Loc} {i j : Nat} {a b : Node}
    {pa pb : Loc} (hlen : ptrs.length = l.length)
    (hrel : ∀ (k : Nat) (n : Node), l[k]? = some n → ∃ p, ptrs[k]? = some p ∧ M.lookup n = some p)
    (ha : l[i]? = some a) (hb : l[j]? = some b) (hMa : M.lookup a = some pa)
    (hMb : M.lookup b = some pb) :
    ∀ (k : Nat) (n : Node), ((l.set i b).set j a)[k]? = some n →
      ∃ p, ((ptrs.set i pb).set j pa)[k]? = some p ∧ M.lookup n = some p := by
  intro k n hk
  have hi : i < l.length := (List.getElem?_eq_some_iff.1 ha).1
  have hj : j < l.length := (List.getElem?_eq_some_iff.1 hb).1
  simp only [List.getElem?_set] at hk ⊢
  by_cases hkj : j = k
  · subst hkj
    simp only [List.length_set, hj, hlen, ite_true, Option.some.injEq] at hk ⊢
    subst hk; exact ⟨pa, rfl, hMa⟩
  · simp only [hkj, ite_false] at hk ⊢
    by_cases hki : i = k
    · subst hki
      simp only [hi, hlen, ite_true, Option.some.injEq] at hk ⊢
      subst hk; exact ⟨pb, rfl, hMb⟩
    · simp only [hki, ite_false] at hk ⊢
      exact hrel k n hk

theorem swap_mem {l : List Node} {i j : Nat} {a b : Node} (ha : l[i]? = some a)
    (hb : l[j]? = some b) {n : Node} (hn : n ∈ (l.set i b).set j a) : n ∈ l := by
  have h1 := List.mem_or_eq_of_mem_set hn
  rcases h1 with h1 | rfl
  · rcases List.mem_or_eq_of_mem_set h1 with h2 | rfl
    · exact h2
    · exact List.mem_of_getElem? hb
  · exact List.mem_of_getElem? ha

theorem wp_nodeArray_Swap (ρ : Repl2Names) (xs : XS) (s : RState) (M : GMap Node Loc)
    (sl : GoSlice) (l : List Node) (i j : w64) (a b : Node) (hi : 0 ≤ sint.Z i) (hj : 0 ≤ sint.Z j)
    (ha : l[sint.nat i]? = some a) (hb : l[sint.nat j]? = some b) :
    {{ naOwn (GF := GF) ρ xs s M sl l }}
      (App (App (Val #(methods src.gryff.nodeArray.ty go!"Swap" #sl)) (Val #i)) (Val #j))
    {{ RET #(); naOwn ρ xs s M sl ((l.set (sint.nat i) b).set (sint.nat j) a) }} := by
  wp_start as H
  icases (naOwn_open ..).1 $$ H with ⟨%ptrs, Hs, Hi, %Hf⟩
  ihave %Hl := ownSlice_len _ _ _ $$ Hs
  obtain ⟨pa, hpa, hMa⟩ := Hf.2.1 _ a ha
  obtain ⟨pb, hpb, hMb⟩ := Hf.2.1 _ b hb
  have hil : sint.Z i < sint.Z sl.len := by
    have h1 := (List.getElem?_eq_some_iff.1 ha).1; have h2 := Hl.1; have h3 := Hf.1
    simp only [sint.nat, sint.Z] at *; omega
  have hjl : sint.Z j < sint.Z sl.len := by
    have h1 := (List.getElem?_eq_some_iff.1 hb).1; have h2 := Hl.1; have h3 := Hf.1
    simp only [sint.nat, sint.Z] at *; omega
  try wp_auto
  rw [ite_eq_left (show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len from ⟨hi, hil⟩)]
  try wp_auto
  rw [ite_eq_left (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len from ⟨hj, hjl⟩)]
  try wp_auto
  rw [ite_eq_left (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len from ⟨hj, hjl⟩)]
  wp_apply wp_load_slice_index (t := go.GoType.PointerType src.gryff.Instance.ty) sl (sint.Z j)
    ptrs _ pb hj $$ [$Hs] as Hs
  · ipureintro; exact hpb
  try wp_auto
  rw [ite_eq_left (show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len from ⟨hi, hil⟩)]
  wp_apply wp_load_slice_index (t := go.GoType.PointerType src.gryff.Instance.ty) sl (sint.Z i)
    ptrs _ pa hi $$ [$Hs] as Hs
  · ipureintro; exact hpa
  try wp_auto
  wp_apply wp_store_slice_index (t := go.GoType.PointerType src.gryff.Instance.ty) sl (sint.Z i)
    ptrs pb $$ [$Hs] as Hs
  · ipureintro
    have h1 := (List.getElem?_eq_some_iff.1 ha).1; have h3 := Hf.1
    simp only [sint.nat, sint.Z] at *; omega
  wp_apply wp_store_slice_index (t := go.GoType.PointerType src.gryff.Instance.ty) sl (sint.Z j)
    _ pa $$ [$Hs] as Hs
  · ipureintro
    have h1 := (List.getElem?_eq_some_iff.1 hb).1; have h3 := Hf.1
    simp only [sint.nat, sint.Z, List.length_set] at *; omega
  wp_end
  iapply (naOwn_open ..).2
  iexists _; iframe
  ipureintro
  refine ⟨by simp [Hf.1], swap_rel Hf.1 Hf.2.1 ha hb hMa hMb, fun n hn => Hf.2.2 n (swap_mem ha hb hn)⟩

theorem naOwn_isSorter (ρ : Repl2Names) (xs : XS) (s : RState) (M : GMap Node Loc)
    (sl : GoSlice) :
    ⊢ sort.isSorter (GF := GF) ⟨src.gryff.nodeArray.ty, #sl⟩ (naOwn ρ xs s M sl) (keyR s) := by
  iapply sort.isSorter_intro
  isplitr
  · imodintro; iintro %l
    iapply wp_nodeArray_Len
  isplitr
  · imodintro; iintro %l %i %j %a %b %h
    iapply wp_nodeArray_Less ρ xs s M sl l i j a b h.1 h.2.1 h.2.2.1 h.2.2.2
  · imodintro; iintro %l %i %j %a %b %h
    iapply wp_nodeArray_Swap ρ xs s M sl l i j a b h.1 h.2.1 h.2.2.1 h.2.2.2

/-- `sort.Sort(nodeArray(list))`. -/
theorem wp_sort_nodeArray (ρ : Repl2Names) (xs : XS) (s : RState) (M : GMap Node Loc)
    (sl : GoSlice) (l : List Node) (hlen : l.length ≤ 2 ^ 62) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗ naOwn (GF := GF) ρ xs s M sl l }}
      (App (Val (@! sort.«Sort»)) (Val #(interface.mkOk src.gryff.nodeArray.ty #sl)))
    {{ RET #(); ∃ l', naOwn ρ xs s M sl l' ∗ ⌜l.Perm l' ∧ ∀ (i j : Nat) (a b : Node),
        l'[i]? = some a → l'[j]? = some b → i < j → ¬ keyR s b a⌝ }} := by
  iintro %Φ ⟨#Hpkg, Hl⟩ HΦ
  ihave #Hsrt := naOwn_isSorter ρ xs s M sl
  wp_apply sort.wp_Sort ⟨src.gryff.nodeArray.ty, #sl⟩ (naOwn ρ xs s M sl) (keyR s) (keyR_swo s) l
    $$ [$Hpkg $Hsrt $Hl]
  · ipureintro; exact hlen
  iintro %l' H
  icases H with ⟨Hl, %Hperm, %Hsorted⟩
  iapply HΦ
  iexists l'; iframe; ipureintro; exact ⟨Hperm, Hsorted⟩

end
end Perennial.gryff.X
