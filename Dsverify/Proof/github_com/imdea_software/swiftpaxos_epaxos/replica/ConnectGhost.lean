/-
Helpers of `ConnectToPeers` (package-internal): slices as their elements by index, and the
dialing phase's per-index cells.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.replica.WaitPeers

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs model

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem bigSepL_range_getD {PROP : Type _} [BI PROP] {A : Type _} (d : A) :
    ∀ (l : List A) (Φ : Nat → A → PROP),
      ([∗list] k ↦ x ∈ l, Φ k x) ⊣⊢ [∗list] j ∈ List.range l.length, Φ j (l.getD j d)
  | [], Φ => by simp
  | a :: t, Φ => by
    rw [List.length_cons, List.range_succ_eq_map]
    refine BigSepL.bigSepL_cons.trans ?_
    refine BiEntails.trans ?_ BigSepL.bigSepL_cons.symm
    rw [BigSepL.bigSepL_map]
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    exact sep_congr .rfl (bigSepL_range_getD d t (fun k x => Φ (k + 1) x))

/-- A choice of the existentials of a big separating conjunction over distinct indices. -/
theorem bigSepL_exists_fun {PROP : Type _} [BI PROP] {X : Type _} [Inhabited X]
    (Φ : Nat → X → PROP) :
    ∀ (l : List Nat), l.Nodup → ([∗list] j ∈ l, ∃ x, Φ j x) ⊢ ∃ f : Nat → X, [∗list] j ∈ l, Φ j (f j)
  | [], _ => by
    iintro _
    iexists (fun _ => default)
    iapply BigSepL.bigSepL_nil.2
    iempintro
  | a :: t, hl => by
    obtain ⟨ha, ht⟩ := List.nodup_cons.mp hl
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨⟨%x, Hx⟩, Ht⟩
    icases bigSepL_exists_fun Φ t ht $$ Ht with ⟨%f, Ht⟩
    iexists (fun k => if k = a then x else f k)
    iapply BigSepL.bigSepL_cons.2
    simp only [ite_true]
    iframe Hx
    iapply BigSepL.bigSepL_mono (Φ := fun _ y => Φ y (f y)) ?_ $$ Ht
    intro k y hk
    have : y ≠ a := fun h => ha (h ▸ List.mem_of_getElem? hk)
    simp only [this, ite_false]
    exact .rfl

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]

/-- A slice as its elements by index. -/
theorem ownSlice_range {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    (s : GoSlice) (vs : List V) (d : V) :
    (s ↦* vs : IProp GF) ⊢
      ([∗list] j ∈ List.range vs.length, typedPointsto (sliceIndexRef V ((j : Nat) : Int) s) (vs.getD j d)
        (DFrac.own 1)) ∗
      (∀ g : Nat → V, ([∗list] j ∈ List.range vs.length,
          typedPointsto (sliceIndexRef V ((j : Nat) : Int) s) (g j) (DFrac.own 1)) -∗
        s ↦* ((List.range vs.length).map g)) := by
  iintro Hs
  icases ownSlice_elems s vs $$ Hs with ⟨He, Hback⟩
  unfold sliceElems
  isplitl [He]
  · iapply (bigSepL_range_getD d vs _).1 $$ He
  iintro %g Hg
  iapply Hback
  · ipureintro; simp
  iapply (bigSepL_range_getD d _ _).2
  simp only [List.length_map, List.length_range]
  iapply BigSepL.bigSepL_mono ?_ $$ Hg
  intro k y hk
  have hy : y = k := by
    obtain ⟨_, h2⟩ := List.getElem?_eq_some_iff.mp hk
    simp only [List.getElem_range] at h2; exact h2.symm
  subst hy
  have hlt : y < vs.length := (List.getElem?_eq_some_iff.mp hk).1 |> fun h => by simpa using h
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hlt]
  exact .rfl

/-- What the reader goroutine of peer `j` starts from once dialing is done: no reader (`rd`
nil), or a connection's reader resources. -/
def readerStart (γ : EpNames) (id : Nat) (L : List GoString) (ew : GoSlice) (j : Nat) (rd : Loc) :
    IProp GF :=
  iprop(⌜rd = null⌝ ∨ ∃ (c : GoInterface) (cid : Nat) (side : Bool), lisRes γ id L ew j c cid side rd)

/-- A pending slot, once dialing is done: the slot and the reader's start. -/
theorem pend_to_slot (γ : EpNames) (id : Nat) (L : List GoString) (ew : GoSlice) (j : Nat)
    (c : GoInterface) (rd w : Loc) :
    pendSlot (GF := GF) γ id L ew j c rd w ⊢ peerSlotX γ id L ew j c w ∗ readerStart γ id L ew j rd := by
  unfold pendSlot peerSlotX readerStart
  iintro ⟨%ms, Hs, (⟨%Hw, %Hc, %Hms, Hst⟩ | ⟨%cid, %side, Hsc, Hlis⟩)⟩
  · isplitl
    · iexists ms; iframe; ileft; iframe; ipureintro; exact ⟨Hw.1, Hc, Hms⟩
    · ileft; ipureintro; exact Hw.2
  · isplitl [Hs Hsc]
    · iexists ms; iframe
    · iright; iexists c, cid, side; iframe

/-- A cell of the dialing phase at index `j` (the replica's own: no slot). -/
def cellAt (γ : EpNames) (id : Nat) (L : List GoString) (p : FwPtrs) (j : Nat) : IProp GF :=
  if j = id then
    iprop(∃ (c : GoInterface) (rd w : Loc) (a : Bool),
      typedPointsto (sliceIndexRef GoInterface (j : Int) p.peers) c (DFrac.own 1) ∗
      typedPointsto (sliceIndexRef Loc (j : Int) p.readers) rd (DFrac.own 1) ∗
      typedPointsto (sliceIndexRef Loc (j : Int) p.writers) w (DFrac.own 1) ∗
      typedPointsto (sliceIndexRef Bool (j : Int) p.alive) a (DFrac.own 1) ∗ ⌜rd = null⌝)
  else pendCells γ id L p j

/-- Dialing done: the cells back as the slices, the slots, and the readers' starts. -/
theorem cells_final (γ : EpNames) (id : Nat) (L : List GoString) (p : FwPtrs) (ls : List w64)
    (hls : ls.length = L.length) :
    ([∗list] j ∈ List.range L.length, cellAt (GF := GF) γ id L p j) -∗
    (∀ g : Nat → GoInterface, ([∗list] j ∈ List.range L.length,
        typedPointsto (sliceIndexRef GoInterface ((j : Nat) : Int) p.peers) (g j) (DFrac.own 1)) -∗
      p.peers ↦* ((List.range L.length).map g)) -∗
    (∀ g : Nat → Loc, ([∗list] j ∈ List.range L.length,
        typedPointsto (sliceIndexRef Loc ((j : Nat) : Int) p.readers) (g j) (DFrac.own 1)) -∗
      p.readers ↦* ((List.range L.length).map g)) -∗
    (∀ g : Nat → Loc, ([∗list] j ∈ List.range L.length,
        typedPointsto (sliceIndexRef Loc ((j : Nat) : Int) p.writers) (g j) (DFrac.own 1)) -∗
      p.writers ↦* ((List.range L.length).map g)) -∗
    (∀ g : Nat → Bool, ([∗list] j ∈ List.range L.length,
        typedPointsto (sliceIndexRef Bool ((j : Nat) : Int) p.alive) (g j) (DFrac.own 1)) -∗
      p.alive ↦* ((List.range L.length).map g)) -∗
    p.lat ↦* ls -∗
    fwPeers γ id L p.peers p.writers p.alive p.lat p.ewma ∗
      ∃ rs : List Loc, p.readers ↦* rs ∗ ⌜rs.length = L.length⌝ ∗
        [∗list] j ∈ List.range L.length,
          if j = id then iprop(⌜rs.getD j null = null⌝) else readerStart γ id L p.ewma j (rs.getD j null) := by
  iintro Hcells Wp Wr Ww Wa Hls
  ihave Hc : [∗list] j ∈ List.range L.length, ∃ x : GoInterface × Loc × Loc × Bool,
      typedPointsto (sliceIndexRef GoInterface ((j : Nat) : Int) p.peers) x.1 (DFrac.own 1) ∗
      typedPointsto (sliceIndexRef Loc ((j : Nat) : Int) p.readers) x.2.1 (DFrac.own 1) ∗
      typedPointsto (sliceIndexRef Loc ((j : Nat) : Int) p.writers) x.2.2.1 (DFrac.own 1) ∗
      typedPointsto (sliceIndexRef Bool ((j : Nat) : Int) p.alive) x.2.2.2 (DFrac.own 1) ∗
      (if j = id then iprop(⌜x.2.1 = null⌝) else pendSlot γ id L p.ewma j x.1 x.2.1 x.2.2.1) $$ [Hcells]
  · iapply BigSepL.bigSepL_mono ?_ $$ Hcells
    intro k y _
    unfold cellAt
    by_cases hy : y = id
    · simp only [hy, ite_true]
      iintro ⟨%c, %rd, %w, %a, H1, H2, H3, H4, %H5⟩
      iexists (c, rd, w, a); iframe; ipureintro; exact H5
    · simp only [hy, ite_false]
      unfold pendCells
      iintro ⟨%c, %rd, %w, %a, H1, H2, H3, H4, H5⟩
      iexists (c, rd, w, a); iframe
  icases bigSepL_exists_fun _ _ List.nodup_range $$ Hc with ⟨%f, Hc⟩
  icases (BigSepL.bigSepL_sep_eqv).1 $$ Hc with ⟨Hp, Hc⟩
  icases (BigSepL.bigSepL_sep_eqv).1 $$ Hc with ⟨Hr, Hc⟩
  icases (BigSepL.bigSepL_sep_eqv).1 $$ Hc with ⟨Hw, Hc⟩
  icases (BigSepL.bigSepL_sep_eqv).1 $$ Hc with ⟨Ha, Hc⟩
  ihave Hp := Wp $$ %(fun j => (f j).1) Hp
  ihave Hr := Wr $$ %(fun j => (f j).2.1) Hr
  ihave Hw := Ww $$ %(fun j => (f j).2.2.1) Hw
  ihave Ha := Wa $$ %(fun j => (f j).2.2.2) Ha
  have hg : ∀ {B : Type} (g : Nat → B) (d : B) (j : Nat), j < L.length →
      ((List.range L.length).map g).getD j d = g j := by
    intro B g d j hj
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]; rfl
  ihave Hc : ([∗list] j ∈ List.range L.length, if j = id then iprop(True) else
        peerSlotX γ id L p.ewma j (((List.range L.length).map (fun j => (f j).1)).getD j interface.nil)
          (((List.range L.length).map (fun j => (f j).2.2.1)).getD j null)) ∗
      ([∗list] j ∈ List.range L.length,
        if j = id then iprop(⌜((List.range L.length).map (fun j => (f j).2.1)).getD j null = null⌝)
        else readerStart γ id L p.ewma j (((List.range L.length).map (fun j => (f j).2.1)).getD j null))
      $$ [Hc]
  · iapply (BigSepL.bigSepL_sep_eqv).1
    iapply BigSepL.bigSepL_mono ?_ $$ Hc
    intro k y hk
    have hy : y < L.length := by
      have := List.mem_of_getElem? hk; simpa using this
    rw [hg _ _ _ hy, hg _ _ _ hy, hg _ _ _ hy]
    by_cases hyi : y = id
    · simp only [hyi, ite_true]
      iintro %H; isplitr; · itrivial
      ipureintro; exact H
    · simp only [hyi, ite_false]
      iintro H
      iapply pend_to_slot $$ H
  icases Hc with ⟨Hs, Hrs⟩
  isplitl [Hp Hw Ha Hls Hs]
  · unfold fwPeers
    iexists _, _, _, ls
    iframe
    ipureintro; simp [hls]
  iexists _
  iframe
  ipureintro; simp

/-- Split a big separating conjunction over the ids by their order with `id`. -/
theorem bigSepL_split3 (id n : Nat) (Φ : Nat → IProp GF) :
    ([∗list] j ∈ List.range n, Φ j) ⊣⊢
      ([∗list] j ∈ List.range n, if j < id then Φ j else iprop(True)) ∗
      ([∗list] j ∈ List.range n, if id < j then Φ j else iprop(True)) ∗
      ([∗list] j ∈ List.range n, if j = id then Φ j else iprop(True)) := by
  have h : ∀ j, Φ j ⊣⊢ iprop((if j < id then Φ j else iprop(True)) ∗
      (if id < j then Φ j else iprop(True)) ∗ (if j = id then Φ j else iprop(True))) := by
    intro j
    rcases Nat.lt_trichotomy j id with h | h | h
    · simp only [h, ite_true, show ¬ id < j by omega, ite_false, show j ≠ id by omega]
      exact ⟨by iintro H; iframe; isplitl <;> itrivial,
        by iintro ⟨H, -, -⟩; iexact H⟩
    · subst h
      simp only [Nat.lt_irrefl, ite_false, ite_true]
      exact ⟨by iintro H; iframe, by iintro ⟨-, -, H⟩; iexact H⟩
    · simp only [show ¬ j < id by omega, ite_false, h, ite_true, show j ≠ id by omega]
      exact ⟨by iintro H; iframe, by iintro ⟨-, H, -⟩; iexact H⟩
  refine BiEntails.trans ?_ (BiEntails.trans BigSepL.bigSepL_sep_eqv
    (sep_congr .rfl BigSepL.bigSepL_sep_eqv))
  exact ⟨BigSepL.bigSepL_mono_of_forall (fun {_ x} => (h x).1),
    BigSepL.bigSepL_mono_of_forall (fun {_ x} => (h x).2)⟩

/-- The dialing phase's cells, from the fresh slices and the framework's start halves. -/
theorem cells_init (γ : EpNames) (id : Nat) (L : List GoString) (p : FwPtrs)
    (hL : L.length = nRep) :
    p.peers ↦* List.replicate L.length (interface.nil : GoInterface) -∗
    p.readers ↦* List.replicate L.length (null : Loc) -∗
    p.writers ↦* List.replicate L.length (null : Loc) -∗
    p.alive ↦* List.replicate L.length false -∗
    p.ewma ↦* List.replicate L.length (W64 0) -∗
    ([∗list] j ∈ List.range nRep,
      if j = id then iprop(True) else iprop(sentHalf (GF := GF) γ id j [] ∗ delivFrom γ id j 0)) -∗
    ([∗list] j ∈ List.range L.length, cellAt γ id L p j) ∗
    ⌜sint.Z p.peers.len = L.length ∧ sint.Z p.readers.len = L.length ∧
      sint.Z p.writers.len = L.length ∧ sint.Z p.alive.len = L.length ∧
      sint.Z p.ewma.len = L.length⌝ ∗
    (∀ g : Nat → GoInterface, ([∗list] j ∈ List.range L.length,
        typedPointsto (sliceIndexRef GoInterface ((j : Nat) : Int) p.peers) (g j) (DFrac.own 1)) -∗
      p.peers ↦* ((List.range L.length).map g)) ∗
    (∀ g : Nat → Loc, ([∗list] j ∈ List.range L.length,
        typedPointsto (sliceIndexRef Loc ((j : Nat) : Int) p.readers) (g j) (DFrac.own 1)) -∗
      p.readers ↦* ((List.range L.length).map g)) ∗
    (∀ g : Nat → Loc, ([∗list] j ∈ List.range L.length,
        typedPointsto (sliceIndexRef Loc ((j : Nat) : Int) p.writers) (g j) (DFrac.own 1)) -∗
      p.writers ↦* ((List.range L.length).map g)) ∗
    (∀ g : Nat → Bool, ([∗list] j ∈ List.range L.length,
        typedPointsto (sliceIndexRef Bool ((j : Nat) : Int) p.alive) (g j) (DFrac.own 1)) -∗
      p.alive ↦* ((List.range L.length).map g)) := by
  iintro Hp Hr Hw Ha He Hh
  ihave %Lp := ownSlice_len _ _ _ $$ Hp
  ihave %Lr := ownSlice_len _ _ _ $$ Hr
  ihave %Lw := ownSlice_len _ _ _ $$ Hw
  ihave %La := ownSlice_len _ _ _ $$ Ha
  ihave %Le := ownSlice_len _ _ _ $$ He
  simp only [List.length_replicate] at Lp Lr Lw La Le
  icases ownSlice_range _ _ interface.nil $$ Hp with ⟨Hp, Wp⟩
  icases ownSlice_range _ _ null $$ Hr with ⟨Hr, Wr⟩
  icases ownSlice_range _ _ null $$ Hw with ⟨Hw, Ww⟩
  icases ownSlice_range _ _ false $$ Ha with ⟨Ha, Wa⟩
  icases ownSlice_range _ _ (W64 0) $$ He with ⟨He, -⟩
  simp only [List.length_replicate]
  iframe Wp Wr Ww Wa
  isplitl [Hp Hr Hw Ha He Hh]
  rotate_left
  · ipureintro
    obtain ⟨Lp1, Lp2⟩ := Lp; obtain ⟨Lr1, Lr2⟩ := Lr; obtain ⟨Lw1, Lw2⟩ := Lw
    obtain ⟨La1, La2⟩ := La; obtain ⟨Le1, Le2⟩ := Le
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [Lp1]; have := Lp2; unfold sint.nat at *; unfold sint.Z at *; omega
    · rw [Lr1]; have := Lr2; unfold sint.nat at *; unfold sint.Z at *; omega
    · rw [Lw1]; have := Lw2; unfold sint.nat at *; unfold sint.Z at *; omega
    · rw [La1]; have := La2; unfold sint.nat at *; unfold sint.Z at *; omega
    · rw [Le1]; have := Le2; unfold sint.nat at *; unfold sint.Z at *; omega
  rw [← hL]
  ihave H := (BigSepL.bigSepL_sep_eqv).2 $$ [Hp Hr]
  · iframe
  ihave H := (BigSepL.bigSepL_sep_eqv).2 $$ [H Hw]
  · iframe
  ihave H := (BigSepL.bigSepL_sep_eqv).2 $$ [H Ha]
  · iframe
  ihave H := (BigSepL.bigSepL_sep_eqv).2 $$ [H He]
  · iframe
  ihave H := (BigSepL.bigSepL_sep_eqv).2 $$ [H Hh]
  · iframe
  iapply BigSepL.bigSepL_mono ?_ $$ H
  intro k y hk
  have hy : y < L.length := by have := List.mem_of_getElem? hk; simpa using this
  simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate, hy, if_true, Option.getD_some]
  unfold cellAt
  by_cases hyi : y = id
  · simp only [hyi, ite_true]
    iintro ⟨⟨⟨⟨⟨H1, H2⟩, H3⟩, H4⟩, -⟩, -⟩
    iexists _, _, _, _
    iframe
    ipureintro; rfl
  · simp only [hyi, ite_false]
    iintro ⟨⟨⟨⟨⟨H1, H2⟩, H3⟩, H4⟩, H5⟩, ⟨Hs, Hd⟩⟩
    unfold pendCells pendSlot lisStart
    iexists _, _, _, _
    iframe
    ileft
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    isplitr
    · ipureintro; intro _; rfl
    isplitr
    · ipureintro; rfl
    iframe
    ipureintro
    have := Le.2; rw [Le.1] at hy; unfold sint.nat at *; unfold sint.Z at *; omega

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
