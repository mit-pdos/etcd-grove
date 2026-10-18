/-
The lessor's proofs' lemmas (2026-10-13, unit 8). Lean-first (no Rocq counterpart).

A `LeaseItem` is a safe map key (comparing it with itself does not panic: a struct of a
string).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.InvLessor
public import Perennial.Proof.time
public import Proof.Lib.Heap

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lease

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

instance leaseItem_safeMapKey (k : LeaseItem) : SafeMapKey (GF := GF) LeaseItem.ty k where
  wp_go_eq_safe_map_key s E Φ := by
    iintro HΦ
    wp_pures
    iapply HΦ

/-- `(*Time).Before` on a fractional points-to (2026-10-13, unit 9: the queue's `Less` reads the
items' times at the lock's share; Perennial's `Time.wp_ptr_Before` takes the whole). -/
theorem Time.wp_ptr_Before_dq (l : Loc) (t u : _root_.Perennial.time.Time) (dq : DFrac) :
    {{ (l ↦{dq} t : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType _root_.Perennial.time.Time.ty @!! go!"Before"))
        (Val #u))
    {{ (b : Bool), RET #b; l ↦{dq} t }} := by
  wp_start as Hl
  wp_auto
  wp_apply _root_.Perennial.time.Time.wp_Before as %b -
  iapply HΦ $$ Hl

/-- Two halves of a points-to agree and make the whole. -/
theorem ptsto_halves_combine {V : Type} [TypedPointsto (GF := GF) V] (l : Loc) (v w : V) :
    typedPointsto (GF := GF) l v (DFrac.own (1 : Qp).half) ∗
      typedPointsto (GF := GF) l w (DFrac.own (1 : Qp).half) ⊢
      ⌜v = w⌝ ∗ typedPointsto (GF := GF) l v (DFrac.own 1) := by
  iintro ⟨H1, H2⟩
  icombine H1 H2 gives %Heq
  subst Heq
  isplitr
  · ipureintro; rfl
  rw [dfrac_own_half_half 1]
  iapply ((typedPointsto_dfractional (GF := GF) l v).dfractional _ _).2
  iframe

/-- A points-to in two halves. -/
theorem ptsto_halves_split {V : Type} [TypedPointsto (GF := GF) V] (l : Loc) (v : V) :
    typedPointsto (GF := GF) l v (DFrac.own 1) ⊢
      typedPointsto (GF := GF) l v (DFrac.own (1 : Qp).half) ∗
        typedPointsto (GF := GF) l v (DFrac.own (1 : Qp).half) := by
  iintro H
  rw [dfrac_own_half_half 1]
  iapply ((typedPointsto_dfractional (GF := GF) l v).dfractional _ _).1 $$ H

instance unit_intoValInj : go.IntoValInj Unit where
  intoVal_inj x y _ := by cases x; cases y; rfl

/-- What a lease's `mu` guards is fractional. -/
instance leaseItems_fractional (l : Loc) : Fractional (leaseItems (GF := GF) l) where
  fractional q1 q2 := by
    unfold leaseItems
    constructor
    · iintro ⟨%sm, %S, Hsm, HS⟩
      icases (ptsto_frac_add _ _ q1 q2).1 $$ Hsm with ⟨Hs1, Hs2⟩
      icases ((ownMap_fractional (GF := GF) sm S).fractional q1 q2).1 $$ HS with ⟨HS1, HS2⟩
      isplitl [Hs1 HS1]
      · iexists sm, S; iframe
      · iexists sm, S; iframe
    · iintro ⟨⟨%sm1, %S1, Hsm1, HS1⟩, ⟨%sm2, %S2, Hsm2, HS2⟩⟩
      icombine Hsm1 Hsm2 gives %Hsm
      subst Hsm
      ihave %HS := ownMap_agree sm1 _ _ S1 S2 $$ [$HS1 $HS2]
      subst HS
      iexists sm1, S1
      isplitl [Hsm1 Hsm2]
      · iapply (ptsto_frac_add _ _ q1 q2).2; iframe
      · iapply ((ownMap_fractional (GF := GF) sm1 S1).fractional q1 q2).2; iframe

/-- What a lease's `expiryMu` guards is fractional. -/
instance leaseExpiry_fractional (l : Loc) : Fractional (leaseExpiry (GF := GF) l) where
  fractional q1 q2 := by
    unfold leaseExpiry
    rw [qp_half_add]
    constructor
    · iintro ⟨%e, He⟩
      icases (ptsto_frac_add _ _ _ _).1 $$ He with ⟨H1, H2⟩
      isplitl [H1]
      · iexists e; iframe
      · iexists e; iframe
    · iintro ⟨⟨%e1, H1⟩, ⟨%e2, H2⟩⟩
      icombine H1 H2 gives %He
      subst He
      iexists e1
      iapply (ptsto_frac_add _ _ _ _).2; iframe

theorem lessorGhost_insert (lp : Loc) (γga : GName) (L L' : List w64) :
    (lessorGhost lp γga L).insert true (Sum.inr L' : LessorGV) = lessorGhost lp γga L' := by
  apply GMap.ext
  intro k
  unfold lessorGhost
  cases k <;> simp [GMap.lookup_insert_eq_iff]

/-- **The live set grows by a lease that may be granted** (`leaseGranted`, D19n), with both
halves (the lessor's under `le.mu`, the owner's). -/
theorem lessor_live_grant (γl : GName) (lp : Loc) (L : List w64) (id : w64) :
    lessorAuth (GF := GF) γl 1 lp L ∗ leaseFrag γl (1 : Qp).half L ∗
      leaseFrag γl (1 : Qp).half L ∗ leaseGranted γl id ==∗
      lessorAuth γl 1 lp (L ++ [id]) ∗ leaseFrag γl (1 : Qp).half (L ++ [id]) ∗
        leaseFrag γl (1 : Qp).half (L ++ [id]) := by
  unfold lessorAuth leaseFrag
  iintro ⟨⟨%γga, Ha, #Hgr⟩, H1, H2, #Hid⟩
  ihave #Hl : iprop([∗list] x ∈ L ++ [id], leaseGranted (GF := GF) γl x) $$ []
  · iapply BigSepL.bigSepL_snoc.2
    iframe Hgr Hid
  icases ghostMapElem_combine true γl _ _ _ _ $$ H1 H2 with ⟨H, -⟩
  ihave H : ghostMapElem (GF := GF) γl true (DFrac.own 1) (Sum.inr L : LessorGV) $$ [H]
  · rw [dfrac_own_half_half 1]; iexact H
  imod ghost_map_update (Sum.inr (L ++ [id]) : LessorGV) $$ Ha H with ⟨Ha, H⟩
  rw [lessorGhost_insert]
  isplitl [Ha]
  · iexists γga
    iframe Ha
    iframe Hl
  ihave H : ghostMapElem (GF := GF) γl true (DFrac.own ((1 : Qp).half + (1 : Qp).half))
      (Sum.inr (L ++ [id]) : LessorGV) $$ [H]
  · rw [Qp.half_add_half]; iexact H
  iapply ((ghostMapElem_fractional (GF := GF) true γl (Sum.inr (L ++ [id]) : LessorGV)).fractional
    (1 : Qp).half (1 : Qp).half).1 $$ H

/-- Two whole points-to of one `int` field contradict. -/
theorem w64Field_excl (a : Loc) (v w : w64) :
    a ↦ v ∗ a ↦ w ⊢ (False : IProp GF) := by
  rw [typedPointsto_unseal]; unfold typedPointstoWrap
  iintro ⟨⟨H1, _⟩, ⟨H2, _⟩⟩
  simp only [typedPointstoDef_heap]
  icombine H1 H2 gives % ⟨Hbad, _⟩
  exfalso
  have : (1 + 1 : Rat) ≤ 1 := Hbad
  grind

/-- Setting a position whose body is `emp` does not change a big separating conjunction. -/
theorem bigSepL_set_emp {A : Type} (C : Nat → A → IProp GF) (l : List A) (i : Nat) (v : A)
    (hi : i < l.length) (hC : ∀ y, C i y = iprop(emp)) :
    ([∗list] k ↦ y ∈ l.set i v, C k y) ⊣⊢ [∗list] k ↦ y ∈ l, C k y := by
  have hv : (l.set i v)[i]? = some v := by simp [hi]
  have hl : l[i]? = some l[i] := List.getElem?_eq_getElem hi
  constructor
  · refine (BigSepL.bigSepL_lookup_acc hv).1.trans ?_
    refine sep_elim_right.trans ((forall_elim l[i]).trans ?_)
    rw [hC, List.set_set, List.set_getElem_self hi]
    exact emp_wand.1
  · refine (BigSepL.bigSepL_lookup_acc hl).1.trans ?_
    refine sep_elim_right.trans ((forall_elim v).trans ?_)
    rw [hC]
    exact emp_wand.1

/-- The swapped list's elements: `b` at `i`, `a` at `j` (`a`, `b` the elements at `i`, `j`). -/
theorem listSwap_eq {A : Type} (xs : List A) (i j : Nat) (a b : A) (ha : xs[i]? = some a)
    (hb : xs[j]? = some b) : listSwap xs i j = (xs.set i b).set j a := by
  unfold listSwap; rw [ha, hb]

theorem listSwap_length {A : Type} (xs : List A) (i j : Nat) :
    (listSwap xs i j).length = xs.length := by
  unfold listSwap
  split <;> simp

theorem listSwap_map {A B : Type} (f : A → B) (xs : List A) (i j : Nat) :
    (listSwap xs i j).map f = listSwap (xs.map f) i j := by
  unfold listSwap
  simp only [List.getElem?_map]
  cases xs[i]? <;> cases xs[j]? <;> simp [List.map_set]

/-- Swapping two positions permutes. -/
theorem perm_swap_set {A : Type} (xs : List A) (i j : Nat) (hi : i < xs.length) (hj : j < xs.length) :
    ((xs.set i xs[j]).set j xs[i]).Perm xs := by
  classical
  refine List.perm_iff_count.2 (fun c => ?_)
  have hj' : j < (xs.set i xs[j]).length := by simpa using hj
  rw [List.count_set hj', List.count_set hi]
  have hle : ∀ k (hk : k < xs.length), (if xs[k] == c then 1 else 0) ≤ xs.count c := by
    intro k hk
    split
    · rename_i h
      have : xs[k] = c := by simpa using h
      exact List.count_pos_iff.mpr (this ▸ List.getElem_mem hk)
    · exact Nat.zero_le _
  have h1 := hle i hi
  have h2 := hle j hj
  have hg : (xs.set i xs[j])[j] = xs[j] := by
    rw [List.getElem_set]; split <;> simp_all
  rw [hg]
  revert h1 h2
  generalize (if xs[i] == c then 1 else 0) = u
  generalize (if xs[j] == c then 1 else 0) = w
  intro h1 h2
  omega

/-- `listSwap` permutes. -/
theorem listSwap_perm {A : Type} (xs : List A) (i j : Nat) : (listSwap xs i j).Perm xs := by
  unfold listSwap
  split
  · rename_i a b ha hb
    have hi : i < xs.length := (List.getElem?_eq_some_iff.mp ha).1
    have hj : j < xs.length := (List.getElem?_eq_some_iff.mp hb).1
    have hxa : xs[i] = a := (List.getElem?_eq_some_iff.mp ha).2
    have hxb : xs[j] = b := (List.getElem?_eq_some_iff.mp hb).2
    subst hxa hxb
    exact perm_swap_set xs i j hi hj
  · exact List.Perm.refl _

end lemmas

end lease
end EtcdGrove
end Perennial
