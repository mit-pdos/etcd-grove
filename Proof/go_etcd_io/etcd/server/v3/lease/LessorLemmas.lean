/-
The lessor's proofs' lemmas (2026-10-13, unit 8). Lean-first (no Rocq counterpart).

A `LeaseItem` is a safe map key (comparing it with itself does not panic: a struct of a
string).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.InvLessor
public import Perennial.Proof.time
public import Perennial.Golang.Theory.Map
public import Perennial.Ghost.GhostVar
public import Perennial.Ghost.GhostMap
public import Perennial.IrisLib.BI

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
      icases (typedPointsto_frac_add _ _ q1 q2).1 $$ Hsm with ⟨Hs1, Hs2⟩
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
      · iapply (typedPointsto_frac_add _ _ q1 q2).2; iframe
      · iapply ((ownMap_fractional (GF := GF) sm1 S1).fractional q1 q2).2; iframe

/-- What a lease's `expiryMu` guards is fractional. -/
instance leaseExpiry_fractional (l : Loc) : Fractional (leaseExpiry (GF := GF) l) where
  fractional q1 q2 := by
    unfold leaseExpiry
    rw [Qp_half_add]
    constructor
    · iintro ⟨%e, He⟩
      icases (typedPointsto_frac_add _ _ _ _).1 $$ He with ⟨H1, H2⟩
      isplitl [H1]
      · iexists e; iframe
      · iexists e; iframe
    · iintro ⟨⟨%e1, H1⟩, ⟨%e2, H2⟩⟩
      icombine H1 H2 gives %He
      subst He
      iexists e1
      iapply (typedPointsto_frac_add _ _ _ _).2; iframe

theorem lessorGhost_insert (lp : Loc) (γga γcl : GName) (L L' : List w64) :
    (lessorGhost lp γga γcl L).insert true (Sum.inr L' : LessorGV) = lessorGhost lp γga γcl L' := by
  apply GMap.ext
  intro k
  unfold lessorGhost
  cases k <;> simp [GMap.lookup_insert_eq_iff]

/-- **The live set grows by a lease that may be granted** (`leaseGranted`, D19n), with both
halves (the lessor's under `le.mu`, the owner's). -/
theorem lessor_live_grant (γl : GName) (lp : Loc) (L : List w64) (M : GMap w64 Loc) (id : w64) :
    lessorAuth (GF := GF) γl 1 lp L M ∗ leaseFrag γl (1 : Qp).half L ∗
      leaseFrag γl (1 : Qp).half L ∗ leaseGranted γl id ==∗
      lessorAuth γl 1 lp (L ++ [id]) M ∗ leaseFrag γl (1 : Qp).half (L ++ [id]) ∗
        leaseFrag γl (1 : Qp).half (L ++ [id]) := by
  unfold lessorAuth leaseFrag
  iintro ⟨⟨%γga, %γcl, Ha, Hcl, #Hgr⟩, H1, H2, #Hid⟩
  ihave #Hl : iprop([∗list] x ∈ L ++ [id], leaseGranted (GF := GF) γl x) $$ []
  · iapply BigSepL.bigSepL_snoc.2
    iframe Hgr Hid
  icases ghostMapElem_combine true γl _ _ _ _ $$ H1 H2 with ⟨H, -⟩
  ihave H : ghostMapElem (GF := GF) γl true (DFrac.own 1) (Sum.inr L : LessorGV) $$ [H]
  · rw [dfrac_own_half_half 1]; iexact H
  imod ghost_map_update (Sum.inr (L ++ [id]) : LessorGV) $$ Ha H with ⟨Ha, H⟩
  rw [lessorGhost_insert]
  isplitl [Ha Hcl]
  · iexists γga, γcl
    iframe Ha Hcl
    iframe Hl
  ihave H : ghostMapElem (GF := GF) γl true (DFrac.own ((1 : Qp).half + (1 : Qp).half))
      (Sum.inr (L ++ [id]) : LessorGV) $$ [H]
  · rw [Qp.half_add_half]; iexact H
  iapply ((ghostMapElem_fractional (GF := GF) true γl (Sum.inr (L ++ [id]) : LessorGV)).fractional
    (1 : Qp).half (1 : Qp).half).1 $$ H

/-- The lessor's authority names the pin's closers' map. -/
theorem lessorAuth_pin (γl : GName) (q : Qp) (lp lp' : Loc) (L : List w64) (M : GMap w64 Loc)
    (γga γcl : GName) :
    lessorAuth (GF := GF) γl q lp L M ∗ lessorPinG γl lp' γga γcl ⊢
      ⌜lp = lp'⌝ ∗ ghostMapAuth γcl q M ∗
        (∀ M' : GMap w64 Loc, ghostMapAuth γcl q M' -∗ lessorAuth γl q lp L M') := by
  unfold lessorAuth lessorPinG
  iintro ⟨⟨%γa, %γc, Ha, Hcl, #Hgr⟩, #Hp⟩
  ihave %Hl := ghost_map_lookup $$ Ha Hp
  have hl : (lessorGhost lp γa γc L).lookup false = some (Sum.inl (lp, γa, γc)) := by
    unfold lessorGhost; simp [GMap.lookup_insert_eq_iff]
  rw [hl] at Hl
  cases Hl
  iframe Hcl
  isplitr
  · ipureintro; rfl
  iintro %M' Hcl
  iexists γga, γcl
  iframe Ha Hcl Hgr

/-- **A granted lease's closer joins the owner's** (unit T3): the closers' map gains the lease
(with the lessor's map), the owner its element and the right to close its `revokec`. -/
theorem closers_grant (γl : GName) (lp : Loc) (L : List w64) (M : GMap w64 Loc) (id : w64)
    (l : Loc) (c : GoChan) (hM : M.lookup id = none)
    (hL : ∀ x : w64, x ∈ L ↔ (M.lookup x).isSome) :
    lessorAuth (GF := GF) γl 1 lp L M ∗ leaseClosers γl L ∗ lsF go!"revokec" l ↦□ c ∗
        revokeCloser c ==∗
      lessorAuth γl 1 lp L (M.insert id l) ∗ leaseClosers γl (L ++ [id]) := by
  iintro ⟨Ha, Hcls, #Hrc, Hrcl⟩
  iunfold leaseClosers at Hcls
  icases Hcls with ⟨%lp', %γga, %γcl, %C, #Hp, %HC, Hcs⟩
  icases lessorAuth_pin γl 1 lp lp' L M γga γcl $$ [$Ha $Hp] with ⟨%Hlp, Hcl, Hback⟩
  subst Hlp
  have hnotL : id ∉ L := by
    intro h; have := (hL id).1 h; rw [hM] at this; cases this
  have hC : C.lookup id = none := by
    cases h : C.lookup id with
    | none => rfl
    | some _ => exact absurd ((HC id).2 (by rw [h]; rfl)) hnotL
  imod ghost_map_insert id l hM $$ Hcl with ⟨Hcl, He⟩
  ihave Ha := Hback $$ %(M.insert id l) Hcl
  iframe Ha
  iunfold leaseClosers
  iexists lp, γga, γcl, (C.insert id l)
  iframe Hp
  isplitr
  · ipureintro
    intro x
    rw [List.mem_append, List.mem_singleton, HC x]
    by_cases hx : id = x
    · subst hx; simp [GMap.lookup_insert_eq_iff, hC]
    · have : (C.insert id l).lookup x = C.lookup x := GMap.lookup_insert_ne C l hx
      rw [this]
      constructor
      · rintro (h | h)
        · exact h
        · exact absurd h.symm hx
      · intro h; exact Or.inl h
  iapply (BigSepM.bigSepM_insert (Φ := fun (i : w64) (x : Loc) =>
    iprop(ghostMapElem (GF := GF) γcl i (DFrac.own 1) x ∗
      ∃ c : GoChan, lsF go!"revokec" x ↦□ c ∗ revokeCloser c)) hC).2
  iframe Hcs He
  iexists c
  iframe Hrc Hrcl

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

end lemmas

end lease
end EtcdGrove
end Perennial
