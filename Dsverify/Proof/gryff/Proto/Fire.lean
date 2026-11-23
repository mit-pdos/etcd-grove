/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Proto/Fire.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Firing a client's atomic update (`opAU`) against the invariant's half of the abstract register
(U4): the step every linearization takes.
-/
module

public import Dsverify.Proof.gryff.Proto.InvDefs
public import Dsverify.Proof.gryff.Proto.InvPure

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial.gryff

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode proto dsverify_lab.harness

section
variable [GooseExts] {GF : BundledGFunctors} [AllG GF] [InvGS_gen .hasLC GF]

instance savedQ_persistent (γq : GName) (Q : w64 → w64 → RegOutput w64 → IProp GF) :
    Persistent (savedQ (GF := GF) γq Q) := by
  unfold savedQ; infer_instance

/-- Record a store lower bound (or find its copy). -/
theorem lbs_add (γ : ProtoNames) (lbs : GMap (Nat × PTag) Unit) (kt : Nat × PTag) (E : CoPset) :
    ghostMapAuth (GF := GF) γ.storeLbs 1 lbs ∗
        ([∗map] kt' ↦ _u ∈ lbs, ghostMapElem (GF := GF) γ.storeLbs kt' DFrac.discard ()) ⊢
      |={E}=> ghostMapAuth γ.storeLbs 1 (lbs.insert kt ()) ∗
        ([∗map] kt' ↦ _u ∈ lbs.insert kt (), ghostMapElem (GF := GF) γ.storeLbs kt' DFrac.discard ()) ∗
        ghostMapElem γ.storeLbs kt DFrac.discard () := by
  iintro ⟨Ha, Hm⟩
  cases h : lbs.lookup kt with
  | some u =>
    have e : lbs.insert kt () = lbs := GMap.insert_id lbs kt () (by rw [h])
    rw [e]
    ihave #He := (BigSepM.bigSepM_lookup (Φ := fun kt' (_ : Unit) =>
      ghostMapElem (GF := GF) γ.storeLbs kt' DFrac.discard ()) (show get? lbs kt = some () by
        show lbs.lookup kt = some (); rw [h])) $$ Hm
    imodintro
    iframe
    iexact He
  | none =>
    imod ghost_map_insert_persist kt () h $$ Ha with ⟨Ha, #He⟩
    imodintro
    iframe Ha He
    iapply (BigSepM.bigSepM_insert (show get? lbs kt = none from h)).2
    iframe
    iexact He

/-- The clients' namespace is outside Gryff's invariant's. -/
theorem clientN_sub_diff (E : CoPset) (hE : ↑clientN ⊆ E) :
    (↑clientN : CoPset) ⊆ E \ ↑gryffN := by
  have hd : clientN ## gryffN := ndot_ne_disjoint nroot (by decide)
  intro p hp
  rw [Iris.Std.mem_diff]
  exact ⟨hE p hp, fun h => hd p ⟨hp, h⟩⟩

/-- Fire `opAU γ i Q` at the abstract register `σ` (the invariant's half): the register becomes
the step's state, and the commit's postcondition is produced. -/
theorem opAU_fire (γ : ProtoNames) (i : RegInput w64) (Q : w64 → w64 → RegOutput w64 → IProp GF)
    (σ : w64) (E : CoPset) (hE : ↑clientN ⊆ E) :
    opAU γ i Q ∗ ghostVar γ.reg (1 : Qp).half σ ⊢
      |={E}=> ghostVar γ.reg (1 : Qp).half (casApply σ i).1 ∗ Q σ (casApply σ i).1 (casApply σ i).2 := by
  unfold opAU regHalf
  iintro ⟨HAU, Hreg⟩
  ihave HAU := atomic_update_mask_weaken hE $$ HAU
  imod HAU with ⟨%σ0, Hα, Hclose⟩
  rcases σ0 with ⟨σ0, ⟨⟩⟩
  dsimp only [Tele.lam, Tele.app, Tele.bind, BI.tforall_cons, BI.tforall_nil, BIBase.wandM]
  ihave %e := ghostVar_agree γ.reg σ0 _ σ _ $$ Hα Hreg
  subst e
  imod ghostVar_update_halves (casApply σ0 i).1 γ.reg σ0 σ0 $$ Hα Hreg with ⟨Hα, Hreg⟩
  icases Hclose with ⟨-, Hc⟩
  imod Hc $$ %(casApply σ0 i).1 %(casApply σ0 i).2 [Hα] with HQ
  · iframe Hα
    ipureintro
    exact (casRegister_step_iff _ _ _ _ _).2 rfl
  imodintro
  iframe

/-- An operation's resources stay valid as `lin` grows, unless `lin` gains it. -/
theorem opRes_lin_grow (γ : ProtoNames) (lin lin' : List (OpId × RegOutput w64)) (id : OpId)
    (m : OpMeta) (hsub : ∀ x ∈ lin, x ∈ lin') (hback : ∀ o, (id, o) ∈ lin' → (id, o) ∈ lin) :
    opRes (GF := GF) γ lin id m ⊢ opRes γ lin' id m := by
  unfold opRes
  iintro (⟨%hn, HQ⟩ | ⟨%o, %Q, %σ, %σ', %ho, HQ, HR⟩)
  · ileft
    isplitr
    · ipureintro; exact fun o ho => hn o (hback o ho)
    · iexact HQ
  · iright
    iexists o, Q, σ, σ'
    isplitr
    · ipureintro; exact hsub _ ho
    isplitl [HQ]
    · iexact HQ
    · iexact HR

/-- The resources of the operations other than `id` stay valid when `lin` gains `id`. -/
theorem opRes_map_grow (γ : ProtoNames) (ops : GMap OpId OpMeta) (lin : List (OpId × RegOutput w64))
    (id : OpId) (e : RegOutput w64) :
    ([∗map] k ↦ x ∈ Iris.Std.PartialMap.delete ops id, opRes (GF := GF) γ lin k x) ⊢
      [∗map] k ↦ x ∈ Iris.Std.PartialMap.delete ops id, opRes γ (lin ++ [(id, e)]) k x := by
  refine BigSepM.bigSepM_mono (fun {k x} hk => opRes_lin_grow γ lin _ k x
    (fun y hy => List.mem_append_left _ hy) (fun o ho => ?_))
  have hk' : id ≠ k := by
    intro e'; subst e'
    rw [Iris.Std.get?_delete_eq rfl] at hk; cases hk
  rcases List.mem_append.1 ho with ho | ho
  · exact ho
  · simp at ho; exact absurd ho.1.symm hk'

/-- `opRes` with its atomic update's later removed (the form after spending a credit). -/
def opResNL (γ : ProtoNames) (lin : List (OpId × RegOutput w64)) (id : OpId) (m : OpMeta) :
    IProp GF :=
  iprop((⌜∀ o, (id, o) ∉ lin⌝ ∗ ∃ Q, savedQ m.rcpt Q ∗ opAU γ m.input Q) ∨
    (∃ (o : RegOutput w64) (Q : w64 → w64 → RegOutput w64 → IProp GF) (σ σ' : w64),
      ⌜(id, o) ∈ lin⌝ ∗ savedQ m.rcpt Q ∗ (▷ Q σ σ' o ∨ token m.claim)))

theorem opRes_to_NL (γ : ProtoNames) (lin : List (OpId × RegOutput w64)) (id : OpId) (m : OpMeta) :
    opRes (GF := GF) γ lin id m ⊢ ▷ opResNL γ lin id m := by
  unfold opRes opResNL
  iintro (⟨%hn, %Q, HQ, HAU⟩ | ⟨%o, %Q, %σ, %σ', %ho, HQ, HR⟩)
  · inext
    ileft
    isplitr
    · ipureintro; exact hn
    iexists Q
    iframe
  · iapply BI.later_intro
    iright
    iexists o, Q, σ, σ'
    isplitr
    · ipureintro; exact ho
    iframe

theorem NL_to_opRes (γ : ProtoNames) (lin : List (OpId × RegOutput w64)) (id : OpId) (m : OpMeta) :
    opResNL (GF := GF) γ lin id m ⊢ opRes γ lin id m := by
  unfold opRes opResNL
  iintro (⟨%hn, %Q, HQ, HAU⟩ | ⟨%o, %Q, %σ, %σ', %ho, HQ, HR⟩)
  · ileft
    isplitr
    · ipureintro; exact hn
    iexists Q
    iframe HQ
    inext
    iexact HAU
  · iright
    iexists o, Q, σ, σ'
    isplitr
    · ipureintro; exact ho
    iframe

theorem opRes_map_to_NL (γ : ProtoNames) (ops : GMap OpId OpMeta) (lin : List (OpId × RegOutput w64)) :
    ([∗map] k ↦ x ∈ ops, opRes (GF := GF) γ lin k x) ⊢ ▷ [∗map] k ↦ x ∈ ops, opResNL γ lin k x :=
  (BigSepM.bigSepM_mono (fun {k x} _ => opRes_to_NL γ lin k x)).trans BigSepM.bigSepM_later_2

/-- The operations' resources while a list of them is linearized: done (`S`) or not yet. -/
def psiRes (γ : ProtoNames) (lin lin' : List (OpId × RegOutput w64)) (S : List OpId) (k : OpId)
    (x : OpMeta) : IProp GF :=
  if k ∈ S then opRes γ lin' k x else opResNL γ lin k x

theorem psiRes_congr (γ : ProtoNames) (lin lin' : List (OpId × RegOutput w64)) (S S' : List OpId)
    (k : OpId) (x : OpMeta) (h : k ∈ S ↔ k ∈ S') :
    psiRes (GF := GF) γ lin lin' S k x = psiRes γ lin lin' S' k x := by
  unfold psiRes
  by_cases hk : k ∈ S
  · rw [if_pos hk, if_pos (h.1 hk)]
  · rw [if_neg hk, if_neg (fun h' => hk (h.2 h'))]

/-- **Linearize a list of operations**: fire their atomic updates in order, from `σ` to `σ'`
(their replay), each one's resources becoming linearized ones. -/
theorem fire_all (γ : ProtoNames) (ops : GMap OpId OpMeta) (lin lin' : List (OpId × RegOutput w64))
    (E : CoPset) (hE : ↑clientN ⊆ E) :
    ∀ (L : List (OpId × RegOutput w64)) (S : List OpId) (σ σ' : w64),
      replayOk σ (entries ops L) σ' →
      (∀ x ∈ L, (ops.lookup x.1).isSome ∧ x ∈ lin' ∧ (∀ o, (x.1, o) ∉ lin) ∧ x.1 ∉ S) →
      (L.map Prod.fst).Nodup →
      ghostVar γ.reg (1 : Qp).half σ ∗ ([∗map] k ↦ x ∈ ops, psiRes (GF := GF) γ lin lin' S k x) ⊢
        |={E}=> ghostVar γ.reg (1 : Qp).half σ' ∗
          [∗map] k ↦ x ∈ ops, psiRes γ lin lin' (S ++ L.map Prod.fst) k x
  | [], S, σ, σ', hr, _, _ => by
    have : σ' = σ := hr
    subst this
    simp only [List.map_nil, List.append_nil]
    iintro ⟨H1, H2⟩
    imodintro
    iframe
  | x :: L, S, σ, σ', hr, hx, hnd => by
    obtain ⟨hsome, hlin', hnl, hnS⟩ := hx x (List.mem_cons_self ..)
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 hsome
    have hent : entries ops (x :: L) = (m.input, x.2) :: entries ops L := by
      simp [entries, hm]
    rw [hent] at hr
    obtain ⟨hout, hr'⟩ := hr
    rw [List.map_cons, List.nodup_cons] at hnd
    iintro ⟨Hreg, Hmap⟩
    icases (BigSepM.bigSepM_delete (show get? ops x.1 = some m from hm)).1 $$ Hmap with ⟨Hm, Hrest⟩
    have hpsi : psiRes (GF := GF) γ lin lin' S x.1 m = opResNL γ lin x.1 m := by
      unfold psiRes; rw [if_neg hnS]
    rw [hpsi]
    unfold opResNL
    icases Hm with (⟨-, %Q, #HQ, HAU⟩ | ⟨%o, %Q, %σ1, %σ2, %ho, -, -⟩)
    rotate_left
    · exact absurd ho (hnl o)
    imod opAU_fire γ m.input Q σ E hE $$ [HAU Hreg] with ⟨Hreg, HQr⟩
    · iframe
    rw [hout]
    ihave Hmap : [∗map] k ↦ y ∈ ops, psiRes (GF := GF) γ lin lin' (S ++ [x.1]) k y $$ [Hrest HQr]
    · iapply (BigSepM.bigSepM_delete (show get? ops x.1 = some m from hm)).2
      isplitl [HQr]
      · have : psiRes (GF := GF) γ lin lin' (S ++ [x.1]) x.1 m = opRes γ lin' x.1 m := by
          unfold psiRes; rw [if_pos (by simp)]
        rw [this]
        unfold opRes
        iright
        iexists x.2, Q, σ, (casApply σ m.input).1
        isplitr
        · ipureintro; exact hlin'
        isplitr
        · iexact HQ
        ileft
        inext
        iexact HQr
      · iapply (BigSepM.bigSepM_mono (fun {k y} hk => by
          have hk' : x.1 ≠ k := by
            intro e; subst e
            rw [Iris.Std.get?_delete_eq rfl] at hk; cases hk
          rw [psiRes_congr γ lin lin' S (S ++ [x.1]) k y (by
            simp only [List.mem_append, List.mem_singleton]
            exact ⟨Or.inl, fun h => h.elim id (fun e => absurd e.symm hk')⟩)])) $$ Hrest
    ihave H := fire_all γ ops lin lin' E hE L (S ++ [x.1]) _ σ' hr' (by
      intro y hy
      obtain ⟨h1, h2, h3, h4⟩ := hx y (List.mem_cons_of_mem _ hy)
      refine ⟨h1, h2, h3, ?_⟩
      simp only [List.mem_append, List.mem_singleton, not_or]
      exact ⟨h4, fun e => hnd.1 (e ▸ List.mem_map_of_mem hy)⟩) hnd.2 $$ [Hreg Hmap]
    · iframe
    rw [show S ++ (x :: L).map Prod.fst = S ++ [x.1] ++ L.map Prod.fst by simp]
    iexact H

end

end Perennial.gryff
