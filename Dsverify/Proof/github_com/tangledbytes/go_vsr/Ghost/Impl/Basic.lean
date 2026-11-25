/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Ghost/Impl/Basic.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`; the client's atomic update is remote's one-shot update (`AUof`).
-/
/-
The ghost layer's implementation: the facts' ghost map (reading facts, adding facts).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Ghost.Impl.Defs

@[expose] public section

noncomputable section

namespace VsrGhost.Impl

open Perennial Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode VsrModel
open Net

attribute [local instance] entryCountable statusCountable repCountable factCountable factDecEq
  kvInCountable

/-! ## Masks -/

theorem mask_disj_of_inter {A B : CoPset} (h : A ∩ B = (∅ : CoPset)) :
    ∀ p, ¬ (p ∈ A ∧ p ∈ B) := by
  intro p ⟨h1, h2⟩
  have : p ∈ A ∩ B := LawfulSet.mem_inter.2 ⟨h1, h2⟩
  rw [h] at this
  exact LawfulSet.mem_empty this

theorem regInvN_sub : ∀ p, p ∈ (↑regInvN : CoPset) → p ∈ (↑regNI : CoPset) :=
  nclose_subseteq regNI "r"

theorem reqNI_sub : ∀ (k : Nat × Nat) p, p ∈ (↑(reqNI k) : CoPset) → p ∈ (↑regNI : CoPset) :=
  fun k p h => nclose_subseteq regNI "q" p (nclose_subseteq (ndot regNI "q") k p h)

theorem reqNI_regInvN_disj :
    ∀ (k : Nat × Nat) p, p ∈ (↑(reqNI k) : CoPset) → p ∈ (↑regInvN : CoPset) → False := by
  intro k p h1 h2
  have h1' := nclose_subseteq (ndot regNI "q") k p h1
  exact ndot_ne_disjoint regNI (x := "q") (y := "r") (by decide) p ⟨h1', h2⟩

theorem sysNI_regNI_disj : ∀ p, p ∈ (↑sysNI : CoPset) → p ∈ (↑regNI : CoPset) → False := by
  intro p h1 h2
  exact ndot_ne_disjoint (ndot nroot "vsr") (x := "sys") (y := "reg") (by decide) p ⟨h1, h2⟩

section proofs
attribute [local instance] GooseGlobalGS.gooseInvGS
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF]

/-- A fact in the facts' map rules the unsized state out: the system is sized (its token). -/
theorem sized_of_lookup (g : GN) (F : GMap Fact Unit) (M : GMap (Nat × Nat) RegVal) (s : Sys)
    {f : Fact} {u : Unit} (h : F !! f = some u) :
    sizedI g F M s -∗ token g.size := by
  iintro Hsz
  iunfold sizedI at Hsz
  icases Hsz with (%hu | Ht)
  · obtain ⟨rfl, -, -⟩ := hu
    cases h
  · iexact Ht

theorem fact_holds (g : GN) (s : Sys) (F : GMap Fact Unit)
    (hF : ∀ f u, F !! f = some u → Holds s f) (f : Fact) :
    ghostMapAuth g.facts 1 F -∗ factI g f -∗ ⌜Holds s f⌝ := by
  iintro HF Hf
  ihave %h := Perennial.ghost_map_lookup $$ HF Hf
  ipureintro
  exact hF _ _ h

theorem facts_holds (g : GN) (s : Sys) (F : GMap Fact Unit)
    (hF : ∀ f u, F !! f = some u → Holds s f) (fs : List Fact) :
    ghostMapAuth g.facts 1 F -∗ ([∗list] f ∈ fs, factI g f) -∗ ⌜∀ f ∈ fs, Holds s f⌝ := by
  induction fs with
  | nil =>
    iintro _ _
    ipureintro
    simp
  | cons f fs ih =>
    iintro HF Hfs
    icases BigSepL.bigSepL_cons.1 $$ Hfs with ⟨Hf, Hfs⟩
    ihave %h1 := fact_holds g s F hF f $$ HF Hf
    ihave %h2 := ih $$ HF Hfs
    ipureintro
    intro f' hf'
    rcases List.mem_cons.mp hf' with rfl | h
    · exact h1
    · exact h2 f' h

theorem facts_add (g : GN) (s : Sys) (fs : List Fact) (hfs : ∀ f ∈ fs, Holds s f) :
    ∀ (F : GMap Fact Unit), (∀ f u, F !! f = some u → Holds s f) →
    ghostMapAuth g.facts 1 F -∗ ([∗map] f ↦ _u ∈ F, factI g f) ==∗
      ∃ F' : GMap Fact Unit, ghostMapAuth g.facts 1 F' ∗
        ⌜∀ f u, F' !! f = some u → Holds s f⌝ ∗
        ([∗map] f ↦ _u ∈ F', factI g f) ∗ [∗list] f ∈ fs, factI g f := by
  induction fs with
  | nil =>
    intro F hF
    iintro HF HFs
    imodintro
    iexists F
    iframe
    isplit
    · ipureintro; exact hF
    · iapply BigSepL.bigSepL_nil.2; iempintro
  | cons f fs ih =>
    intro F hF
    have hf : Holds s f := hfs f List.mem_cons_self
    have hfs' : ∀ f ∈ fs, Holds s f := fun f' h => hfs f' (List.mem_cons_of_mem _ h)
    iintro HF HFs
    cases hFf : F !! f with
    | some u =>
      icases (BigSepM.bigSepM_lookup_acc (Φ := fun f (_ : Unit) => factI g f) hFf).1 $$ HFs
        with ⟨#Hf, HFs⟩
      ispecialize HFs $$ Hf
      imod ih hfs' F hF $$ HF HFs with ⟨%F', HF, %hF', HFs, Hfs⟩
      imodintro
      iexists F'
      isplitl [HF]
      · iexact HF
      isplitr
      · ipureintro; exact hF'
      isplitl [HFs]
      · iexact HFs
      iapply BigSepL.bigSepL_cons.2
      isplitl []
      · iexact Hf
      · iexact Hfs
    | none =>
      imod ghost_map_insert_persist f () hFf $$ HF with ⟨HF, #Hf⟩
      ihave HFs : ([∗map] f ↦ _u ∈ (<[f := ()]> F : GMap Fact Unit), factI g f) $$ [HFs]
      · iapply (BigSepM.bigSepM_insert (Φ := fun f (_ : Unit) => factI g f) hFf).2
        isplitl []
        · iexact Hf
        · iexact HFs
      imod ih hfs' (<[f := ()]> F) (by
          intro f' u h
          simp only [GMap.lookup_insert_eq_iff] at h
          split at h
          · subst_vars; exact hf
          · exact hF _ _ h) $$ HF HFs with ⟨%F', HF, %hF', HFs, Hfs⟩
      imodintro
      iexists F'
      isplitl [HF]
      · iexact HF
      isplitr
      · ipureintro; exact hF'
      isplitl [HFs]
      · iexact HFs
      iapply BigSepL.bigSepL_cons.2
      isplitl []
      · iexact Hf
      · iexact Hfs

end proofs

end VsrGhost.Impl
