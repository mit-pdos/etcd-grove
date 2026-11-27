/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Ghost/Impl/Step.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`; the client's atomic update is remote's one-shot update (`AUof`).
-/
/-
The replicas' laws' implementation: pure consequences of the invariant (`ghost_pure`,
`ghost_pure_rep`), learning a fact (`ghost_fact`), and a model step that leaves the linearized
log and the registry as they are (`ghost_step`).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Ghost.Impl.Basic

@[expose] public section

noncomputable section

namespace VsrGhost.Impl

open Perennial Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode VsrModel
open Net

attribute [local instance] entryCountable statusCountable repCountable factCountable factDecEq
  kvInCountable

section proofs
attribute [local instance] GooseGlobalGS.gooseInvGS
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF]

theorem ghost_pure_impl (g : GN) (E : CoPset) (hE : ↑sysNI ⊆ E) (fs : List Fact) (φ : Prop)
    (H : ∀ s, VsrModel.Inv s → (∀ f ∈ fs, Holds s f) → φ) :
    sysInvI (GF := GF) g -∗ ([∗list] f ∈ fs, factI g f) ={E}=∗ ⌜φ⌝ := by
  iintro #Hsys Hfs
  unfold sysInvI
  iinv Hsys with >Hb Hclose
  iunfold sysBody, sysAt at Hb
  icases Hb with ⟨%s, %F, %R, %N, %M, %hInv, HF, %hF, HFs, HR, %hR, Habs, HN, %hN, HM, %hM, HMs, Hsz⟩
  ihave %h := facts_holds g s F hF fs $$ HF Hfs
  imod Hclose $$ [HF HFs HR Habs HN HM HMs Hsz] with -
  · unfold sysBody sysAt
    iexists s, F, R, N, M
    iframe
    ipureintro
    exact ⟨hInv, hF, hR, hN, hM⟩
  imodintro
  ipureintro
  exact H s hInv h

theorem ghost_pure_rep_impl (g : GN) (E : CoPset) (hE : ↑sysNI ⊆ E) (r : Nat) (p : Rep)
    (fs : List Fact) (φ : Prop)
    (H : ∀ s, VsrModel.Inv s → s.reps r = p → (∀ f ∈ fs, Holds s f) → φ) :
    sysInvI (GF := GF) g -∗ repOwnI g r p -∗ ([∗list] f ∈ fs, factI g f) ={E}=∗ repOwnI g r p ∗ ⌜φ⌝ := by
  iintro #Hsys Hr Hfs
  unfold sysInvI
  iinv Hsys with >Hb Hclose
  iunfold sysBody, sysAt at Hb
  icases Hb with ⟨%s, %F, %R, %N, %M, %hInv, HF, %hF, HFs, HR, %hR, Habs, HN, %hN, HM, %hM, HMs, Hsz⟩
  ihave %h := facts_holds g s F hF fs $$ HF Hfs
  ihave %hRr := Perennial.ghost_map_lookup $$ HR Hr
  imod Hclose $$ [HF HFs HR Habs HN HM HMs Hsz] with -
  · unfold sysBody sysAt
    iexists s, F, R, N, M
    iframe
    ipureintro
    exact ⟨hInv, hF, hR, hN, hM⟩
  imodintro
  iframe Hr
  ipureintro
  exact H s hInv (hR r p hRr) h

theorem ghost_step_impl (g : GN) (E : CoPset) (hE : ↑sysNI ⊆ E) (n r : Nat) (p p' : Rep)
    (fs fs' : List Fact) (st : Sys → Sys)
    (H : ∀ s, VsrModel.Inv s → s.n = n → s.reps r = p → (∀ f ∈ fs, Holds s f) →
      VsrModel.Inv (st s) ∧ Le s (st s) ∧ (st s).reps r = p' ∧
      (∀ x, x ≠ r → (st s).reps x = s.reps x) ∧
      (st s).lin = s.lin ∧ (st s).reg = s.reg ∧ (∀ f ∈ fs', Holds (st s) f)) :
    factI (GF := GF) g (.size n) -∗ sysInvI g -∗ repOwnI g r p -∗ ([∗list] f ∈ fs, factI g f) ={E}=∗
      repOwnI g r p' ∗ [∗list] f ∈ fs', factI g f := by
  iintro #Hn #Hsys Hr Hfs
  unfold sysInvI
  iinv Hsys with >Hb Hclose
  iunfold sysBody, sysAt at Hb
  icases Hb with ⟨%s, %F, %R, %N, %M, %hInv, HF, %hF, HFs, HR, %hR, Habs, HN, %hN, HM, %hM, HMs,
    Hsz⟩
  -- the size fact: the system is sized (its token), with `n` replicas
  ihave %hFn := Perennial.ghost_map_lookup $$ HF Hn
  ihave Htok := sized_of_lookup g F M s hFn $$ Hsz
  have hsn : s.n = n := hF _ _ hFn
  ihave %h := facts_holds g s F hF fs $$ HF Hfs
  ihave %hRr := Perennial.ghost_map_lookup $$ HR Hr
  obtain ⟨hInv', hLe, hr', hrx, hlin, hreg, hfs'⟩ := H s hInv hsn (hR r p hRr) h
  imod Perennial.ghost_map_update p' $$ HR Hr with ⟨HR, Hr⟩
  imod facts_add g (st s) fs' hfs' F (fun f u hf => holds_mono hLe f (hF f u hf)) $$ HF HFs
    with ⟨%F', HF, %hF', HFs, Hfs'⟩
  ihave Hsz : sizedI g F' M (st s) $$ [Htok]
  · iunfold sizedI; iright; iexact Htok
  imod Hclose $$ [HF HFs HR Habs HN HM HMs Hsz] with -
  · unfold sysBody sysAt
    iexists (st s), F', (<[r := p']> R), N, M
    rw [hlin, hreg]
    iframe
    ipureintro
    refine ⟨hInv', hF', ?_, hN, hM⟩
    intro x q hx
    simp only [GMap.lookup_insert_eq_iff] at hx
    split at hx
    · rename_i hrx'; subst hrx'; cases hx; exact hr'
    · rename_i hne
      rw [hrx x (Ne.symm hne)]
      exact hR x q hx
  imodintro
  iframe

theorem ghost_fact_impl (g : GN) (E : CoPset) (hE : ↑sysNI ⊆ E) (n r : Nat) (p : Rep)
    (fs : List Fact) (f : Fact)
    (H : ∀ s, VsrModel.Inv s → s.n = n → s.reps r = p → (∀ f' ∈ fs, Holds s f') → Holds s f) :
    factI (GF := GF) g (.size n) -∗ sysInvI g -∗ repOwnI g r p -∗ ([∗list] f' ∈ fs, factI g f') ={E}=∗
      repOwnI g r p ∗ factI g f := by
  iintro #Hn #Hsys Hr Hfs
  imod ghost_step_impl g E hE n r p p fs [f] id
    (fun s h hn hr hfs => ⟨h, ⟨fun _ => Nat.le_refl _, fun _ _ h => h,
      fun _ L h => ⟨L, h, List.prefix_refl L⟩, fun _ _ => List.prefix_refl _,
      fun _ _ _ => Or.inl rfl, List.prefix_refl _, fun _ _ _ h => h, rfl⟩,
      hr, fun _ _ => rfl, rfl, rfl, by simpa using H s h hn hr hfs⟩) $$ Hn Hsys Hr Hfs
    with ⟨Hr, Hf⟩
  imodintro
  iframe Hr
  icases Hf with ⟨Hf, -⟩
  iexact Hf

end proofs

end VsrGhost.Impl
