/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Ghost/Impl/Alloc.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`; the client's atomic update is remote's one-shot update (`AUof`).
-/
/-
`ghost_alloc`'s implementation: the start's ghost state and invariants.
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

/-- Insert the keys `l` (fresh, distinct) with values `f`, getting their elements. -/
theorem ghost_map_insert_list {K V : Type} [DecidableEq K] [Pos.Countable K] [Pos.Countable V]
    (γ : GName) (f : K → V) (l : List K) (hl : l.Nodup) :
    ∀ (m : GMap K V), (∀ k ∈ l, m !! k = none) →
    (ghostMapAuth γ 1 m : IProp GF) ==∗ ∃ m' : GMap K V, ghostMapAuth γ 1 m' ∗
      ⌜∀ k v, m' !! k = some v → m !! k = some v ∨ v = f k⌝ ∗
      [∗list] k ∈ l, ghostMapElem γ k (DFrac.own 1) (f k) := by
  induction l with
  | nil =>
    intro m _
    iintro H
    imodintro
    iexists m
    iframe
    isplit
    · ipureintro; intro k v h; exact Or.inl h
    · iapply BigSepL.bigSepL_nil.2; iempintro
  | cons k l ih =>
    intro m hm
    have hk : m !! k = none := hm k List.mem_cons_self
    have hkl : k ∉ l := (List.nodup_cons.mp hl).1
    iintro H
    imod Perennial.ghost_map_insert k (f k) hk $$ H with ⟨H, Hk⟩
    imod ih (List.nodup_cons.mp hl).2 (<[k := f k]> m) (by
        intro k' hk'
        rw [GMap.lookup_insert_ne]
        · exact hm k' (List.mem_cons_of_mem _ hk')
        · intro h; subst h; exact hkl hk') $$ H with ⟨%m', H, %hm', Hl⟩
    imodintro
    iexists m'
    isplitl [H]
    · iexact H
    isplitr
    · ipureintro
      intro k' v h
      rcases hm' k' v h with h | h
      · simp only [GMap.lookup_insert_eq_iff] at h
        split at h
        · subst_vars; cases h; exact Or.inr rfl
        · exact Or.inl h
      · exact Or.inr h
    iapply BigSepL.bigSepL_cons.2
    iframe

theorem ghost_alloc_impl :
    ⊢ |={⊤}=> ∃ g : GN, sysInvI g ∗ regInvI g ∗ absOwnI g (fun _ => none) ∗ token g.size ∗
      ([∗list] r ∈ List.range 5, repOwnI g r VsrModel.initRep) ∗
      ([∗list] c ∈ List.range 6, nextReqI g (c + 1) 1) := by
  imod Perennial.ghost_map_alloc_empty (K := Fact) (V := Unit) with ⟨%γf, HF⟩
  imod Perennial.ghost_map_alloc_empty (K := Nat) (V := Rep) with ⟨%γr, HR⟩
  imod ghost_map_insert_list γr (fun _ => VsrModel.initRep) (List.range 5) List.nodup_range ∅
    (fun _ _ => rfl) $$ HR with ⟨%R, HR, %hR, Hreps⟩
  imod Perennial.ghost_map_alloc_empty (K := Nat) (V := Nat) with ⟨%γn, HN⟩
  imod ghost_map_insert_list γn (fun _ => (1 : Nat)) ((List.range 6).map (· + 1))
    (List.Pairwise.map (· + 1) (fun a b h hab => h (by omega)) List.nodup_range) ∅ (fun _ _ => rfl) $$ HN
    with ⟨%N, HN, -, Hnext⟩
  imod Perennial.ghost_map_alloc_empty (K := Nat × Nat) (V := RegVal) with ⟨%γm, HM⟩
  icases (ghostMapAuth_halves γm _).1 $$ HM with ⟨HM, HM'⟩
  imod ghostVar_alloc ([] : List Entry) with ⟨%γa, Ha⟩
  icases (ghostVar_split_half γa 1 ([] : List Entry)).1 $$ Ha with ⟨Ha, Ha'⟩
  imod token_alloc with ⟨%γz, Hz⟩
  imod inv_alloc sysNI ⊤ (sysBody ⟨γf, γr, γa, γn, γm, γz⟩) $$ [HF HR Ha HN HM] with #Hsys
  · inext
    unfold sysBody sysAt
    iexists VsrModel.init 3, ∅, R, N, ∅
    isplitr
    · ipureintro; exact init_inv 3 (by decide)
    isplitl [HF]
    · iexact HF
    isplitr
    · ipureintro; intro f u h; cases h
    isplitr
    · iapply BigSepM.bigSepM_empty.2; iempintro
    isplitl [HR]
    · iexact HR
    isplitr
    · ipureintro
      intro r p h
      rcases hR r p h with h | h
      · cases h
      · exact h.symm
    rw [show (VsrModel.init 3).lin = [] from rfl]
    isplitl [Ha]
    · iexact Ha
    isplitl [HN]
    · iexact HN
    isplitr
    · ipureintro; intro _ _ _ _ _; rfl
    isplitl [HM]
    · iexact HM
    isplitr
    · ipureintro; intro _ _; rfl
    isplitr
    · iapply BigSepM.bigSepM_empty.2; iempintro
    iunfold sizedI
    ileft
    ipureintro
    exact ⟨rfl, rfl, rfl⟩
  imod inv_alloc regInvN ⊤ (regBody ⟨γf, γr, γa, γn, γm, γz⟩) $$ [HM'] with #Hreg
  · inext
    unfold regBody
    iexists ∅
    iframe
    iapply BigSepM.bigSepM_empty.2; iempintro
  imodintro
  iexists ⟨γf, γr, γa, γn, γm, γz⟩
  unfold sysInvI regInvI
  isplitr
  · iexact Hsys
  isplitr
  · iexact Hreg
  isplitl [Ha']
  · unfold absOwnI
    iexists []
    iframe
    ipureintro; rfl
  isplitl [Hz]
  · iexact Hz
  isplitl [Hreps]
  · iexact Hreps
  · ieval (simp only [BigSepL.bigSepL_map]) at Hnext
    iexact Hnext

/-- `ghost_size` over the implementation's names: with node 0's size token, the unsized system
(at `init m`, no fact, nothing registered) moves to `init n` with the fact `.size n`, and takes
the token (sized); the sized system already holds the token (two tokens: impossible). -/
theorem ghost_size_impl (g : GN) (E : CoPset) (hE : ↑sysNI ⊆ E) (n : Nat) (hn : 0 < n) :
    sysInvI g -∗ token g.size ={E}=∗ factI g (.size n) := by
  iintro #Hsys Ht
  unfold sysInvI
  iinv Hsys with >Hb Hclose
  iunfold sysBody, sysAt at Hb
  icases Hb with ⟨%s, %F, %R, %N, %M, %hInv, HF, %hF, HFs, HR, %hR, Habs, HN, %hN, HM, %hM, HMs,
    Hsz⟩
  iunfold sizedI at Hsz
  icases Hsz with (%hu | Ht')
  · obtain ⟨rfl, rfl, hs⟩ := hu
    obtain ⟨m, rfl⟩ : ∃ m, s = init m := ⟨_, hs⟩
    imod facts_add g (init n) [.size n] (by intro f hf; simp at hf; subst hf; rfl) ∅
      (fun f u h => by cases h) $$ HF HFs with ⟨%F', HF, %hF', HFs, Hfs⟩
    imod Hclose $$ [HF HFs HR Habs HN HM HMs Ht] with -
    · unfold sysBody sysAt
      iexists init n, F', R, N, ∅
      rw [show (init n).lin = (init m).lin from rfl]
      isplitr
      · ipureintro; exact init_inv n hn
      isplitl [HF]
      · iexact HF
      isplitr
      · ipureintro; exact hF'
      isplitl [HFs]
      · iexact HFs
      isplitl [HR]
      · iexact HR
      isplitr
      · ipureintro; exact hR
      isplitl [Habs]
      · iexact Habs
      isplitl [HN]
      · iexact HN
      isplitr
      · ipureintro; exact hN
      isplitl [HM]
      · iexact HM
      isplitr
      · ipureintro; exact hM
      isplitl [HMs]
      · iexact HMs
      iunfold sizedI
      iright
      iexact Ht
    imodintro
    icases Hfs with ⟨Hf, -⟩
    iexact Hf
  · iexfalso
    iapply token_exclusive $$ Ht Ht'

end proofs

end VsrGhost.Impl
