/-
The tail's commit (`commit`): every pending version of the key up to the committed one is
linearized, in version order.
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Protocol.Fire

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

namespace github_com.despreston.go_craq

/-- During a commit of `k` from `cvOf L k` up: version `w`'s record is done at stage `j` (every
version of `k` up to `j` linearized). -/
def stageDone (L : CLog) (k : GoString) (j : Int) (w : w64) (ri : RecInfo) : Bool :=
  decide (uint.Z w ≤ uint.Z (cvOf L ri.key) ∨ (ri.key = k ∧ uint.Z w ≤ j))

/-- The invariant's state after a commit. -/
theorem craqWf_commit {l l' : List (GoString × GoString)} {L : CLog} {n : w64}
    {R : GMap w64 RecInfo} {k x : GoString} {v : w64} {p c : GName}
    (Hwf : craqWf l L n R) (hlt : uint.Z (cvOf L k) < uint.Z v)
    (hRv : R.lookup v = some ((k, x, p, c) : RecInfo))
    (hl1 : ∀ k', k' ≠ k → kvOfPuts l' k' = kvOfPuts l k') (hl2 : kvOfPuts l' k = some x) :
    craqWf l' (L ++ [(k, v)]) n R := by
  have hv0 : v ≠ W64 0 := by
    intro h; subst h
    have := uint_Z_nonneg (cvOf L k)
    have h0 : uint.Z (W64 0) = 0 := rfl
    omega
  refine ⟨Hwf.1, fun k' => ?_, fun k' => ?_, Hwf.2.2.2⟩
  · by_cases hk : k' = k
    · subst hk
      rw [hl2]
      unfold absOf
      rw [cvOf_commit_self _ _ _ hlt]
      simp only [hRv]
      simp only [show (v = W64 0) = False from propext ⟨hv0, False.elim⟩]
      rfl
    · rw [hl1 k' hk, Hwf.2.1 k']
      unfold absOf
      rw [cvOf_commit_ne _ _ _ _ hk]
  · by_cases hk : k' = k
    · subst hk
      rw [cvOf_commit_self _ _ _ hlt]
      intro _
      exact ⟨_, hRv, rfl⟩
    · rw [cvOf_commit_ne _ _ _ _ hk]
      exact Hwf.2.2.1 k'

section commit
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable {GF : BundledGFunctors} [G : GooseGlobalGS HasLC.hasLC GF]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The records at stage `j`. -/
def stageRes (γ : CraqNames) (L : CLog) (k : GoString) (j : Int) (R : GMap w64 RecInfo) :
    IProp GF :=
  [∗map] w ↦ ri ∈ R, recRes γ ri (stageDone L k j w ri)

theorem stageRes_delete (γ : CraqNames) (L : CLog) (k : GoString) (j : Int)
    {R : GMap w64 RecInfo} {w : w64} {ri : RecInfo} (h : R.lookup w = some ri) :
    stageRes (GF := GF) γ L k j R ⊣⊢
      recRes γ ri (stageDone L k j w ri) ∗ stageRes γ L k j (GMap.delete w R) := by
  unfold stageRes
  exact BigSepM.bigSepM_delete (M := GMap w64) (show get? R w = some ri from h)

/-- A stage changes nothing for the records other than `k`'s version `j + 1`. -/
theorem stageRes_succ_eq (γ : CraqNames) (L : CLog) (k : GoString) (j : Int)
    (R : GMap w64 RecInfo) (hj : 0 ≤ j ∧ j + 1 < 2 ^ 64)
    (h : ∀ w ri, R.lookup w = some ri → w = W64 (j + 1) → ri.key ≠ k) :
    stageRes (GF := GF) γ L k j R = stageRes γ L k (j + 1) R := by
  unfold stageRes
  apply BigSepM.bigSepM_eq
  intro w ri hw
  have hw' : R.lookup w = some ri := hw
  unfold stageDone
  by_cases hwe : w = W64 (j + 1)
  · have hk := h w ri hw' hwe
    simp [hk]
  · have hne : uint.Z w ≠ j + 1 := by
      intro he
      apply hwe
      apply uint_Z_inj.1
      rw [he, uint_Z_W64 _ (by omega) hj.2]
    have : uint.Z w ≤ j ↔ uint.Z w ≤ j + 1 := by omega
    simp only [this]

/-- One stage: linearize `k`'s version `j + 1`, if it is one. -/
theorem commit_step (γ : CraqNames) (E : CoPset) (hE : clientMask ⊆ E) (L : CLog) (k : GoString)
    (j : Int) (R : GMap w64 RecInfo) (l : List (GoString × GoString))
    (hj0 : uint.Z (cvOf L k) ≤ j) (hj1 : j + 1 < 2 ^ 64) :
    ⊢ ghostVar (GF := GF) γ.abs (1 : Qp).half l -∗ stageRes γ L k j R ={E}=∗
      ∃ l', ⌜(∀ k', k' ≠ k → kvOfPuts l' k' = kvOfPuts l k') ∧
        (∀ ri, R.lookup (W64 (j + 1)) = some ri → ri.key = k → kvOfPuts l' k = some ri.val)⌝ ∗
        ghostVar γ.abs (1 : Qp).half l' ∗ stageRes γ L k (j + 1) R := by
  have hj : 0 ≤ j ∧ j + 1 < 2 ^ 64 := ⟨by have := uint_Z_nonneg (cvOf L k); omega, hj1⟩
  have hwZ : uint.Z (W64 (j + 1)) = j + 1 := uint_Z_W64 _ (by omega) hj1
  iintro Habs Hst
  by_cases hpend : ∃ ri, R.lookup (W64 (j + 1)) = some ri ∧ ri.key = k
  · obtain ⟨ri, hR, hk⟩ := hpend
    icases (stageRes_delete γ L k j hR).1 $$ Hst with ⟨Hr, Hst⟩
    have hd0 : stageDone L k j (W64 (j + 1)) ri = false := by
      unfold stageDone; rw [hk, hwZ]; simp; omega
    have hd1 : stageDone L k (j + 1) (W64 (j + 1)) ri = true := by
      unfold stageDone; rw [hk, hwZ]; simp
    rw [hd0]
    imod fire_put γ E hE l ri $$ Habs Hr with ⟨Habs, Hr⟩
    imodintro
    iexists ((ri.key, ri.val) :: l)
    iframe Habs
    isplitr
    · ipureintro
      refine ⟨fun k' hk' => ?_, fun ri' hR' _ => ?_⟩
      · rw [kvOfPuts_cons]; simp [hk, hk']
      · rw [hR] at hR'; cases hR'
        rw [kvOfPuts_cons]; simp [hk]
    iapply (stageRes_delete γ L k (j + 1) hR).2
    rw [hd1]
    iframe Hr
    rw [← stageRes_succ_eq γ L k j _ hj]
    · iexact Hst
    · intro w ri' hw hwe
      subst hwe
      rw [GMap.lookup_delete] at hw
      cases hw
  · rw [← stageRes_succ_eq γ L k j R hj]
    · imodintro
      iexists l
      iframe
      ipureintro
      exact ⟨fun _ _ => rfl, fun ri hR hk => absurd ⟨ri, hR, hk⟩ hpend⟩
    · intro w ri hw hwe hk
      subst hwe
      exact hpend ⟨ri, hw, hk⟩

/-- The stages from `cvOf L k` to `cvOf L k + d`. -/
theorem commit_loop (γ : CraqNames) (E : CoPset) (hE : clientMask ⊆ E) (L : CLog) (k : GoString)
    (R : GMap w64 RecInfo) (l0 : List (GoString × GoString)) (d : Nat)
    (hd : uint.Z (cvOf L k) + d < 2 ^ 64) :
    ⊢ ghostVar (GF := GF) γ.abs (1 : Qp).half l0 -∗ stageRes γ L k (uint.Z (cvOf L k)) R ={E}=∗
      ∃ l, ⌜(∀ k', k' ≠ k → kvOfPuts l k' = kvOfPuts l0 k') ∧
        (0 < d → ∀ ri, R.lookup (W64 (uint.Z (cvOf L k) + d)) = some ri → ri.key = k →
          kvOfPuts l k = some ri.val)⌝ ∗
        ghostVar γ.abs (1 : Qp).half l ∗ stageRes γ L k (uint.Z (cvOf L k) + d) R := by
  induction d with
  | zero =>
    iintro Habs Hst
    imodintro
    iexists l0
    iframe Habs
    isplitr
    · ipureintro
      exact ⟨fun _ _ => rfl, fun h => absurd h (Nat.lt_irrefl 0)⟩
    have : uint.Z (cvOf L k) + ((0 : Nat) : Int) = uint.Z (cvOf L k) := by omega
    rw [this]
    iexact Hst
  | succ d ih =>
    iintro Habs Hst
    imod ih (by omega) $$ Habs Hst with ⟨%l, %Hl, Habs, Hst⟩
    imod commit_step γ E hE L k (uint.Z (cvOf L k) + d) R l (by omega) (by omega) $$ Habs Hst
      with ⟨%l', %Hl', Habs, Hst⟩
    have he : uint.Z (cvOf L k) + ((d + 1 : Nat) : Int) = uint.Z (cvOf L k) + d + 1 := by omega
    rw [he]
    imodintro
    iexists l'
    iframe Habs Hst
    ipureintro
    refine ⟨fun k' hk' => (Hl'.1 k' hk').trans (Hl.1 k' hk'), fun _ ri hR hk => Hl'.2 ri hR hk⟩

theorem stage_start (γ : CraqNames) (L : CLog) (k : GoString) (R : GMap w64 RecInfo) :
    ([∗map] w ↦ ri ∈ R, recRes (GF := GF) γ ri (decide (uint.Z w ≤ uint.Z (cvOf L ri.key))))
      ⊢ stageRes γ L k (uint.Z (cvOf L k)) R := by
  unfold stageRes
  apply BigSepM.bigSepM_mono
  intro w ri _
  unfold stageDone
  by_cases hk : ri.key = k
  · rw [hk]; simp
  · simp [hk]

theorem stage_end (γ : CraqNames) (L : CLog) (k : GoString) (v : w64) (R : GMap w64 RecInfo)
    (hlt : uint.Z (cvOf L k) < uint.Z v) :
    stageRes (GF := GF) γ L k (uint.Z v) R ⊢
      [∗map] w ↦ ri ∈ R, recRes γ ri
        (decide (uint.Z w ≤ uint.Z (cvOf (L ++ [(k, v)]) ri.key))) := by
  unfold stageRes
  apply BigSepM.bigSepM_mono
  intro w ri _
  unfold stageDone
  by_cases hk : ri.key = k
  · rw [hk, cvOf_commit_self _ _ _ hlt]
    have h2 : (uint.Z w ≤ uint.Z (cvOf L k) ∨ uint.Z w ≤ uint.Z v) ↔
        uint.Z w ≤ uint.Z v := by omega
    simp only [true_and, h2]; exact .rfl
  · rw [cvOf_commit_ne _ _ _ _ hk]
    simp [hk]

theorem commit.holds : commit.spec (GF := GF) (G := G) := by
  intro γ E hE L v k x
  iintro ⟨#Hinv, Htok, #Hval, Hlc⟩
  by_cases hlt' : ¬ uint.Z (cvOf L k) < uint.Z v
  · simp only [hlt', ↓reduceIte]
    imodintro
    iexact Htok
  have hlt : uint.Z (cvOf L k) < uint.Z v := Classical.not_not.1 hlt'
  simp only [hlt, ↓reduceIte]
  unfold isCraq
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later $$ Hlc Hi with Hi
  unfold craqInv
  icases Hi with ⟨%l, %L0, %n, %R, Habs, HL, Hnext, HR, %Hwf, #Hels, Hrs⟩
  unfold tailTok
  imod cv_halves_update γ.cv (l' := L ++ [(k, v)]) (List.prefix_append L _) $$ Htok HL
    with ⟨%HLL, Htok, HL⟩
  subst HLL
  unfold valsElem
  icases Hval with ⟨-, %p, %c, Hel⟩
  ihave %HRv := ghost_map_lookup $$ HR Hel
  ihave Hst := stage_start γ L k R $$ Hrs
  have hv := uint_Z_lt v
  have hc := uint_Z_nonneg (cvOf L k)
  have Hloop := commit_loop (GF := GF) γ (E \ ↑craqN) (clientN_sub_diff hE) L k R l
    (uint.Z v - uint.Z (cvOf L k)).toNat (by omega)
  have he : uint.Z (cvOf L k) + ((uint.Z v - uint.Z (cvOf L k)).toNat : Int) = uint.Z v := by
    omega
  rw [he] at Hloop
  imod Hloop $$ Habs Hst with ⟨%l', %Hl', Habs, Hst⟩
  have hWv : W64 (uint.Z v) = v := uint_Z_inj.1 (uint_Z_W64 _ (uint_Z_nonneg v) hv)
  have hl2 : kvOfPuts l' k = some x := by
    have := Hl'.2 (by omega) _ (hWv ▸ HRv) rfl
    exact this
  imod Hclose $$ [Habs HL Hnext HR Hst] with -
  · inext
    iexists l', L ++ [(k, v)], n, R
    iframe Habs HL Hnext HR Hels
    isplitr
    · ipureintro
      exact craqWf_commit Hwf hlt HRv Hl'.1 hl2
    iapply stage_end γ L k v R hlt $$ Hst
  imodintro
  iexact Htok

end commit

end github_com.despreston.go_craq

end Perennial
