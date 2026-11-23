/-
The protocol's laws at the invariant: `read`, `assign`, `collect`, `valsElem_pos`.
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Protocol.Commit

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

namespace github_com.despreston.go_craq

/-- The invariant's state after an assignment. -/
theorem craqWf_assign {l : List (GoString × GoString)} {L : CLog} {n : w64}
    {R : GMap w64 RecInfo} (ri : RecInfo) (Hwf : craqWf l L n R) (hn : uint.Z n < 2 ^ 64 - 1) :
    R.lookup (n + W64 1) = none ∧ uint.Z (n + W64 1) = uint.Z n + 1 ∧
      (∀ k, uint.Z (cvOf L k) ≤ uint.Z n) ∧
      craqWf l L (n + W64 1) (GMap.insert (n + W64 1) ri R) := by
  have hn1 : uint.Z (n + W64 1) = uint.Z n + 1 := by word
  have hnone : R.lookup (n + W64 1) = none := by
    cases h : R.lookup (n + W64 1) with
    | none => rfl
    | some _ =>
      have := (Hwf.1 (n + W64 1)).1 (by rw [h]; rfl)
      omega
  have hcv : ∀ k, uint.Z (cvOf L k) ≤ uint.Z n := by
    intro k
    by_cases h0 : cvOf L k = W64 0
    · rw [h0]; have := uint_Z_nonneg n; exact Int.le_trans (by decide) this
    · obtain ⟨ri, hri, _⟩ := Hwf.2.2 k h0
      exact ((Hwf.1 _).1 (by simp [hri])).2
  have hne : ∀ k, cvOf L k ≠ W64 0 → cvOf L k ≠ n + W64 1 := by
    intro k _ h
    have := hcv k
    rw [h] at this
    omega
  refine ⟨hnone, hn1, hcv, fun v => ?_, fun k => ?_, fun k hk => ?_⟩
  · by_cases hv : v = n + W64 1
    · subst hv
      rw [GMap.lookup_insert]
      simp only [Option.isSome_some, true_iff]
      word
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hv), Hwf.1 v]
      have : uint.Z v ≠ uint.Z n + 1 := fun h => hv (uint_Z_inj.1 (h.trans hn1.symm))
      omega
  · rw [Hwf.2.1 k]
    unfold absOf
    by_cases h0 : cvOf L k = W64 0
    · simp [h0]
    · simp only [h0, ↓reduceIte]
      rw [GMap.lookup_insert_ne _ _ (Ne.symm (hne k h0))]
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm (hne k hk))]
    exact Hwf.2.2 k hk

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable {GF : BundledGFunctors} [G : GooseGlobalGS HasLC.hasLC GF]

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem recRes_false (γ : CraqNames) (ri : RecInfo) :
    recRes (GF := GF) γ ri false = iprop(∃ Q : KvM.Output → IProp GF,
      savedPropOwn ri.post .discard (putReceipt ri.key ri.val Q) ∗
      opAU γ (.put ri.key ri.val) Q) := rfl

theorem recRes_true (γ : CraqNames) (ri : RecInfo) :
    recRes (GF := GF) γ ri true =
      iprop(∃ P : IProp GF, savedPropOwn ri.post .discard P ∗ (P ∨ token ri.col)) := rfl

theorem assign.holds : assign.spec (GF := GF) (G := G) := by
  intro γ E hE n hn k x Q
  iintro ⟨#Hinv, Hnext, HAU⟩
  unfold isCraq
  iinv Hinv with Hi Hclose
  unfold craqInv
  icases Hi with ⟨%l, %L, %n', %R, Habs, HL, Hnext', HR, Hwf, Hels, Hrs⟩
  imod Habs
  imod HL
  imod Hnext'
  imod HR
  imod Hwf with %Hwf
  unfold nextHalf
  ihave %Hn := ghostVar_agree _ _ _ _ _ $$ Hnext Hnext'
  subst Hn
  obtain ⟨hnone, hn1, hcv, Hwf'⟩ := craqWf_assign (n := n) (L := L) (l := l) (R := R) ⟨k, x, 0, 0⟩
    Hwf hn
  imod ghostVar_update_halves (n + W64 1) $$ Hnext Hnext' with ⟨Hnext, Hnext'⟩
  imod saved_prop_alloc (putReceipt k x Q) DFrac.discard DFrac.valid_discard with ⟨%p, #Hsp⟩
  imod token_alloc (GF := GF) with ⟨%c, Htokc⟩
  imod ghost_map_insert_persist (n + W64 1) ((k, x, p, c) : RecInfo) hnone $$ HR with ⟨HR, #Hel⟩
  obtain ⟨-, -, -, Hwf2⟩ := craqWf_assign (n := n) (L := L) (l := l) (R := R) ((k, x, p, c))
    Hwf hn
  imod Hclose $$ [Habs HL Hnext' HR Hels Hrs HAU] with -
  · inext
    iexists l, L, n + W64 1, GMap.insert (n + W64 1) ((k, x, p, c) : RecInfo) R
    iframe Habs HL Hnext' HR
    isplitr
    · ipureintro; exact Hwf2
    isplitl [Hels]
    · iapply (BigSepM.bigSepM_insert (M := GMap w64)
        (show get? R (n + W64 1) = none from hnone)).2
      iframe Hel Hels
    iapply (BigSepM.bigSepM_insert (M := GMap w64)
      (show get? R (n + W64 1) = none from hnone)).2
    iframe Hrs
    have hd : decide (uint.Z (n + W64 1) ≤ uint.Z (cvOf L (RecInfo.key ((k, x, p, c) : RecInfo))))
        = false := by
      have := hcv k
      have e : RecInfo.key ((k, x, p, c) : RecInfo) = k := rfl
      rw [e]; simp only [decide_eq_false_iff_not]; omega
    rw [hd, recRes_false]
    iexists Q
    iframe Hsp HAU
  imodintro
  iframe Hnext
  unfold valsElem ticket
  isplitr
  · iexists p, c; iexact Hel
  iexists p, c
  iframe Hel Hsp Htokc

theorem read_facts {l : List (GoString × GoString)} {L : CLog} {n : w64} {R : GMap w64 RecInfo}
    (Hwf : craqWf l L n R) (k : GoString) :
    (cvOf L k = W64 0 ↔ kvOfPuts l k = none) ∧
      ∀ x, kvOfPuts l k = some x →
        ∃ p c, R.lookup (cvOf L k) = some ((k, x, p, c) : RecInfo) := by
  rw [Hwf.2.1 k]
  unfold absOf
  by_cases h0 : cvOf L k = W64 0
  · simp [h0]
  · obtain ⟨ri, hri, hk⟩ := Hwf.2.2 k h0
    simp only [h0, ↓reduceIte, hri, Option.map_some, reduceCtorEq,
      true_and, Option.some.injEq]
    intro x hx
    obtain ⟨k', x', p, c⟩ := ri
    simp only [RecInfo.key] at hk
    simp only [RecInfo.val] at hx
    subst hk hx
    exact ⟨p, c, rfl⟩

theorem read.holds : read.spec (GF := GF) (G := G) := by
  intro γ E hE L k Q
  have hE' := clientN_sub_diff hE
  iintro ⟨#Hinv, Htok, HAU, Hlc⟩
  unfold isCraq
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later $$ Hlc Hi with Hi
  unfold craqInv
  icases Hi with ⟨%l, %L0, %n, %R, Habs, HL, Hnext, HR, %Hwf, #Hels, Hrs⟩
  unfold tailTok
  ihave %HLL := monoListAuthOwn_agree _ _ _ _ _ $$ Htok HL
  obtain ⟨-, HLL⟩ := HLL
  subst HLL
  imod opAU_commit γ (E \ ↑craqN) hE' (.get k) Q l $$ Habs HAU with ⟨%l', Habs, -, %Hl', HQ⟩
  rw [Hl'.2 k rfl]
  have Hrf := read_facts Hwf k
  imod Hclose $$ [Habs HL Hnext HR Hrs] with -
  · inext
    iexists l, L, n, R
    iframe Habs HL Hnext HR Hels Hrs
    ipureintro; exact Hwf
  imodintro
  iframe Htok
  iexists kvOfPuts l
  isplitl [HQ]
  · iapply (show Q (KvM.stepF (.get k) (kvOfPuts l)).2 ⊢ Q (.got (kvOfPuts l k)) from .rfl) $$ HQ
  unfold readFacts
  isplitr
  · ipureintro; exact Hrf.1
  iintro %x %hx
  obtain ⟨p, c, hR⟩ := Hrf.2 x hx
  unfold valsElem
  iexists p, c
  iapply (BigSepM.bigSepM_lookup (M := GMap w64)
    (show get? R (cvOf L k) = some ((k, x, p, c) : RecInfo) from hR)) $$ Hels

/-- `collect` (two later credits: the invariant's later and the saved proposition's). -/
theorem collect_lc2 (γ : CraqNames) (E : CoPset) (hE : ↑craqN ⊆ E) (v : w64) (k x : GoString)
    (Q : KvM.Output → IProp GF) :
    isCraq (GF := GF) γ ∗ ticket γ v k x Q ∗ cvLb γ k v ∗ £ 2 ={E}=∗ putReceipt k x Q := by
  iintro ⟨#Hinv, Htk, #Hlb, Hlc⟩
  icases (lc_split (n := 1) (m := 1)).1 $$ Hlc with ⟨Hlc1, Hlc2⟩
  unfold ticket
  icases Htk with ⟨%p, %c, #Hel, #Hsp, Htokc⟩
  unfold isCraq
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later $$ Hlc1 Hi with Hi
  unfold craqInv
  icases Hi with ⟨%l, %L, %n, %R, Habs, HL, Hnext, HR, %Hwf, #Hels, Hrs⟩
  ihave %HRv := ghost_map_lookup $$ HR Hel
  ihave %Hle := cvLb_auth γ _ L k v $$ HL Hlb
  icases (BigSepM.bigSepM_delete (M := GMap w64) (show get? R v = some ((k, x, p, c) : RecInfo)
    from HRv)).1 $$ Hrs with ⟨Hr, Hrs⟩
  have hd : decide (uint.Z v ≤ uint.Z (cvOf L (RecInfo.key ((k, x, p, c) : RecInfo)))) = true := by
    simp only [RecInfo.key, decide_eq_true_eq]; exact Hle
  rw [hd, recRes_true]
  icases Hr with ⟨%P, #HP, Hor⟩
  icases Hor with (HPr | Htok2)
  rotate_left
  · iexfalso; iapply token_exclusive $$ Htokc Htok2
  ihave Hag := saved_prop_agree _ _ _ (putReceipt k x Q) P $$ Hsp HP
  imod Hclose $$ [Habs HL Hnext HR Hrs Htokc] with -
  · inext
    iexists l, L, n, R
    iframe Habs HL Hnext HR Hels
    isplitr
    · ipureintro; exact Hwf
    iapply (BigSepM.bigSepM_delete (M := GMap w64) (show get? R v = some ((k, x, p, c) : RecInfo)
      from HRv)).2
    iframe Hrs
    rw [hd, recRes_true]
    iexists P
    iframe HP
    iright
    iexact Htokc
  imod lc_fupd_elim_later $$ Hlc2 Hag with #Hag
  imodintro
  ihave #Hiff := internalEq_iff _ _ $$ Hag
  icases Hiff with ⟨-, H2⟩
  iapply H2
  iexact HPr

theorem collect.holds : collect.spec (GF := GF) (G := G) := collect_lc2

/-- `valsElem_pos`, at the invariant. -/
theorem valsElem_pos_inv (γ : CraqNames) (E : CoPset) (hE : ↑craqN ⊆ E) (v : w64)
    (k x : GoString) :
    isCraq (GF := GF) γ ∗ valsElem γ v k x ={E}=∗ ⌜1 ≤ uint.Z v⌝ := by
  iintro ⟨#Hinv, #Hval⟩
  unfold isCraq
  iinv Hinv with Hi Hclose
  unfold craqInv
  icases Hi with ⟨%l, %L, %n, %R, Habs, HL, Hnext, HR, Hwf, Hels, Hrs⟩
  imod HR
  imod Hwf with %Hwf
  unfold valsElem
  icases Hval with ⟨%p, %c, Hel⟩
  ihave %HRv := ghost_map_lookup $$ HR Hel
  imod Hclose $$ [Habs HL Hnext HR Hels Hrs] with -
  · inext
    iexists l, L, n, R
    iframe
    ipureintro; exact Hwf
  imodintro
  ipureintro
  exact ((Hwf.1 v).1 (by simp [HRv])).1

theorem valsElem_pos.holds : valsElem_pos.spec (GF := GF) (G := G) := valsElem_pos_inv

end laws

end github_com.despreston.go_craq

end Perennial
