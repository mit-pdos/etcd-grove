/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Ghost/Impl/Client.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`; the client's atomic update is remote's one-shot update (`AUof`).
-/
/-
`ghost_register` and `ghost_retrieve`'s implementation: a client registers its request with its
atomic update (the registry and a request invariant), and retrieves the update's result with its
ticket once a reply shows the request linearized.
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

/-- `ghost_register` over the implementation's names. -/
theorem ghost_register_impl (g : GN) (E : CoPset) (hE : ↑sysNI ⊆ E) (hR : ↑regNI ⊆ E)
    (N c n : Nat) (i : KvInI) (hi : InputOk i) (hb : RegBound c n i)
    (Q : Store → Store → KvOutI → IProp GF) :
    factI g (.size N) -∗ sysInvI g -∗ regInvI g -∗ nextReqI g c n -∗
      AUof g i Q ={E}=∗
      nextReqI g c (n + 1) ∗ factI g (.msg (.request n c (encOp i))) ∗ ticketI g c n i Q := by
  have hsr := sysNI_regNI_disj
  have h1 := regInvN_sub
  iintro #Hsize #Hsys #Hreg Hn HAU
  unfold sysInvI regInvI
  iinv Hsys with >Hb Hclose
  iunfold sysBody, sysAt at Hb
  icases Hb with ⟨%s, %F, %R, %N, %M, %hInv, HF, %hF, HFs, HR, %hR, Habs, HN, %hN, HM, %hM, HMs,
    Hsz⟩
  -- the size fact: the system is sized (its token)
  ihave %hFn := Perennial.ghost_map_lookup $$ HF Hsize
  ihave Htok := sized_of_lookup g F M s hFn $$ Hsz
  ihave %hNc := Perennial.ghost_map_lookup $$ HN Hn
  have hreg0 : s.reg c n = none := hN c n hNc n (Nat.le_refl _)
  have hMk : M !! (c, n) = none := by
    have := hM c n
    rw [hreg0] at this
    cases h : M !! (c, n) with
    | none => rfl
    | some _ => rw [h] at this; cases this
  obtain ⟨hInv', hLe⟩ := stepRegister_inv s c n i hInv hreg0 hi hb
  have hnotin : StatusOk s.lin c n none := by
    intro e he ⟨hc, hn⟩
    obtain ⟨i', hi', -⟩ := hInv.2.2.2.2.2.2.2.2.2.1 e he
    rw [hc, hn, hreg0] at hi'
    cases hi'
  iinv Hreg with Hrb Hrclose
  iunfold regBody at Hrb
  icases Hrb with ⟨%M', >HM', HMr⟩
  ihave %hMM := ghostMapAuth_agree g.regm _ _ M M' $$ HM HM'
  subst hMM
  -- the request's ghost state: its status, its ticket, its pending token, its invariant
  imod ghostVar_alloc (none : Option GoString) with ⟨%γs, Hγs⟩
  icases (ghostVar_split_half γs 1 (none : Option GoString)).1 $$ Hγs with ⟨Hγs1, Hγs2⟩
  imod token_alloc with ⟨%γt, Ht⟩
  imod token_alloc with ⟨%γp, Hp⟩
  imod inv_alloc (reqNI (c, n)) _ (reqInv i Q γs γt) $$ [Hγs2] with #HI
  · inext
    unfold reqInv
    iexists none
    iframe
    unfold reqBody
    iempintro
  -- the registry's map
  ihave HMf := (ghostMapAuth_halves g.regm M).2 $$ [HM HM']
  · iframe
  imod Perennial.ghost_map_insert_persist (c, n) ((γs, γt, γp, i) : RegVal) hMk $$ HMf with ⟨HMf, #Hel⟩
  icases (ghostMapAuth_halves g.regm _).1 $$ HMf with ⟨HM, HM'⟩
  -- the counter
  imod Perennial.ghost_map_update (n + 1) $$ HN Hn with ⟨HN, Hn⟩
  -- the request's fact
  imod facts_add g (stepRegister s c n i) [.msg (.request n c (encOp i))]
    (by
      intro f hf
      simp only [List.mem_singleton] at hf
      subst hf
      exact ⟨i, by simp [stepRegister], rfl⟩) F
    (fun f u h => holds_mono hLe f (hF f u h)) $$ HF HFs with ⟨%F', HF, %hF', HFs, Hfs⟩
  imod Hrclose $$ [HM' HMr HAU] with -
  · inext
    unfold regBody
    iexists _
    iframe HM'
    iapply (BigSepM.bigSepM_insert (m := M) (Φ := fun q y => regEntry g q y) hMk).2
    iframe HMr
    unfold regEntry
    ileft
    iexists Q
    iframe HI
    unfold AUof
    iexact HAU
  ihave Hsz : sizedI g F' (<[(c, n) := ((γs, γt, γp, i) : RegVal)]> M) (stepRegister s c n i)
    $$ [Htok]
  · iunfold sizedI; iright; iexact Htok
  imod Hclose $$ [HF HFs HR Habs HN HM HMs Hγs1 Hp Hsz] with -
  · inext
    unfold sysBody sysAt
    iexists (stepRegister s c n i), F', R, (<[c := n + 1]> N),
      (<[(c, n) := ((γs, γt, γp, i) : RegVal)]> M)
    isplitr
    · ipureintro; exact hInv'
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
    rw [stepRegister_lin]
    isplitl [Habs]
    · iexact Habs
    isplitl [HN]
    · iexact HN
    isplitr
    · ipureintro
      intro c' m hm n' hn'
      simp only [GMap.lookup_insert_eq_iff] at hm
      simp only [stepRegister]
      split at hm
      · subst_vars
        cases hm
        have : n' ≠ n := by omega
        simp only [true_and, this, ite_false]
        exact hN c' n hNc n' (by omega)
      · rename_i hcc
        have : ¬ (c' = c ∧ n' = n) := fun h => hcc h.1.symm
        simp only [this, ite_false]
        exact hN c' m hm n' hn'
    isplitl [HM]
    · iexact HM
    isplitr
    · ipureintro
      intro c' n'
      simp only [GMap.lookup_insert_eq_iff, stepRegister]
      by_cases h : c' = c ∧ n' = n
      · obtain ⟨rfl, rfl⟩ := h; simp
      · have : ¬ ((c, n) = (c', n')) := fun h' => h (by cases h'; exact ⟨rfl, rfl⟩)
        simp only [h, this, ite_false]
        exact hM c' n'
    isplitr [Hsz]
    rotate_left
    · iexact Hsz
    iapply (BigSepM.bigSepM_insert (m := M) (Φ := fun q y => sysEntry s.lin q y) hMk).2
    iframe HMs
    unfold sysEntry
    iexists none
    iframe
    isplit
    · ipureintro; exact hnotin
    · unfold pendTok; iexact Hp
  imodintro
  iframe Hn
  icases Hfs with ⟨Hf, -⟩
  iframe Hf
  unfold ticketI
  iexists γs, γt, γp
  isplitr
  · iexact Hel
  isplitl [Ht]
  · iexact Ht
  · iexact HI

/-- `ghost_retrieve` over the implementation's names. -/
theorem ghost_retrieve_impl (g : GN) (E : CoPset) (hR : ↑regNI ⊆ E) (hE : ↑sysNI ⊆ E)
    (c n v : Nat) (i : KvInI) (Q : Store → Store → KvOutI → IProp GF) (res : GoString) :
    £ 1 -∗ sysInvI g -∗ regInvI g -∗ ticketI g c n i Q -∗
      factI g (.msg (.reply n c v res)) ={E}=∗
      ∃ σ σ', Q σ σ' (outOfReplyI i res) ∗
        ⌜kvStep σ i σ' (outOfReplyI i res)⌝ := by
  have hsr := sysNI_regNI_disj
  have h2 := reqNI_sub
  iintro Hlc #Hsys #_ Ht #Hf
  unfold ticketI
  icases Ht with ⟨%γs, %γt, %γp, #Hel, Ht, #HI⟩
  unfold sysInvI
  iinv Hsys with >Hb Hclose
  iunfold sysBody, sysAt at Hb
  icases Hb with ⟨%s, %F, %R, %N, %M, %hInv, HF, %hF, HFs, HR, %hR, Habs, HN, %hN, HM, %hM, HMs, Hsz⟩
  ihave %hrep := fact_holds g s F hF _ $$ HF Hf
  ihave %hMk := Perennial.ghost_map_lookup $$ HM Hel
  icases (BigSepM.bigSepM_lookup_acc (m := M) (Φ := fun q y => sysEntry s.lin q y) hMk).1 $$ HMs
    with ⟨Hse, HMs⟩
  iunfold sysEntry at Hse
  icases Hse with ⟨%st, Hγs, %hst, Hpt⟩
  have hst' : st = some res := statusOk_reply hInv.2.2.2.2.2.2.2.2.1 hrep st hst
  subst hst'
  iinv HI with Hb Hiclose
  imod lc_fupd_elim_later $$ Hlc Hb with Hb
  iunfold reqInv at Hb
  icases Hb with ⟨%st', Hγs', Hb⟩
  icombine Hγs Hγs' gives % ⟨-, hst'⟩
  subst hst'
  iunfold reqBody at Hb
  icases Hb with (Hd | Ht')
  · imod Hiclose $$ [Hγs' Ht] with -
    · inext
      unfold reqInv
      iexists _
      iframe Hγs'
      unfold reqBody
      iright
      iexact Ht
    ispecialize HMs $$ [Hγs Hpt]
    · unfold sysEntry
      iexists _
      iframe
      ipureintro; exact hst
    imod Hclose $$ [HF HFs HR Habs HN HM HMs Hsz] with -
    · unfold sysBody sysAt
      iexists s, F, R, N, M
      iframe
      ipureintro
      exact ⟨hInv, hF, hR, hN, hM⟩
    imodintro
    unfold Done
    icases Hd with ⟨%σ, %σ', HQ, %hstep⟩
    iexists σ, σ'
    iframe
    ipureintro; exact hstep
  · iexfalso
    iapply token_exclusive $$ Ht Ht'

end proofs

end VsrGhost.Impl
