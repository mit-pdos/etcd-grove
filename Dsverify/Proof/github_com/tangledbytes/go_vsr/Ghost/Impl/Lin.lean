/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Ghost/Impl/Lin.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`; the client's atomic update is remote's one-shot update (`AUof`).
-/
/-
`ghost_lin`'s implementation: the linearization point (helping). The replica executing op `k`
first anywhere commits the client's atomic update, found in the registry.
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

/-- An entry other than the new one keeps its status when the log grows by `e`. -/
theorem sysEntry_snoc (lin : List Entry) (e : Entry) (k : Nat × Nat) (x : RegVal)
    (hk : k ≠ (e.cid, e.req)) :
    sysEntry (GF := GF) lin k x ⊢ sysEntry (lin ++ [e]) k x := by
  unfold sysEntry
  iintro ⟨%st, Hv, %hst, Hp⟩
  iexists st
  iframe
  ipureintro
  exact statusOk_snoc (fun h => hk (by rw [h.1, h.2])) st hst

/-- The commit at the linearization point: the log grows by `e`, the entry of registered request
`(e.cid, e.req)` (pending), whose atomic update the registry holds; it is committed (the abstract
state takes the step) and its result goes to the request's invariant. -/
theorem lin_commit (g : GN) (E' : CoPset) (lin : List Entry) (e : Entry)
    (hC : ⊤ \ vsrE ⊆ E') (hQ : ↑(reqNI (e.cid, e.req)) ⊆ E')
    (M : GMap (Nat × Nat) RegVal) (x : RegVal)
    (hMk : M !! (e.cid, e.req) = some x)
    (hnew : ∀ e' ∈ lin, (e'.cid, e'.req) ≠ (e.cid, e.req))
    (hstep : kvStep (storeOf lin) x.2.2.2 (storeOf (lin ++ [e]))
      (outOfReplyI x.2.2.2 (outOf (lin ++ [e]) lin.length))) :
    ghostVar g.abs (1 : Qp).half lin -∗ ([∗map] k ↦ y ∈ M, sysEntry lin k y) -∗
      ([∗map] k ↦ y ∈ M, regEntry g k y) ={E'}=∗
      ghostVar g.abs (1 : Qp).half (lin ++ [e]) ∗
      ([∗map] k ↦ y ∈ M, sysEntry (lin ++ [e]) k y) ∗ ([∗map] k ↦ y ∈ M, regEntry g k y) := by
  iintro Habs HMs HMr
  icases (BigSepM.bigSepM_delete (Φ := fun k y => sysEntry lin k y) hMk).1 $$ HMs with ⟨Hse, HMs⟩
  icases (BigSepM.bigSepM_delete (Φ := fun k y => regEntry g k y) hMk).1 $$ HMr with ⟨Hre, HMr⟩
  iunfold sysEntry at Hse
  icases Hse with ⟨%st, Hγs, %hst, Hpt⟩
  have hst0 : st = none := by
    cases st with
    | none => rfl
    | some r =>
      exfalso
      obtain ⟨j, e', hj, hc, hn, -⟩ := hst
      exact hnew e' (List.mem_of_getElem? hj) (by simp [hc, hn])
  subst hst0
  isimp only [pendTok] at Hpt
  iunfold regEntry at Hre
  icases Hre with (⟨%Q, HAU, #HI⟩ | Hpt')
  · iunfold AUof at HAU
    imod fupd_mask_subseteq (PROP := IProp GF) hC with Hmask
    imod HAU with ⟨%σ, Hσ, Hcommit⟩
    iunfold absOwnI at Hσ
    icases Hσ with ⟨%L, HL, %hL⟩
    icombine Habs HL gives % ⟨-, hLeq⟩
    subst hLeq hL
    imod ghostVar_update_halves (lin ++ [e]) g.abs lin lin $$ Habs HL with ⟨Habs, HL⟩
    imod Hcommit $$ %(storeOf (lin ++ [e])) %(outOfReplyI x.2.2.2 (outOf (lin ++ [e]) lin.length)) [HL] with HQ
    · iunfold absOwnI
      isplitl [HL]
      · iexists _; iframe; ipureintro; rfl
      · ipureintro; exact hstep
    imod Hmask
    iinv HI with Hb Hiclose
    iunfold reqInv at Hb
    icases Hb with ⟨%st', >Hγs', Hb⟩
    icombine Hγs Hγs' gives % ⟨-, hst'⟩
    subst hst'
    imod ghostVar_update_halves (some (outOf (lin ++ [e]) lin.length)) x.1 none none $$ Hγs Hγs'
      with ⟨Hγs, Hγs'⟩
    imod Hiclose $$ [Hγs' HQ] with -
    · inext
      unfold reqInv
      iexists _
      iframe
      unfold reqBody
      ileft
      unfold Done
      iexists _, _
      iframe
      ipureintro; exact hstep
    imodintro
    iframe Habs
    isplitl [HMs Hγs]
    · iapply (BigSepM.bigSepM_delete (Φ := fun k y => sysEntry (lin ++ [e]) k y) hMk).2
      isplitl [Hγs]
      · unfold sysEntry
        iexists _
        iframe
        isplit
        · ipureintro; exact statusOk_new lin e
        · unfold pendTok; iempintro
      · iapply BigSepM.bigSepM_mono _ $$ HMs
        intro k y hk
        apply sysEntry_snoc
        intro h; subst h
        change GMap.lookup (GMap.delete (e.cid, e.req) M) (e.cid, e.req) = some y at hk
        rw [GMap.lookup_delete] at hk; cases hk
    · iapply (BigSepM.bigSepM_delete (Φ := fun k y => regEntry g k y) hMk).2
      iframe HMr
      unfold regEntry
      iright
      iexact Hpt
  · iexfalso
    iapply token_exclusive $$ Hpt Hpt'

/-- The ghost update of `stepLin`: the abstract state and the registered requests' statuses follow
the linearized log (and, if it grows, the new entry's request is committed). -/
theorem lin_update (g : GN) (E' : CoPset) (hC : ⊤ \ vsrE ⊆ E') (hQ : ∀ k, ↑(reqNI k) ⊆ E')
    (s : Sys) (l mine : List Entry) (k : Nat) (h : Inv s) (hc : Committed s l)
    (hkl : k ≤ l.length) (hmine : mine <+: s.lin) (hml : mine <+: l) (hlen : mine.length + 1 = k)
    (e : Entry) (he : l[k - 1]? = some e) (M : GMap (Nat × Nat) RegVal)
    (hM : ∀ c n, s.reg c n = (M !! (c, n)).map (fun v => v.2.2.2)) :
    ghostVar g.abs (1 : Qp).half s.lin -∗ ([∗map] q ↦ y ∈ M, sysEntry s.lin q y) -∗
      ([∗map] q ↦ y ∈ M, regEntry g q y) ={E'}=∗
      ghostVar g.abs (1 : Qp).half (stepLin s l k).lin ∗
      ([∗map] q ↦ y ∈ M, sysEntry (stepLin s l k).lin q y) ∗
      ([∗map] q ↦ y ∈ M, regEntry g q y) := by
  by_cases hgrow : s.lin.length < k
  · obtain ⟨hInv', -, -⟩ := stepLin_inv s l mine k h hc hkl hmine hml hlen
    -- the new entry is registered
    have hmem : e ∈ (stepLin s l k).lin := by
      have hpre := (stepLin_inv s l mine k h hc hkl hmine hml hlen).2.2
      have h1 : (l.take k)[k - 1]? = some e := by
        rw [List.getElem?_take_of_lt (by omega)]; exact he
      exact List.mem_of_getElem? (prefix_getElem? hpre h1)
    obtain ⟨i, hi, -⟩ := hInv'.2.2.2.2.2.2.2.2.2.1 e hmem
    rw [stepLin_reg] at hi
    obtain ⟨hlin', hnew, habs', hout'⟩ := stepLin_kv s l mine k h hc hkl hmine hml hlen hgrow e he i hi
    have hMk : ∃ x : RegVal, M !! (e.cid, e.req) = some x ∧ x.2.2.2 = i := by
      rw [hM] at hi
      cases hx : M !! (e.cid, e.req) with
      | none => rw [hx] at hi; cases hi
      | some x => rw [hx] at hi; exact ⟨x, rfl, Option.some.inj hi⟩
    obtain ⟨x, hMk, rfl⟩ := hMk
    rw [hlin']
    iapply lin_commit g E' s.lin e hC (hQ _) M x hMk hnew
    have hσ := kv_step_svc (absState s) x.2.2.2 (storeOk_inv s h)
    rw [← habs', ← hout'] at hσ
    simpa [absState, hlin'] using hσ
  · rw [stepLin_same s l k hgrow]
    iintro Habs HMs HMr
    imodintro
    iframe

/-- `ghost_lin` over the implementation's names. -/
theorem ghost_lin_impl (g : GN) (E : CoPset) (hE : ↑sysNI ⊆ E) (hR : ↑regNI ⊆ E)
    (hC : ⊤ \ vsrE ⊆ E) (hd : ↑sysNI ∩ ↑regNI = (∅ : CoPset))
    (l mine : List Entry) (k : Nat) (e : Entry)
    (hk : mine.length + 1 = k) (hml : mine <+: l) (he : l[k - 1]? = some e) (v w : Nat) :
    £ 1 -∗ sysInvI (GF := GF) g -∗ regInvI g -∗ factI g (.committedBy w l) -∗
      factI g (.linPrefix mine) ={E}=∗
      factI g (.linPrefix (l.take k)) ∗
      factI g (.msg (.reply e.req e.cid v (outOf (l.take k) (k - 1)))) := by
  have hkl : k ≤ l.length := by have := (List.getElem?_eq_some_iff.mp he).1; omega
  have hd' := mask_disj_of_inter hd
  have h1 := regInvN_sub
  have h2 := reqNI_sub
  have h3 := reqNI_regInvN_disj
  have h4 := sysNI_vsrE
  have h5 := regNI_vsrE
  iintro Hlc #Hsys #Hreg #Hc #Hm
  unfold sysInvI regInvI
  iinv Hsys with >Hb Hclose
  iunfold sysBody, sysAt at Hb
  icases Hb with ⟨%s, %F, %R, %N, %M, %hInv, HF, %hF, HFs, HR, %hR, Habs, HN, %hN, HM, %hM, HMs, Hsz⟩
  -- the committedBy fact: the system is sized (its token)
  ihave %hFc := Perennial.ghost_map_lookup $$ HF Hc
  ihave Htok := sized_of_lookup g F M s hFc $$ Hsz
  ihave %hcb := fact_holds g s F hF _ $$ HF Hc
  ihave %hmi := fact_holds g s F hF _ $$ HF Hm
  have hcl : Committed s l := committed_of_by s w l hcb
  obtain ⟨hInv', hLe, hpre⟩ := stepLin_inv s l mine k hInv hcl hkl hmi hml hk
  have hf2 : Holds (stepLin s l k) (.msg (.reply e.req e.cid v (outOf (l.take k) (k - 1)))) := by
    have hlt : k - 1 < (l.take k).length := by simp; omega
    refine ⟨k - 1, e, ?_, rfl, rfl, outOf_prefix hpre hlt⟩
    have h1 : (l.take k)[k - 1]? = some e := by
      rw [List.getElem?_take_of_lt (by omega)]; exact he
    exact prefix_getElem? hpre h1
  iinv Hreg with Hrb Hrclose
  imod lc_fupd_elim_later $$ Hlc Hrb with Hrb
  iunfold regBody at Hrb
  icases Hrb with ⟨%M', HM', HMr⟩
  ihave %hMM := ghostMapAuth_agree g.regm _ _ M M' $$ HM HM'
  subst hMM
  imod lin_update g _ (by solve_ndisj) (fun k => by solve_ndisj) s l mine k hInv hcl hkl hmi hml hk
    e he M hM $$ Habs HMs HMr with ⟨Habs, HMs, HMr⟩
  imod facts_add g (stepLin s l k) [.linPrefix (l.take k),
      .msg (.reply e.req e.cid v (outOf (l.take k) (k - 1)))]
    (by intro f hf; simp at hf; rcases hf with rfl | rfl; exact hpre; exact hf2) F
    (fun f u h => holds_mono hLe f (hF f u h)) $$ HF HFs with ⟨%F', HF, %hF', HFs, Hfs⟩
  imod Hrclose $$ [HM' HMr] with -
  · inext
    unfold regBody
    iexists M
    iframe
  ihave Hsz : sizedI g F' M (stepLin s l k) $$ [Htok]
  · iunfold sizedI; iright; iexact Htok
  imod Hclose $$ [HF HFs HR Habs HN HM HMs Hsz] with -
  · unfold sysBody sysAt
    iexists (stepLin s l k), F', R, N, M
    rw [stepLin_reps, stepLin_reg]
    iframe
    ipureintro
    exact ⟨hInv', hF', hR, hN, hM⟩
  imodintro
  icases Hfs with ⟨Hf1, Hf2, -⟩
  iframe

end proofs

end VsrGhost.Impl
