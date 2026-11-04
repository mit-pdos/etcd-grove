/-
**The sync token's trade** with the work queue's key token, inside `s1Inv` (the worker's
`processNextWorkItem`, `S1Inv.lean`'s header). Lean-first; the autoverify run's glue proofs,
track B.

* `s1Inv_take`: the queue's token of the owner's canonical key in, the owner's sync token out
  (registering the owner on its first sync: `register_step`);
* `s1Inv_give`: the sync token back in, the queue's token out (for `Done`).
-/
module

public import Proof.k8s_io.kubernetes.pkg.controller.daemon.S1Inv
public import Spec.k8s_io.kubernetes.pkg.controller.daemon.DaemonSetsController__syncDaemonSet

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI Iris.ProofMode apimodel informer consistency workqueue

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

instance seenTok_timeless (γ : S1Names) (o : Owner) (Lr : Nat × Bool) :
    Timeless (seenTok (GF := GF) γ o Lr) := by unfold seenTok; infer_instance
instance ownerTok_timeless (c : DscComp) (o : Owner) (q : Qp) :
    Timeless (ownerTok (GF := GF) c o q) := by unfold ownerTok; infer_instance
instance syncTok_timeless (γ : S1Names) (c : DscComp) (o : Owner) :
    Timeless (syncTok (GF := GF) γ c o) := by unfold syncTok; infer_instance
instance keyTok_timeless' (γq : QNames) (k : GoString) :
    Timeless (keyTok (GF := GF) γq k) := by unfold keyTok; infer_instance
instance infRvLb_timeless (γi : InfNames) (n : Nat) :
    Timeless (infRvLb (GF := GF) γi n) := by unfold infRvLb; infer_instance
instance apiMirror_timeless (γ : S1Names) (σ : St) :
    Timeless (apiMirror (GF := GF) γ σ) := by unfold apiMirror; infer_instance

instance consState_timeless' (γc : ConsNames) (M : GMap Owner consistency.Rec) :
    Timeless (consState (GF := GF) γc M) := by unfold consState; infer_instance
instance s1Entry_timeless (γ : S1Names) (c : DscComp) (o : Owner) (Lr : Nat × Bool) :
    Timeless (s1Entry (GF := GF) γ c o Lr) := by unfold s1Entry; infer_instance
instance claimDep_timeless (c : DscComp) (on : Owner × GoString) :
    Timeless (claimDep (GF := GF) c on) := by unfold claimDep; infer_instance
instance entries_timeless (γ : S1Names) (c : DscComp) (Lm : GMap Owner (Nat × Bool)) :
    Timeless ([∗map] o ↦ Lr ∈ Lm, s1Entry (GF := GF) γ c o Lr) :=
  BigSepM.bigSepM_timeless (fun _ => inferInstance)
instance claimDeps_timeless (c : DscComp) (C : Claims) :
    Timeless ([∗map] on ↦ _v ∈ C, claimDep (GF := GF) c on) :=
  BigSepM.bigSepM_timeless (fun _ => inferInstance)

instance s1Res_timeless (γ : S1Names) (c : DscComp) : Timeless (s1Res (GF := GF) γ c) := by
  unfold s1Res
  infer_instance

theorem keyTok_excl2 (γq : DNames) (k : GoString) :
    keyTok (GF := GF) γq.tq k ∗ keyTok γq.tq k ⊢ False := by
  unfold keyTok
  iintro ⟨H1, H2⟩
  ihave %Hv := ghostMapElem_valid_2 (K := GoString) k γq.tq.proc (DFrac.own 1) (DFrac.own 1)
    _ _ $$ H1 H2
  exact absurd (DFrac.valid_own_op Hv.1) (by simp)

theorem ownerTok_excl2 (c : DscComp) (o : Owner) (q : Qp) :
    ownerTok (GF := GF) c o 1 ∗ ownerTok c o q ⊢ False := by
  unfold ownerTok
  iintro ⟨H1, H2⟩
  ihave %Hv := ghostMapElem_valid_2 (K := Owner) (V := Unit) o c.tok (DFrac.own 1) (DFrac.own q)
    () () $$ H1 H2
  exact absurd (DFrac.valid_own_op Hv.1) (by simp)

/-- **The worker takes the owner's sync token**, giving the queue's token of its key. -/
theorem s1Inv_take (γ : S1Names) (c : DscComp) (o : Owner) :
    s1Inv (GF := GF) γ c ∗ keyTok c.γq.tq (ownerKey o) ⊢ |={⊤}=> syncTok γ c o := by
  iintro ⟨#Hinv, Hk⟩
  iunfold s1Inv at Hinv
  iinv Hinv with >Hres Hclose
  iunfold s1Res at Hres
  icases Hres with ⟨%σ, %M, %Lm, %C, %D, %Ld, Hm, Hcs, Hta, %HD, Hlb, Hents, Hca, Hcl, #HLd,
    %Hok⟩
  cases hL : Lm !! o with
  | some Lr =>
    icases (BigSepM.bigSepM_delete (Φ := fun o Lr => s1Entry (GF := GF) γ c o Lr) hL).1 $$ Hents
      with ⟨Hent, Hrest⟩
    iunfold s1Entry at Hent
    icases Hent with ⟨Hs, #Hlb0, Hor⟩
    icases Hor with (Hst | Hk2)
    · imod Hclose $$ [Hm Hcs Hta Hlb Hca Hcl Hs Hrest Hk] with -
      · inext
        iunfold s1Res
        iexists σ, M, Lm, C, D, Ld
        isplitl [Hm]; · iexact Hm
        isplitl [Hcs]; · iexact Hcs
        isplitl [Hta]; · iexact Hta
        isplitr; · ipureintro; exact HD
        isplitl [Hlb]; · iexact Hlb
        isplitl [Hs Hrest Hk]
        · iapply (BigSepM.bigSepM_delete (Φ := fun o Lr => s1Entry (GF := GF) γ c o Lr) hL).2
          isplitl [Hs Hk]
          · iunfold s1Entry
            isplitl [Hs]; · iexact Hs
            isplitr; · iexact Hlb0
            iright; iexact Hk
          · iexact Hrest
        isplitl [Hca]; · iexact Hca
        isplitl [Hcl]; · iexact Hcl
        isplitr; · iexact HLd
        ipureintro; exact Hok
      imodintro
      iexact Hst
    · iexfalso
      iapply keyTok_excl2 $$ [Hk Hk2]
      iframe
  | none =>
    have hD : D.lookup o = none := by
      have := HD o
      rw [hL] at this
      simpa using this
    imod (ghost_map_insert (K := Owner) (V := Unit) (γ := c.tok) o () hD) $$ Hta with ⟨Hta, Htok⟩
    imod (ghost_map_insert (K := Owner) (V := Nat × Bool) (γ := γ.lb) o (0, false) hL) $$ Hlb
      with ⟨Hlb, Hseen⟩
    icases (ghostMapElem_halves (K := Owner) (V := Nat × Bool) γ.lb o (0, false)).1 $$ Hseen
      with ⟨Hs1, Hs2⟩
    imod (monoNatLbOwn_0 (GF := GF) c.podI.γi.rvlb) with #H0
    imod Hclose $$ [Hm Hcs Hta Hlb Hca Hcl Hents Hs1 Hk] with -
    · inext
      iunfold s1Res
      iexists σ, M, <[o := (0, false)]> Lm, C, <[o := ()]> D, Ld
      isplitl [Hm]; · iexact Hm
      isplitl [Hcs]; · iexact Hcs
      isplitl [Hta]; · iexact Hta
      isplitr
      · ipureintro
        intro o'
        by_cases e : o = o'
        · subst e; simp
        · simp only [GMap.lookup_insert_eq_iff, e, ↓reduceIte]
          exact HD o'
      isplitl [Hlb]; · iexact Hlb
      isplitl [Hents Hs1 Hk]
      · iapply (BigSepM.bigSepM_insert (Φ := fun o Lr => s1Entry (GF := GF) γ c o Lr) hL).2
        isplitl [Hs1 Hk]
        · iunfold s1Entry
          isplitl [Hs1]; · iunfold seenTok; iexact Hs1
          isplitr; · iunfold infRvLb; iexact H0
          iright; iexact Hk
        · iexact Hents
      isplitl [Hca]; · iexact Hca
      isplitl [Hcl]; · iexact Hcl
      isplitr; · iexact HLd
      ipureintro
      exact register_step σ M Lm C Ld o Hok hL
    imodintro
    iunfold syncTok
    isplitl [Htok]; · iunfold ownerTok; iexact Htok
    iexists (0, false)
    iunfold seenTok
    iexact Hs2

/-- **The worker gives the sync token back**, taking the queue's token of its key. -/
theorem s1Inv_give (γ : S1Names) (c : DscComp) (o : Owner) :
    s1Inv (GF := GF) γ c ∗ syncTok γ c o ⊢ |={⊤}=> keyTok c.γq.tq (ownerKey o) := by
  iintro ⟨#Hinv, Hst⟩
  iunfold s1Inv at Hinv
  iinv Hinv with >Hres Hclose
  iunfold s1Res at Hres
  icases Hres with ⟨%σ, %M, %Lm, %C, %D, %Ld, Hm, Hcs, Hta, %HD, Hlb, Hents, Hca, Hcl, #HLd,
    %Hok⟩
  iunfold syncTok at Hst
  icases Hst with ⟨Htok, Hseen⟩
  iunfold ownerTok at Htok
  ihave %HDo := (ghost_map_lookup (K := Owner) (V := Unit) (γ := c.tok)) $$ Hta Htok
  have hL : (Lm !! o).isSome := by
    have := HD o
    rw [← this]
    show (D.lookup o).isSome = true
    rw [HDo]; rfl
  obtain ⟨Lr, hLr⟩ := Option.isSome_iff_exists.mp hL
  icases (BigSepM.bigSepM_delete (Φ := fun o Lr => s1Entry (GF := GF) γ c o Lr) hLr).1 $$ Hents
    with ⟨Hent, Hrest⟩
  iunfold s1Entry at Hent
  icases Hent with ⟨Hs, #Hlb0, Hor⟩
  icases Hor with (Hst2 | Hk)
  · iunfold syncTok at Hst2
    icases Hst2 with ⟨Htok2, -⟩
    iexfalso
    iapply (ownerTok_excl2 c o 1)
    iunfold ownerTok
    iunfold ownerTok at Htok2
    isplitl [Htok]
    · iexact Htok
    · iexact Htok2
  · imod Hclose $$ [Hm Hcs Hta Hlb Hca Hcl Hs Hrest Htok Hseen] with -
    · inext
      iunfold s1Res
      iexists σ, M, Lm, C, D, Ld
      isplitl [Hm]; · iexact Hm
      isplitl [Hcs]; · iexact Hcs
      isplitl [Hta]; · iexact Hta
      isplitr; · ipureintro; exact HD
      isplitl [Hlb]; · iexact Hlb
      isplitl [Hs Hrest Htok Hseen]
      · iapply (BigSepM.bigSepM_delete (Φ := fun o Lr => s1Entry (GF := GF) γ c o Lr) hLr).2
        isplitl [Hs Htok Hseen]
        · iunfold s1Entry
          isplitl [Hs]; · iexact Hs
          isplitr; · iexact Hlb0
          ileft
          iunfold syncTok
          isplitl [Htok]; · iunfold ownerTok; iexact Htok
          iexact Hseen
        · iexact Hrest
      isplitl [Hca]; · iexact Hca
      isplitl [Hcl]; · iexact Hcl
      isplitr; · iexact HLd
      ipureintro; exact Hok
    imodintro
    iexact Hk

/-- A canonical key's owner has it as its key. -/
theorem ownerKey_of_canon {key : GoString} {o : Owner} (h : keyCanon key)
    (ho : ownerOf key = some o) : ownerKey o = key := by
  unfold ownerOf at ho
  cases hs : cache.splitKey key with
  | none => rw [hs] at ho; cases ho
  | some p =>
    rw [hs] at ho
    simp only [Option.map_some, Option.some.injEq] at ho
    subst ho
    exact h p.1 p.2 hs

/-- **The worker's trade for a key** the queue handed out (canonical): the sync token of the key's
owner, if any, and the way back to the queue's token. -/
theorem s1Inv_trade (γ : S1Names) (c : DscComp) (key : GoString) (hcan : keyCanon key) :
    s1Inv (GF := GF) γ c ∗ keyTok c.γq.tq key ⊢
      |={⊤}=> keySyncTok γ c key ∗ (keySyncTok γ c key -∗ |={⊤}=> keyTok c.γq.tq key) := by
  iintro ⟨#Hinv, Hk⟩
  cases ho : ownerOf key with
  | none =>
    simp only [keySyncTok, ho]
    imodintro
    isplitr
    · itrivial
    · iintro _
      imodintro
      iexact Hk
  | some o =>
    have hok := ownerKey_of_canon hcan ho
    subst hok
    simp only [keySyncTok, ho]
    imod s1Inv_take γ c o $$ [Hinv Hk] with Hst
    · iframe #; iframe
    imodintro
    iframe
    iintro Hst
    iapply s1Inv_give γ c o
    iframe #; iframe

end lemmas

end dsctl
end EtcdGrove
end Perennial
