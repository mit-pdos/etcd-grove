/-
Lemmas on the request ids (`Defs.lean`): claiming an id for a request's data, the claims'
agreement, and the slots' exclusivity. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.idutil.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **Claiming an id** of the incarnation's prefix for the data `d` with the ghost name `γf`, given
the claimer's fact `□ Φ id d γf`: its element of the cluster's issued map goes from `none` to
`some (d, γf, key)`, read-only from then on, and the fact is kept in the cluster's claims invariant
under the claimer's key, whose facts are the generator's `Φ` (D21e (A); by key since R2c). -/
theorem idClaim_make (γi : IdNames) (g : Loc) (Φ : w64 → List w8 → GName → IProp GF) (id : w64)
    (d : List w8) (γf : GName) (E : CoPset) (HE : ↑idClusterN ⊆ E) :
    ⊢ idGen (GF := GF) γi g Φ -∗ idUnclaimed γi id -∗ ⌜idPfx id = γi.pfx⌝ -∗ □ Φ id d γf ={E}=∗
      idClaim γi id d γf := by
  iintro #Hg Hu %Hp #HΦ
  iunfold idGen at Hg
  icases Hg with ⟨%s0, %Hgn, #Hpfx, %Hs0, #Hinv, %X, %hX, %Φs, %x, %HΦx, #Hkf, #Hcl⟩
  iunfold idClusterInv at Hcl
  iinv Hcl with Hi Hclose
  icases Hi with ⟨%I, %C, %R, %Fm, >HI, >HC, >HR, >HF, >%Hok, #HFs, #HG⟩
  iunfold idUnclaimed at Hu
  icombine HI Hu gives %Hlk
  have Hlk' : I.lookup id = some none := Hlk
  imod ghost_map_update (some (d, γf, γi.key)) $$ HI Hu with ⟨HI, Hu⟩
  imod ghostMapElem_persist $$ Hu with Hu
  imod Hclose $$ [HI HC HR HF] with -
  · inext
    iexists (I.insert id (some (d, γf, γi.key))), C, R, Fm
    iframe HI HC HR HF HG
    isplitr
    · ipureintro
      refine ⟨fun id' => ?_, Hok.2⟩
      rw [← Hok.1 id']
      have := GMap.lookup_insert_is_Some I id id' (some (d, γf, γi.key))
      rw [this]
      by_cases h : id = id'
      · subst h; simp [Hlk]
      · simp [h]
    iunfold idClaimsFacts at HFs
    iunfold idClaimsFacts
    ihave ⟨-, Hk⟩ := (BigSepM.bigSepM_insert_acc (PROP := IProp GF) (m := I)
      (Φ := fun id v => idClaimFact Φs γi.fs id v) Hlk') $$ HFs
    iapply Hk
    iunfold idClaimFact
    iexists x
    iframe Hkf
    rw [HΦx]
    iexact HΦ
  imodintro
  iunfold idClaim
  iexact Hu

/-- **A claim's fact**, of a claim of the incarnation's own key: the claimer's `Φ`, from the
cluster's claims invariant through the key's saved predicate (D21e (A); by key since R2c: a claim of
another key, another member's or an earlier incarnation's, has that key's facts). -/
theorem idClaim_fact (γi : IdNames) (g : Loc) (Φ : w64 → List w8 → GName → IProp GF) (id : w64)
    (d : List w8) (γf : GName) (E : CoPset) (HE : ↑idClusterN ⊆ E) :
    ⊢ idGen (GF := GF) γi g Φ -∗ idClaim γi id d γf ={E}=∗ ▷ □ Φ id d γf := by
  iintro #Hg #Hc
  iunfold idGen at Hg
  icases Hg with ⟨%s0, %Hgn, #Hpfx, %Hs0, #Hinv, %X, %hX, %Φs, %x, %HΦx, #Hkf, #Hcl⟩
  iunfold idClusterInv at Hcl
  iinv Hcl with Hi Hclose
  icases Hi with ⟨%I, %C, %R, %Fm, >HI, >HC, >HR, >HF, >%Hok, #HFs, #HG⟩
  iunfold idClaim at Hc
  ihave %Hlk := ghost_map_lookup $$ HI Hc
  ihave #Hf : iprop(▷ □ Φ id d γf) $$ []
  · iunfold idClaimsFacts at HFs
    inext
    icases (BigSepM.bigSepM_lookup_acc (PROP := IProp GF) (m := I)
      (Φ := fun id v => idClaimFact Φs γi.fs id v) Hlk).1 $$ HFs with ⟨Hf, -⟩
    iunfold idClaimFact at Hf
    icases Hf with ⟨%x', #Hkf', #HΦ'⟩
    iunfold idKeyFactAt at Hkf Hkf'
    ihave %He := ghostMapElem_agree $$ Hkf Hkf'
    subst He
    rw [← HΦx]
    iexact HΦ'
  imod Hclose $$ [HI HC HR HF] with -
  · inext
    iexists I, C, R, Fm
    iframe HI HC HR HF HFs HG
    ipureintro; exact Hok
  imodintro
  iexact Hf

/-- Two claims of one id agree, the claimer's key included (R2c). -/
theorem idClaim_entry_agree (γi : IdNames) (id : w64) (v v' : IdClaimV) :
    ⊢ id ↪[γi.issued]□ (some v : Option IdClaimV) -∗ id ↪[γi.issued]□ (some v' : Option IdClaimV) -∗
      ⌜v = v'⌝ := by
  iintro #H1 #H2
  ihave %H := ghostMapElem_agree $$ H1 H2
  ipureintro; exact Option.some.inj H

theorem idClaim_agree (γi : IdNames) (id : w64) (d1 d2 : List w8) (γ1 γ2 : GName) :
    ⊢ idClaim (GF := GF) γi id d1 γ1 -∗ idClaim γi id d2 γ2 -∗ ⌜d1 = d2 ∧ γ1 = γ2⌝ := by
  iintro #H1 #H2
  iunfold idClaim at H1 H2
  ihave %H := idClaim_entry_agree γi id _ _ $$ H1 H2
  ipureintro
  simp only [Prod.mk.injEq] at H
  exact ⟨H.1, H.2.1⟩

/-- A claim by any key and an incarnation's claim of one id agree (R2c). -/
theorem idClaimAny_agree (γi : IdNames) (id : w64) (d1 d2 : List w8) (γ1 γ2 : GName) :
    ⊢ idClaimAny (GF := GF) γi id d1 γ1 -∗ idClaim γi id d2 γ2 -∗ ⌜d1 = d2 ∧ γ1 = γ2⌝ := by
  iintro #H1 #H2
  iunfold idClaimAny at H1
  icases H1 with ⟨%k, #H1⟩
  iunfold idClaim at H2
  ihave %H := idClaim_entry_agree γi id _ _ $$ H1 H2
  ipureintro
  simp only [Prod.mk.injEq] at H
  exact ⟨H.1, H.2.1⟩

/-- **A claim is the incarnation's own or another key's** (R2c): what the apply thread cases on. -/
theorem idClaimAny_own_or (γi : IdNames) (id : w64) (d : List w8) (γf : GName) :
    ⊢ idClaimAny (GF := GF) γi id d γf -∗
      idClaim γi id d γf ∨ ∃ k : IdKey, ⌜k ≠ γi.key⌝ ∗
        id ↪[γi.issued]□ (some (d, γf, k) : Option IdClaimV) := by
  iintro #Hc
  iunfold idClaimAny at Hc
  icases Hc with ⟨%k, #Hc⟩
  by_cases h : k = γi.key
  · subst h
    ileft
    iunfold idClaim
    iexact Hc
  · iright
    iexists k
    iframe Hc
    ipureintro; exact h

/-- **Another key's claim excludes the incarnation's own** (R2c): no claim of the incarnation, so no
waiter of it, for an id another key claimed. -/
theorem idClaim_other_excl (γi : IdNames) (id : w64) (d d' : List w8) (γf γf' : GName) (k : IdKey)
    (hk : k ≠ γi.key) :
    ⊢ id ↪[γi.issued]□ (some (d, γf, k) : Option IdClaimV) -∗ idClaim (GF := GF) γi id d' γf' -∗
      False := by
  iintro #H1 #H2
  iunfold idClaim at H2
  ihave %H := idClaim_entry_agree γi id _ _ $$ H1 H2
  simp only [Prod.mk.injEq] at H
  exact absurd H.2.2 hk

theorem idClaim_unclaimed (γi : IdNames) (id : w64) (d : List w8) (γf : GName) :
    ⊢ idClaimAny (GF := GF) γi id d γf -∗ idUnclaimed γi id -∗ False := by
  iintro #H1 H2
  iunfold idClaimAny at H1
  icases H1 with ⟨%k, #H1⟩
  iunfold idUnclaimed at H2
  icombine H1 H2 gives %Heq
  cases Heq.2

/-- **The reserved id `0` is claimed by no request** (D19c). -/
theorem idClaim_noZero (γi : IdNames) (d : List w8) (γf : GName) :
    ⊢ idNoZero (GF := GF) γi -∗ idClaimAny γi (W64 0) d γf -∗ False := by
  iintro #H1 #H2
  iunfold idNoZero at H1
  iunfold idClaimAny at H2
  icases H2 with ⟨%k, #H2⟩
  ihave %H := ghostMapElem_agree $$ H1 H2
  cases H

end lemmas

end EtcdGrove
end Perennial
