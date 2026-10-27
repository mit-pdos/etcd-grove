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

/-- **Claiming an id** of the member's prefix for the data `d` with the ghost name `γf`, given the
claimer's fact `□ Φ id d γf`: its element of the cluster's issued map goes from `none` to
`some (d, γf)`, read-only from then on, and the fact is kept in the cluster's claims invariant (at
the member's prefix, whose facts are the generator's `Φ`; D21e (A)). -/
theorem idClaim_make (γi : IdNames) (g : Loc) (Φ : w64 → List w8 → GName → IProp GF) (id : w64)
    (d : List w8) (γf : GName) (E : CoPset) (HE : ↑idClusterN ⊆ E) :
    ⊢ idGen (GF := GF) γi g Φ -∗ idUnclaimed γi id -∗ ⌜idPfx id = γi.pfx⌝ -∗ □ Φ id d γf ={E}=∗
      idClaim γi id d γf := by
  iintro #Hg Hu %Hp #HΦ
  iunfold idGen at Hg
  icases Hg with ⟨%s0, %Hgn, #Hpfx, %Hs0, #Hinv, %Φs, %HΦs, #Hcl⟩
  iunfold idClusterInv at Hcl
  iinv Hcl with Hi Hclose
  icases Hi with ⟨%I, %C, >HI, >HC, >%Hok, HF⟩
  iunfold idUnclaimed at Hu
  icombine HI Hu gives %Hlk
  have Hlk' : I.lookup id = some none := Hlk
  imod ghost_map_update (some (d, γf)) $$ HI Hu with ⟨HI, Hu⟩
  imod ghostMapElem_persist $$ Hu with Hu
  have hΦ : Φs (idPfx id) = Φ := by rw [Hp, HΦs]
  imod Hclose $$ [HI HC HF] with -
  · inext
    iexists (I.insert id (some (d, γf))), C
    iframe HI HC
    isplitr
    · ipureintro
      refine ⟨fun id' => ?_, Hok.2⟩
      rw [← Hok.1 id']
      have := GMap.lookup_insert_is_Some I id id' (some (d, γf))
      rw [this]
      by_cases h : id = id'
      · subst h; simp [Hlk]
      · simp [h]
    iunfold idClaimsFacts at HF
    iunfold idClaimsFacts
    ihave ⟨-, Hk⟩ := (BigSepM.bigSepM_insert_acc (PROP := IProp GF) (m := I)
      (Φ := fun id v => idClaimFact (Φs (idPfx id)) id v) Hlk') $$ HF
    iapply Hk
    simp only [hΦ]
    iunfold idClaimFact
    iexact HΦ
  imodintro
  iunfold idClaim
  iexact Hu

/-- **A claim's fact**, of an id of the member's prefix: the claimer's `Φ`, from the cluster's
claims invariant (D21e (A): an id of another prefix has that member's facts). -/
theorem idClaim_fact (γi : IdNames) (g : Loc) (Φ : w64 → List w8 → GName → IProp GF) (id : w64)
    (d : List w8) (γf : GName) (E : CoPset) (HE : ↑idClusterN ⊆ E) :
    ⊢ idGen (GF := GF) γi g Φ -∗ idClaim γi id d γf -∗ ⌜idPfx id = γi.pfx⌝ ={E}=∗
      ▷ □ Φ id d γf := by
  iintro #Hg #Hc %Hp
  iunfold idGen at Hg
  icases Hg with ⟨%s0, %Hgn, #Hpfx, %Hs0, #Hinv, %Φs, %HΦs, #Hcl⟩
  iunfold idClusterInv at Hcl
  iinv Hcl with Hi Hclose
  icases Hi with ⟨%I, %C, >HI, >HC, >%Hok, HF⟩
  iunfold idClaim at Hc
  ihave %Hlk := ghost_map_lookup $$ HI Hc
  have hΦ : Φs (idPfx id) = Φ := by rw [Hp, HΦs]
  iunfold idClaimsFacts at HF
  ihave #Hf : iprop(▷ □ Φ id d γf) $$ [HF]
  · inext
    icases (BigSepM.bigSepM_lookup_acc (PROP := IProp GF) (m := I)
      (Φ := fun id v => idClaimFact (Φs (idPfx id)) id v) Hlk).1 $$ HF with ⟨Hf, -⟩
    simp only [hΦ]
    iunfold idClaimFact at Hf
    iexact Hf
  imod Hclose $$ [HI HC HF] with -
  · inext
    iexists I, C
    iframe HI HC
    isplitr
    · ipureintro; exact Hok
    iunfold idClaimsFacts
    iexact HF
  imodintro
  iexact Hf

theorem idClaim_agree (γi : IdNames) (id : w64) (d1 d2 : List w8) (γ1 γ2 : GName) :
    ⊢ idClaim (GF := GF) γi id d1 γ1 -∗ idClaim γi id d2 γ2 -∗ ⌜d1 = d2 ∧ γ1 = γ2⌝ := by
  iintro H1 H2
  iunfold idClaim at H1 H2
  icombine H1 H2 gives %Heq
  ipureintro
  have := Option.some.inj Heq.2
  exact ⟨(Prod.mk.inj this).1, (Prod.mk.inj this).2⟩

theorem idClaim_unclaimed (γi : IdNames) (id : w64) (d : List w8) (γf : GName) :
    ⊢ idClaim (GF := GF) γi id d γf -∗ idUnclaimed γi id -∗ False := by
  iintro H1 H2
  iunfold idClaim at H1
  iunfold idUnclaimed at H2
  icombine H1 H2 gives %Heq
  cases Heq.2

/-- **The reserved id `0` is claimed by no request** (D19c). -/
theorem idClaim_noZero (γi : IdNames) (d : List w8) (γf : GName) :
    ⊢ idNoZero (GF := GF) γi -∗ idClaim γi (W64 0) d γf -∗ False := by
  iintro H1 H2
  iunfold idNoZero at H1
  iunfold idClaim at H2
  icombine H1 H2 gives %Heq
  cases Heq.2

end lemmas

end EtcdGrove
end Perennial
