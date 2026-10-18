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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **Claiming an id** for the data `d` with the ghost name `γf`, given the claimer's fact
`□ Φ id d γf`: its issued map element goes from `none` to `some (d, γf)`, read-only from then
on, and the fact is kept in the generator's invariant. -/
theorem idClaim_make (γi : IdNames) (g : Loc) (Φ : w64 → List w8 → GName → IProp GF) (id : w64)
    (d : List w8) (γf : GName) (E : CoPset) (HE : ↑idN ⊆ E) :
    ⊢ idGen (GF := GF) γi g Φ -∗ idUnclaimed γi id -∗ □ Φ id d γf ={E}=∗ idClaim γi id d γf := by
  iintro #Hg Hu #HΦ
  iunfold idGen at Hg
  icases Hg with ⟨%pfx, %s0, %Hgn, #Hpfx, %Hs0, #Hinv⟩
  iinv Hinv with Hi Hclose
  icases Hi with ⟨%k, %I, %S, >Hsuf, >Hcred, >HI, >HS, >%Hdom, HF⟩
  iunfold idUnclaimed at Hu
  icombine HI Hu gives %Hlk
  have Hlk' : I.lookup id = some none := Hlk
  imod ghost_map_update (some (d, γf)) $$ HI Hu with ⟨HI, Hu⟩
  imod ghostMapElem_persist $$ Hu with Hu
  imod Hclose $$ [Hsuf Hcred HI HS HF] with -
  · inext
    iexists k, (I.insert id (some (d, γf))), S
    iframe Hsuf Hcred HI HS
    isplitr
    · ipureintro
      refine fun id' => ⟨?_, (Hdom id').2⟩
      rw [← (Hdom id').1]
      have := GMap.lookup_insert_is_Some I id id' (some (d, γf))
      rw [this]
      by_cases h : id = id'
      · subst h; simp [Hlk]
      · simp [h]
    iunfold idClaimsFacts at HF
    iunfold idClaimsFacts
    ihave ⟨-, Hk⟩ := (BigSepM.bigSepM_insert_acc (PROP := IProp GF) (m := I) (Φ := idClaimFact Φ) Hlk') $$ HF
    iapply Hk
    iunfold idClaimFact
    iexact HΦ
  imodintro
  iunfold idClaim
  iexact Hu

/-- **A claim's fact**: the claimer's `Φ`, from the generator's invariant. -/
theorem idClaim_fact (γi : IdNames) (g : Loc) (Φ : w64 → List w8 → GName → IProp GF) (id : w64)
    (d : List w8) (γf : GName) (E : CoPset) (HE : ↑idN ⊆ E) :
    ⊢ idGen (GF := GF) γi g Φ -∗ idClaim γi id d γf ={E}=∗ ▷ □ Φ id d γf := by
  iintro #Hg #Hc
  iunfold idGen at Hg
  icases Hg with ⟨%pfx, %s0, %Hgn, #Hpfx, %Hs0, #Hinv⟩
  iinv Hinv with Hi Hclose
  icases Hi with ⟨%k, %I, %S, >Hsuf, >Hcred, >HI, >HS, >%Hdom, HF⟩
  iunfold idClaim at Hc
  ihave %Hlk := ghost_map_lookup $$ HI Hc
  iunfold idClaimsFacts at HF
  ihave #Hf : iprop(▷ □ Φ id d γf) $$ [HF]
  · inext
    icases (BigSepM.bigSepM_lookup_acc (PROP := IProp GF) (m := I) (Φ := idClaimFact Φ) Hlk).1 $$ HF with ⟨Hf, -⟩
    iunfold idClaimFact at Hf
    iexact Hf
  imod Hclose $$ [Hsuf Hcred HI HS HF] with -
  · inext
    iexists k, I, S
    iframe Hsuf Hcred HI HS
    isplitr
    · ipureintro; exact Hdom
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

theorem idSlot_excl (γi : IdNames) (id : w64) :
    ⊢ idSlot (GF := GF) γi id -∗ idSlot γi id -∗ False := by
  iintro H1 H2
  iunfold idSlot at H1 H2
  ihave %Hne := ghostMapElem_ne _ _ _ _ _ _ $$ H1 H2
  exact absurd rfl Hne

end lemmas

end EtcdGrove
end Perennial
