/-
Facts about Perennial's heap resources (the map points-to `ownMap`, the typed points-to) that
belong to no Go package. The ones about Iris's own resources are in `Proof/Lib/Iris.lean`.

They are kept here until Perennial has them: each is a candidate for an independent Perennial
proposal (CLAUDE.md, "Changes to Perennial"), and goes once its Perennial counterpart lands.
The copies they replace were each proved in a package's section, under that package's
assumptions (`notes/decisions.md`, "Proof/Lib: facts that belong to no Go package").
-/
module

public import Proof.Lib.Iris
public import Perennial.Golang.Theory.Map

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section heap
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [go.PreSemantics]

/-- A points-to at `q1 + q2` in two parts. -/
theorem ptsto_frac_add {V : Type} [TypedPointsto (GF := GF) V] (l : Loc) (v : V) (q1 q2 : Qp) :
    typedPointsto (GF := GF) l v (DFrac.own (q1 + q2)) ⊣⊢
      typedPointsto (GF := GF) l v (DFrac.own q1) ∗ typedPointsto (GF := GF) l v (DFrac.own q2) :=
  (typedPointsto_dfractional (GF := GF) l v).dfractional (DFrac.own q1) (DFrac.own q2)

variable {K V : Type} [ZeroVal K] [DecidableEq K] [ZeroVal V] [go.IntoValInj K]

/-- A map points-to splits and combines by fraction. -/
theorem ownMap_fractional (mref : Loc) (m : GMap K V) :
    Fractional (fun q : Qp => (ownMap (GF := GF) mref (DFrac.own q) m : IProp GF)) where
  fractional p q := by
    rw [ownMap_unseal]
    have hh := fun mv => (heapPointsto_fractional mref mv).fractional p q
    constructor
    · iintro H
      unfold ownMapDef
      iNamed H
      icases (hh mv).1 $$ Hown with ⟨H1, H2⟩
      isplitl [H1]
      · iexists mv, mp; simp only [named]; iframe H1; ipureintro; exact ⟨His_map, Hagree, Hdom, Hdefault⟩
      · iexists mv, mp; simp only [named]; iframe H2; ipureintro; exact ⟨His_map, Hagree, Hdom, Hdefault⟩
    · iintro ⟨H1, H2⟩
      unfold ownMapDef
      iNamedSuffix H1 "1"
      iNamedSuffix H2 "2"
      icombine Hown1 Hown2 gives % ⟨_, Hmv⟩
      subst Hmv
      iexists mv, mp
      simp only [named]
      isplitl [Hown1 Hown2]
      · iapply (hh mv).2; iframe
      ipureintro; exact ⟨His_map2, Hagree2, Hdom2, Hdefault2⟩

/-- Two shares of a map points-to agree on the map (for values whose Go values are injective). -/
theorem ownMap_agree [go.IntoValInj V] (mref : Loc) (dq1 dq2 : DFrac) (m1 m2 : GMap K V) :
    ownMap (GF := GF) mref dq1 m1 ∗ ownMap (GF := GF) mref dq2 m2 ⊢ ⌜m1 = m2⌝ := by
  rw [ownMap_unseal]
  iintro ⟨H1, H2⟩
  unfold ownMapDef
  iNamedSuffix H1 "1"
  iNamedSuffix H2 "2"
  icombine Hown1 Hown2 gives % ⟨_, Hmv⟩
  subst Hmv
  ipureintro
  apply GMap.ext
  intro k
  have h1 := Hagree1 k
  have h2 := Hagree2 k
  rw [← go.mapLookup_pure _ _ _ His_map1, go.mapLookup_pure _ _ _ His_map2] at h1
  rw [h1] at h2
  change m1 !! k = m2 !! k
  cases hk1 : m1 !! k <;> cases hk2 : m2 !! k <;> simp only [hk1, hk2] at h2
  · rfl
  · cases h2
  · cases h2
  · simp only [Prod.mk.injEq, true_and] at h2
    rw [go.intoVal_inj h2]

end heap

end EtcdGrove
end Perennial
