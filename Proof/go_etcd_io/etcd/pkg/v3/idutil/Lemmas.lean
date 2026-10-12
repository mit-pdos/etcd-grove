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

/-- **Claiming an id** for the data `d`: its issued map element goes from `none` to `some d`,
read-only from then on. -/
theorem idClaim_make (γi : IdNames) (g : Loc) (id : w64) (d : List w8) (E : CoPset)
    (HE : ↑idN ⊆ E) :
    ⊢ idGen (GF := GF) γi g -∗ idUnclaimed γi id ={E}=∗ idClaim γi id d := by
  iintro #Hg Hu
  iunfold idGen at Hg
  icases Hg with ⟨%pfx, %s0, %Hgn, #Hpfx, %Hs0, #Hinv⟩
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%k, %I, %S, Hsuf, Hcred, %Hk, HI, HS, %Hdom⟩
  iunfold idUnclaimed at Hu
  icombine HI Hu gives %Hlk
  imod ghost_map_update (some d) $$ HI Hu with ⟨HI, Hu⟩
  imod ghostMapElem_persist $$ Hu with Hu
  imod Hclose $$ [Hsuf Hcred HI HS] with -
  · inext
    iexists k, (I.insert id (some d)), S
    iframe
    ipureintro
    refine ⟨Hk, fun id' => ⟨?_, (Hdom id').2⟩⟩
    rw [← (Hdom id').1]
    have := GMap.lookup_insert_is_Some I id id' (some d)
    rw [this]
    by_cases h : id = id'
    · subst h; simp [Hlk]
    · simp [h]
  imodintro
  iunfold idClaim
  iexact Hu

theorem idClaim_agree (γi : IdNames) (id : w64) (d1 d2 : List w8) :
    ⊢ idClaim (GF := GF) γi id d1 -∗ idClaim γi id d2 -∗ ⌜d1 = d2⌝ := by
  iintro H1 H2
  iunfold idClaim at H1 H2
  icombine H1 H2 gives %Heq
  ipureintro; exact Option.some.inj Heq.2

theorem idClaim_unclaimed (γi : IdNames) (id : w64) (d : List w8) :
    ⊢ idClaim (GF := GF) γi id d -∗ idUnclaimed γi id -∗ False := by
  iintro H1 H2
  iunfold idClaim at H1
  iunfold idUnclaimed at H2
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
