/-
Proof of `Spec/k8s_io/client_go/util/consistency/newConsistencyStore.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.util.consistency.newConsistencyStore
public import Proof.k8s_io.client_go.util.consistency.InvLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace consistency

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.util.consistency

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.util.consistency.Assumptions]

theorem newConsistencyStore.wp_proof : newConsistencyStore.spec (GF := GF) (hG := hG) := by
  intro sm dq S G T
  wp_start as ⟨Hsm, #Hget, #Hexcl⟩
  iapply wp_fupd
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_map_make1 (K := Owner) (V := Loc) k8s_io.apimachinery.pkg.types.NamespacedName.ty
    (go.GoType.PointerType ownerRecord.ty) as %wm Hwm
  iStructNamed «$r0»
  ipersist writes
  ipersist stores
  ipersist Hsm
  -- the ghost state
  imod ghostVar_alloc (∅ : GMap Owner Rec) with ⟨%γM, HM⟩
  ihave ⟨HM1, HM2⟩ := (ghostVar_split_half γM 1 (∅ : GMap Owner Rec)).1 $$ HM
  imod ghostVar_alloc (∅ : GMap Owner Loc) with ⟨%γW, HW⟩
  ihave ⟨HW1, HW2⟩ := (ghostVar_split_half γW 1 (∅ : GMap Owner Loc)).1 $$ HW
  imod ghost_map_alloc_empty (K := Loc) (V := RecS) with ⟨%γr, Hrecs⟩
  imod ghost_map_alloc_empty (K := Nat) (V := Pend) with ⟨%γp, Hpend⟩
  imod ghost_map_alloc_empty (K := Owner) (V := EnsSt) with ⟨%γe, Hens⟩
  let γ : ConsNames := ⟨γM, γW, γr, γp, γe, wm, sm⟩
  imod inv_alloc consN ⊤ (consInv γ T) $$ [HM1 HW1 Hrecs Hpend Hens] with #Hinv
  · inext
    iunfold consInv
    iexists ∅, ∅, ∅, ∅, ∅, 0, ∅
    simp only [γ]
    iframe
    isplitr
    · iapply BigSepM.bigSepM_empty.2; itrivial
    isplitr
    · iapply BigSepM.bigSepM_empty.2; itrivial
    isplitr
    · iapply BigSepM.bigSepM_empty.2; itrivial
    isplitr
    · iapply BigSepM.bigSepM_empty.2; itrivial
    ipureintro
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> simp_all [absRel]
  imod sync.init_RWMutex (writesP γ) (E := ⊤) _ $$ [Hwm HW2] writesLock with Hrds
  · inext; iunfold writesP; iexists ∅; simp only [γ]; iframe
  ihave ⟨Hrds, #Hguard⟩ := sync.ownRWMutex_slots_guard _ _ $$ Hrds
  imodintro
  iapply HΦ
  iexists γ
  isplitr
  · iunfold isCons; simp only [γ, named]; iframe #
  isplitl [HM2]
  · iunfold consState; iexact HM2
  iunfold consReader
  iexact Hrds

end proof

end consistency
end EtcdGrove
end Perennial
