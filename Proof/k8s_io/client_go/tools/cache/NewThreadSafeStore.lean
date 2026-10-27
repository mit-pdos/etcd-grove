/-
Proof of `Spec/k8s_io/client_go/tools/cache/NewThreadSafeStore.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.NewThreadSafeStore
public import Spec.k8s_io.client_go.tools.cache.newStoreMetrics

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.tools.cache

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

theorem NewThreadSafeStore.wp_proof
    (wp_metrics : newStoreMetrics.spec (GF := GF) (hG := hG)) :
    NewThreadSafeStore.spec (GF := GF) (hG := hG) := by
  intro OK Fam im ip fv fnIds opts
  wp_start as ⟨Him, #Hfns, Hip, Hopts⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave %Hol := ownSlice_len $$ Hopts
  wp_auto
  wp_apply wp_map_make1 (K := GoString) (V := GoInterface) go.string
    (go.GoType.InterfaceType []) as %il Hil
  (try wp_auto)
  have hlen : opts.len = W64 0 := by simp at Hol; word
  ihave HI : (i_ptr ↦ W64 0 : IProp GF) $$ [i]
  · iexact i
  wp_for HI
  wp_if_destruct
  · exfalso; rw [hlen] at Hif; exact absurd Hif (by decide)
  (try wp_auto)
  wp_apply wp_metrics
  · ipureintro; exact ⟨rfl, by simp [interface.mkOk]⟩
  iintro %mp ⟨%g, #Hg, #Hgok⟩
  iStructNamed «$r0»
  wp_pures
  wp_load
  wp_pures
  wp_store
  ipersist metrics
  ipersist index
  iStructNamed «$v1»
  ipersist indexers
  -- the ghost state and the lock
  imod ghostVar_alloc (⟨∅, [], fnIds⟩ : St) with ⟨%γst, Hst⟩
  ihave ⟨Hst1, Hst2⟩ := (ghostVar_split_half γst 1 (⟨∅, [], fnIds⟩ : St)).1 $$ Hst
  imod ghostVar_alloc (⟨il, ip, ∅, fv⟩ : Ph) with ⟨%γph, Hgp⟩
  let γ : TsNames := ⟨γst, γph, «$v1_ptr», im⟩
  imod sync.init_RWMutex (tsP «$r0_ptr» γ OK Fam) (E := ⊤) _ $$ [Hst1 Hgp items Hil rv indices Hip Him] lock
    with Hrds
  · inext
    iunfold tsP
    iexists ⟨∅, [], fnIds⟩, ⟨il, ip, ∅, fv⟩
    simp only [γ]
    iframe
    isplitl
    · iunfold tsPhys
      iframe
      iunfold ownIx
      rw [GMap.fmap_empty]
      iframe
      iapply BigSepM.bigSepM_empty.2; itrivial
    isplitr
    · iunfold tsPers
      have hf : St.fns Fam (⟨∅, [], fnIds⟩ : St) = GMap.fmap Fam fnIds := rfl
      rw [hf]
      isplitr
      · iexact Hfns
      · iapply BigSepM.bigSepM_empty.2; itrivial
    ipureintro
    refine ⟨fun n hn => by simp [GMap.mem_iff] at hn, fun n F _ v k => ?_⟩
    unfold ixAt viewN inIdx objAt valsOf
    simp [GMap.mem_iff]
  ihave ⟨Hrds, #Hguard⟩ := sync.ownRWMutex_slots_guard _ _ $$ Hrds
  wp_auto
  iapply HΦ
  iexists γ
  isplitr
  · iunfold isTS
    iexists mp, g
    simp only [γ]
    iframe #
  isplitl [Hst2]
  · iunfold storeSt; iexact Hst2
  iunfold tsReader
  iexact Hrds

end proof

end cache
end EtcdGrove
end Perennial
