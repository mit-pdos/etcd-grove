/-
Port of election_proof/proof_MemoryStorage__Term.v.
-/
module

public import Spec.go_etcd_io.raft.v3.MemoryStorage__Term

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem MemoryStorage.Term.wp_proof :
    MemoryStorage.Term.spec (GF := GF) (hG := hG) := by
  intro ms γs σ i0
  wp_start as ⟨Hms, %Hrange, %Hpf⟩
  iunfold ownMemoryStorage at Hms
  icases Hms with ⟨#Hinit, #Hmu, Hview, %Hbounded⟩
  wp_auto
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
  iunfold memstorageInv at Hinv
  icases Hinv with ⟨%σ0, Hinv⟩
  iNamedSuffix Hinv "_inv"
  -- below the pending batch the contents answer as the view (2026-10-10)
  icases memView_agree γs σ σ0 $$ Hview Hgs_inv with ⟨%Hvw, Hview, Hgs_inv⟩
  obtain ⟨Hrange0, Hteq⟩ := memView_term σ σ0 Hvw i0 Hrange Hpf
  iunfold memstorageFields at Hfields_inv
  icases Hfields_inv with ⟨%hs, %snap, %es, %dummy, %cs, %voters, Hfields_inv⟩
  iNamed Hfields_inv
  wp_auto
  icases Hents with #Hents
  ihave %Hlen := ownSlice_len $$ Hents
  icases ownSlice_elem_acc 0 dummy es _ (dummy :: σ0.ents) (by omega) rfl $$ Hents with ⟨#He, -⟩
  obtain ⟨Hlen1, Hlen2⟩ := Hlen
  simp only [List.length_cons] at Hlen1
  have H0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z es.len := by
    constructor <;> word
  simp only [H0, and_self, ↓reduceIte]
  word_lit_simp
  -- Lean: field loads through a struct points-to at a fraction other than `1` are
  -- not found by `wp_load` (see `pbEntryID`); split the entry into its fields
  iStructNamedSuffix He "_0"
  wp_auto
  obtain ⟨Hd0, Hd1⟩ := Hdummy
  wp_if_destruct
  · exfalso; rw [Hd0] at Hif; word
  wp_if_destruct
  · exfalso; rw [Hd0] at Hif; word
  have Hn : sint.Z (i0 - dummy.Index') = uint.Z i0 - uint.Z σ0.prev.index' := by
    rw [Hd0]; word
  rw [Hn]
  have Hlt : (uint.Z i0 - uint.Z σ0.prev.index').toNat < (dummy :: σ0.ents).length := by
    simp only [List.length_cons]; omega
  obtain ⟨e, He⟩ : ∃ e, (dummy :: σ0.ents)[(uint.Z i0 - uint.Z σ0.prev.index').toNat]? = some e :=
    ⟨_, List.getElem?_eq_getElem Hlt⟩
  icases ownSlice_elem_acc (uint.Z i0 - uint.Z σ0.prev.index') e es _ (dummy :: σ0.ents)
    (by omega) He $$ Hents with ⟨#He1, -⟩
  have H1 : 0 ≤ uint.Z i0 - uint.Z σ0.prev.index' ∧
      uint.Z i0 - uint.Z σ0.prev.index' < sint.Z es.len := by
    constructor <;> word
  simp only [H1, and_self, ↓reduceIte]
  iStructNamedSuffix He1 "_1"
  wp_auto
  have Hterm : termAt σ0.prev σ0.ents i0 = some e.Term' := by
    unfold termAt
    by_cases Hi : uint.Z i0 = uint.Z σ0.prev.index'
    · simp only [Hi, ↓reduceIte]
      have H0 : (uint.Z i0 - uint.Z σ0.prev.index').toNat = 0 := by omega
      rw [H0] at He
      simp only [List.getElem?_cons_zero, Option.some.injEq] at He
      subst He
      rw [Hd1]
    · simp only [Hi, ↓reduceIte]
      have HS : (uint.Z i0 - uint.Z σ0.prev.index').toNat =
          (uint.Z i0 - uint.Z σ0.prev.index' - 1).toNat + 1 := by omega
      rw [HS] at He
      simp only [List.getElem?_cons_succ] at He
      rw [He]
      rfl
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hgs_inv HhardState Hsnapshot Hvoters Hents_f Hents_cap HcallStats]
  · inext
    unfold memstorageInv memstorageFields
    iexists σ0
    iframe Hgs_inv
    isplitl
    · iexists hs, snap, es, dummy, _, voters
      iframe # ∗
      ipureintro; exact ⟨Hsnap_id, Hd0, Hd1⟩
    ipureintro; exact Hpb_inv
  iapply HΦ
  isplitr
  · ipureintro; rw [← Hteq]; exact Hterm
  unfold ownMemoryStorage
  iframe # ∗
  ipureintro; exact Hbounded

end proof

end EtcdGrove
end Perennial
