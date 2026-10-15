/-
Port of election_proof/proof_MemoryStorage__Term.v.
-/
module

public import Raft37.Spec.go_etcd_io.raft.v3.MemoryStorage__Term
public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.Entry__GetIndex
public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.Entry__GetTerm
public import Raft37.Proof.go_etcd_io.raft.v3.LemmasMemstorage

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

theorem MemoryStorage.Term.wp_proof
    (wp_GetIndex : raftpb.Entry.GetIndex.spec (GF := GF) (hG := hG))
    (wp_GetTerm : raftpb.Entry.GetTerm.spec (GF := GF) (hG := hG)) :
    MemoryStorage.Term.spec (GF := GF) (hG := hG) := by
  intro ms γs σ i0
  wp_start as ⟨Hms, %Hrange, %Hpf⟩
  iunfold ownMemoryStorage at Hms
  icases Hms with ⟨#Hinit, #Hmu, Hview, Hsn, %Hbounded⟩
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
  iunfold memstorageInv at Hinv
  icases Hinv with ⟨%σ0, Hinv⟩
  iNamedSuffix Hinv "_inv"
  -- below the pending batch the contents answer as the view (2026-10-10)
  icases memView_agree γs σ σ0 $$ Hview Hgs_inv with ⟨%Hvw, Hview, Hgs_inv⟩
  obtain ⟨Hrange0, Hteq⟩ := memView_term σ σ0 Hvw i0 Hrange Hpf
  iunfold memstorageFields at Hfields_inv
  icases Hfields_inv with ⟨%hp, %es, %dummy, %nfi, %nli, %nen, %nte, %nsn, Hfields_inv⟩
  iNamed Hfields_inv
  icases Hents with #Hents
  ihave %Hcl := entsRO_cons_len $$ Hents
  icases entsRO_lookup es (dummy :: σ0.ents) 0 dummy rfl $$ Hents
    with ⟨%ls, %l0, #Hls, #He0, %Hl0⟩
  wp_auto
  rw [ite_eq_left ⟨by word, by word⟩]
  wp_apply wp_load_slice_index es (sint.Z (W64 0)) ls DFrac.discard l0 (by word) $$ [Hls] with -
  · iframe Hls; ipureintro; exact Hl0.1
  wp_apply wp_GetIndex.1 l0 DFrac.discard dummy $$ [He0] with -
  · iframe He0
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
  icases entsRO_lookup es (dummy :: σ0.ents) _ e He $$ Hents
    with ⟨%ls1, %l1, #Hls1, #He1, %Hl1⟩
  have H1 : 0 ≤ uint.Z i0 - uint.Z σ0.prev.index' ∧
      uint.Z i0 - uint.Z σ0.prev.index' < sint.Z es.len := by
    constructor <;> word
  simp only [H1, and_self, ↓reduceIte]
  wp_apply wp_load_slice_index es (uint.Z i0 - uint.Z σ0.prev.index') ls1 DFrac.discard l1 (by word) $$ [Hls1] with -
  · iframe Hls1; ipureintro; exact Hl1.1
  wp_apply wp_GetTerm.1 l1 DFrac.discard e $$ [He1] with -
  · iframe He1
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
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hgs_inv HhardState Hents_f Hents_cap Hcs_firstIndex Hcs_lastIndex Hcs_entries Hcs_term Hcs_snapshot]
  · inext
    unfold memstorageInv memstorageFields
    iexists σ0
    iframe Hgs_inv
    isplitl
    · iexists hp, es, dummy, _, _, _, _, _
      iframe # ∗
      ipureintro; exact ⟨Hd0, Hd1⟩
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
