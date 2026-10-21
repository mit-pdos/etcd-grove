/-
Port of election_proof/proof_MemoryStorage__Term.v.
-/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.MemoryStorage__Term
public import RaftWitness.Spec.go_etcd_io.raft.v3.raftpb.Entry__GetIndex
public import RaftWitness.Spec.go_etcd_io.raft.v3.raftpb.Entry__GetTerm
public import RaftWitness.Proof.go_etcd_io.raft.v3.LemmasMemstorage

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
  intro ms γs σ i0 ec
  wp_start as ⟨Hms, %Hrange, %Hpf, #Hec⟩
  iunfold ownMemoryStorage at Hms
  icases Hms with ⟨#Hinit, #Hmu, Hview, Hsn, %Hbounded⟩
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
  iunfold memstorageInv at Hinv
  icases Hinv with ⟨%σ0, %c, Hinv⟩
  iNamedSuffix Hinv "_inv"
  -- below the pending batch the contents answer as the view (2026-10-10); (D19i part 1) the
  -- fields are the contents cut at `c`
  icases memCut_view γs σ σ0 c $$ Hview Hgs_inv Hcut_inv
    with ⟨%Hvc, #Hcutlb, Hview, Hgs_inv, Hcut_inv⟩
  obtain ⟨Hvw, Hcok, Hcfl⟩ := Hvc
  obtain ⟨Hrange0, Hteq⟩ := memView_term σ σ0 Hvw i0 Hrange Hpf
  iunfold memstorageFields at Hfields_inv
  icases Hfields_inv with ⟨%hp, %es, %dummy, %nfi, %nli, %nen, %nte, %nsn, Hfields_inv⟩
  iNamed Hfields_inv
  icases Hents with #Hents
  ihave %Hcl := entsRO_cons_len $$ Hents
  icases entsRO_lookup es (dummy :: (memCut σ0 c).ents) 0 dummy rfl $$ Hents
    with ⟨%ls, %l0, #Hls, #He0, %Hl0⟩
  wp_auto
  rw [ite_eq_left ⟨by word, by word⟩]
  wp_apply wp_load_slice_index es (sint.Z (W64 0)) ls DFrac.discard l0 (by word) $$ [Hls] with -
  · iframe Hls; ipureintro; exact Hl0.1
  wp_apply wp_GetIndex.1 l0 DFrac.discard dummy $$ [He0] with -
  · iframe He0
  obtain ⟨Hd0, Hd1⟩ := Hdummy
  simp only [memCut] at Hd0 Hd1 Hcl
  have Hclast := memCut_stLast Hcok
  simp only [EtcdGrove.stLast, memCut] at Hclast
  wp_if_destruct
  · -- (D19i part 1) below the boundary: the application compacted past `i0`, `ErrCompacted`
    have Hlt : uint.Z i0 < uint.Z c.index' := by rw [Hd0] at Hif; word
    have Hne : c ≠ σ0.prev := by
      intro Hc; rw [Hc, Hvw.1] at Hlt; omega
    have Hfl : uint.Z c.index' ≤ uint.Z σ.fl := Hcfl.resolve_left Hne
    try wp_auto
    wp_method_call
    wp_call
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hgs_inv HhardState Hents_f Hents_cap Hcs_firstIndex Hcs_lastIndex Hcs_entries Hcs_term Hcs_snapshot Hcut_inv]
    · inext
      unfold memstorageInv memstorageFields
      iexists σ0, c
      iframe Hgs_inv Hcut_inv
      isplitl
      · iexists hp, es, dummy, _, _, _, _, _
        iframe # ∗
        ipureintro; exact ⟨Hd0, Hd1⟩
      ipureintro; exact Hpb_inv
    iapply HΦ
    isplitr
    · iright
      isplitr
      · ipureintro; exact ⟨rfl, by omega⟩
      iapply memStorCut_mono γs _ _ (by omega) (by have := uint_Z_nonneg i0; omega) $$ Hcutlb
    unfold ownMemoryStorage memSnapShare
    iframe # ∗
    ipureintro; exact Hbounded
  have Hge : uint.Z c.index' ≤ uint.Z i0 := by rw [Hd0] at Hif; word
  wp_if_destruct
  · exfalso; rw [Hd0] at Hif; word
  have Hn : sint.Z (i0 - dummy.Index') = uint.Z i0 - uint.Z c.index' := by
    rw [Hd0]; word
  rw [Hn]
  have Hlt : (uint.Z i0 - uint.Z c.index').toNat < (dummy :: (memCut σ0 c).ents).length := by
    simp only [List.length_cons, memCut]; omega
  obtain ⟨e, He⟩ : ∃ e, (dummy :: (memCut σ0 c).ents)[(uint.Z i0 - uint.Z c.index').toNat]? = some e :=
    ⟨_, List.getElem?_eq_getElem Hlt⟩
  icases entsRO_lookup es (dummy :: (memCut σ0 c).ents) _ e He $$ Hents
    with ⟨%ls1, %l1, #Hls1, #He1, %Hl1⟩
  have H1 : 0 ≤ uint.Z i0 - uint.Z c.index' ∧
      uint.Z i0 - uint.Z c.index' < sint.Z es.len := by
    constructor <;> word
  simp only [H1, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index es (uint.Z i0 - uint.Z c.index') ls1 DFrac.discard l1 (by word) $$ [Hls1] with -
  · iframe Hls1; ipureintro; exact Hl1.1
  wp_apply wp_GetTerm.1 l1 DFrac.discard e $$ [He1] with -
  · iframe He1
  have Hterm : termAt (memCut σ0 c).prev (memCut σ0 c).ents i0 = some e.Term' := by
    simp only [memCut]
    unfold termAt
    by_cases Hi : uint.Z i0 = uint.Z c.index'
    · simp only [Hi, ↓reduceIte]
      have H0 : (uint.Z i0 - uint.Z c.index').toNat = 0 := by omega
      rw [H0] at He
      simp only [List.getElem?_cons_zero, Option.some.injEq] at He
      subst He
      rw [Hd1]
    · simp only [Hi, ↓reduceIte]
      have HS : (uint.Z i0 - uint.Z c.index').toNat =
          (uint.Z i0 - uint.Z c.index' - 1).toNat + 1 := by omega
      rw [HS] at He
      simp only [List.getElem?_cons_succ, memCut] at He
      rw [He]
      rfl
  have Hterm' : termAt σ0.prev σ0.ents i0 = some e.Term' := by
    rw [← termAt_memCut Hcok i0 Hge]
    simpa only [memCut] using Hterm
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hgs_inv HhardState Hents_f Hents_cap Hcs_firstIndex Hcs_lastIndex Hcs_entries Hcs_term Hcs_snapshot Hcut_inv]
  · inext
    unfold memstorageInv memstorageFields
    iexists σ0, c
    iframe Hgs_inv Hcut_inv
    isplitl
    · iexists hp, es, dummy, _, _, _, _, _
      iframe # ∗
      ipureintro; exact ⟨Hd0, Hd1⟩
    ipureintro; exact Hpb_inv
  iapply HΦ
  isplitr
  · ileft; ipureintro; exact ⟨rfl, by rw [← Hteq]; exact Hterm'⟩
  unfold ownMemoryStorage
  iframe # ∗
  ipureintro; exact Hbounded

end proof

end EtcdGrove
end Perennial
