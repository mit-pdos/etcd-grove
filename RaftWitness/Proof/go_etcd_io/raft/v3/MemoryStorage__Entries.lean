/- Port of election_proof/proof_MemoryStorage__Entries.v. -/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.MemoryStorage__Entries
public import RaftWitness.Spec.go_etcd_io.raft.v3.MemoryStorage__lastIndex
public import RaftWitness.Spec.go_etcd_io.raft.v3.limitSize
public import RaftWitness.Spec.go_etcd_io.raft.v3.raftpb.Entry__GetIndex
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

theorem MemoryStorage.Entries.wp_proof
    (wp_GetIndex : raftpb.Entry.GetIndex.spec (GF := GF) (hG := hG))
    (wp_MemoryStorage_lastIndex : MemoryStorage.lastIndex.spec (GF := GF) (hG := hG))
    (wp_limitSize : limitSize.spec (GF := GF) (hG := hG)) :
    MemoryStorage.Entries.spec (GF := GF) (hG := hG) := by
  intro ms γs σv lo hi maxSize ec
  wp_start as ⟨Hms, %Hrangev, %Hpf, #Hec⟩
  iunfold ownMemoryStorage at Hms
  icases Hms with ⟨#Hinit, #Hmu, Hview, Hsn, %Hbounded⟩
  wp_apply wp_with_defer as %defer defer
  -- `ms.Lock()`: the method of the embedded `sync.Mutex`
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
  iunfold memstorageInv at Hinv
  icases Hinv with ⟨%σL, %c, Hinv⟩
  iNamedSuffix Hinv "_inv"
  -- below the pending batch the contents `σL` answer as the view `σv` (2026-10-10); (D19i part 1)
  -- the fields `σ` are them cut at `c`
  icases memCut_view γs σv σL c $$ Hview Hgs_inv Hcut_inv
    with ⟨%Hvc, #Hcutlb, Hview, Hgs_inv, Hcut_inv⟩
  obtain ⟨Hvw, Hcok, Hcfl⟩ := Hvc
  obtain ⟨HrangeL, HtkL, HprevL⟩ := memView_entries σv σL Hvw lo hi Hrangev Hpf
  have Hlast := memCut_stLast Hcok
  have Hpb' : uint.Z (memCut σL c).prev.index' + ((memCut σL c).ents.length : Int) < 2^61 := by
    unfold EtcdGrove.stLast at Hlast; omega
  have Hc1 := Hcok.1
  generalize Hσ : memCut σL c = σ at Hpb' Hlast ⊢
  have Hσprev : σ.prev = c := by rw [← Hσ]; rfl
  iNamed Hfields_inv
  icases Hents with #Hents
  ihave %Hcl := entsRO_cons_len $$ Hents
  icases entsRO_lookup es (dummy :: σ.ents) 0 dummy rfl $$ Hents
    with ⟨%ls, %l0, #Hls, #He0, %Hl0⟩
  wp_auto
  rw [ite_eq_left ⟨by word, by word⟩]
  wp_apply wp_load_slice_index es (sint.Z (W64 0)) ls DFrac.discard l0 (by word) $$ [Hls] with -
  · iframe Hls; ipureintro; exact Hl0.1
  wp_apply wp_GetIndex.1 l0 DFrac.discard dummy $$ [He0] with -
  · iframe He0
  obtain ⟨Hd0, Hd1⟩ := Hdummy
  wp_if_destruct
  · -- (D19i part 1) at or below the boundary: the application compacted past `lo`,
    -- `ErrCompacted`
    have Hle : uint.Z lo ≤ uint.Z c.index' := by rw [Hd0, Hσprev] at Hif; omega
    have Hne : c ≠ σL.prev := by
      intro Hc; rw [Hc] at Hle; omega
    have Hfl : uint.Z c.index' ≤ uint.Z σv.fl := Hcfl.resolve_left Hne
    try wp_auto
    wp_method_call
    wp_call
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hgs_inv HhardState Hents_f Hents Hents_cap Hcs_firstIndex Hcs_lastIndex Hcs_entries Hcs_term Hcs_snapshot Hcut_inv]
    · inext
      unfold memstorageInv memstorageFields
      iexists σL, c
      iframe Hgs_inv Hcut_inv
      rw [Hσ]
      isplitl
      · iexists _, _, _, _, _, _, _, _
        iframe # ∗
        ipureintro; exact ⟨Hd0, Hd1⟩
      ipureintro; exact Hpb_inv
    iapply HΦ $$ %slice.nil %([] : List EntryM) %ec
    ileft
    isplitr
    · ipureintro; exact ⟨rfl, by omega⟩
    isplitr
    · iapply memStorCut_mono γs _ _ (by omega) (by have := uint_Z_nonneg lo; omega) $$ Hcutlb
    unfold ownMemoryStorage
    iframe # ∗
    ipureintro; exact Hbounded
  have Hlo : uint.Z c.index' + 1 ≤ uint.Z lo := by rw [Hd0, Hσprev] at Hif; omega
  have Hrange : uint.Z σ.prev.index' + 1 ≤ uint.Z lo ∧ uint.Z lo < uint.Z hi ∧
      uint.Z hi ≤ uint.Z σ.prev.index' + (σ.ents.length : Int) + 1 := by
    rw [Hσprev]
    unfold EtcdGrove.stLast at Hlast
    refine ⟨Hlo, Hrangev.2.1, ?_⟩
    have := HrangeL.2.2
    rw [Hσprev] at Hlast
    omega
  have HE : (σ.ents.take (uint.Z hi - uint.Z σ.prev.index' - 1).toNat).drop
        (uint.Z lo - uint.Z σ.prev.index' - 1).toNat =
      (σv.ents.take (uint.Z hi - uint.Z σv.prev.index' - 1).toNat).drop
        (uint.Z lo - uint.Z σv.prev.index' - 1).toNat := by
    rw [← Hσ]
    simp only [memCut]
    rw [memCut_drop Hcok lo hi Hlo Hrangev.2.1, HtkL, HprevL]
  ihave Hf : memstorageFields ms σ $$ [HhardState Hents_f Hents_cap Hcs_firstIndex Hcs_lastIndex Hcs_entries Hcs_term Hcs_snapshot]
  · unfold memstorageFields
    iexists _, _, _, _, _, _, _, _
    iframe HhardState Hents_f Hcs_firstIndex Hcs_lastIndex Hcs_entries Hcs_term Hcs_snapshot Hents Hents_cap
    ipureintro
    exact ⟨Hd0, Hd1⟩
  wp_apply wp_MemoryStorage_lastIndex ms σ Hpb' $$ [$Hf] as %li ⟨%Hli, Hf⟩
  rw [Hd0]
  unfold memstorageFields
  iNamed Hf
  icases Hents with #Hents
  clear Hcl Hl0
  ihave %Hcl := entsRO_cons_len $$ Hents
  obtain ⟨Hd0', Hd1'⟩ := Hdummy
  wp_if_destruct
  · exfalso; word
  wp_if_destruct
  · exfalso; word
  iunfold entsRO at Hents
  iunfold entsPts at Hents
  icases Hents with ⟨%ls, #Hls, #Hbig⟩
  ihave %Hlen2 := ownSlice_len _ _ _ $$ Hls
  ihave %Hwf2 := ownSlice_wf _ _ _ $$ Hls
  ihave %Hbl := entsBig_length $$ Hbig
  have Hlo' : sint.Z (lo - σ.prev.index') = uint.Z lo - uint.Z σ.prev.index' := by word
  have Hhi' : sint.Z (hi - σ.prev.index') = uint.Z hi - uint.Z σ.prev.index' := by word
  rw [ite_eq_left ⟨by word, by word, by word⟩]
  wp_auto
  -- the sub-slice `σ.ents[lo-offset:hi-offset]` is `E0`
  have Hlon : sint.nat (lo - σ.prev.index') = (uint.Z lo - uint.Z σ.prev.index' - 1).toNat + 1 := by
    word
  have Hhin : sint.nat (hi - σ.prev.index') = (uint.Z hi - uint.Z σ.prev.index' - 1).toNat + 1 := by
    word
  have HE0 : subslice (sint.nat (lo - σ.prev.index')) (sint.nat (hi - σ.prev.index')) (dummy :: σ.ents) =
      (σ.ents.take (uint.Z hi - uint.Z σ.prev.index' - 1).toNat).drop
        (uint.Z lo - uint.Z σ.prev.index' - 1).toNat := by
    rw [Hlon, Hhin]; simp [subslice]
  have HE0len : ((σ.ents.take (uint.Z hi - uint.Z σ.prev.index' - 1).toNat).drop
      (uint.Z lo - uint.Z σ.prev.index' - 1).toNat).length =
      (uint.Z hi - uint.Z lo).toNat := by
    simp only [List.length_drop, List.length_take]; omega
  icases (ownSlice_slice (lo - σ.prev.index') (hi - σ.prev.index') es DFrac.discard ls
      ⟨by word, by word, by word⟩).1 $$ Hls with ⟨-, #Hsub, -⟩
  ihave #Hbsub := entsBig_subslice (sint.nat (lo - σ.prev.index')) (sint.nat (hi - σ.prev.index'))
    ls (dummy :: σ.ents) $$ Hbig
  ihave #HsubE : entsRO (slice.slice es Loc (lo - σ.prev.index') (hi - σ.prev.index'))
      ((σ.ents.take (uint.Z hi - uint.Z σ.prev.index' - 1).toNat).drop
        (uint.Z lo - uint.Z σ.prev.index' - 1).toNat) $$ []
  · rw [← HE0]
    iunfold entsRO; iunfold entsPts
    iexists _
    iframe Hsub Hbsub
  wp_apply wp_limitSize $$ [$HsubE] as %s1 %nlim ⟨%Hn, Hs1, -⟩
  iunfold entsPts at Hs1
  icases Hs1 with ⟨%ls1, #Hs1, #Hb1⟩
  ihave %Hs1len := ownSlice_len _ _ _ $$ Hs1
  ihave %Hs1wf := ownSlice_wf _ _ _ $$ Hs1
  ihave %Hb1len := entsBig_length $$ Hb1
  have HE0ne : (σ.ents.take (uint.Z hi - uint.Z σ.prev.index' - 1).toNat).drop
      (uint.Z lo - uint.Z σ.prev.index' - 1).toNat ≠ [] := by
    intro Hc; rw [Hc, List.length_nil] at HE0len; omega
  have Hn1 := Hn.2 HE0ne
  have Hnetake : ((σ.ents.take (uint.Z hi - uint.Z σ.prev.index' - 1).toNat).drop
      (uint.Z lo - uint.Z σ.prev.index' - 1).toNat).take nlim ≠ [] := by
    intro Hc
    have := congrArg List.length Hc
    rw [List.length_take, List.length_nil] at this
    omega
  have Hls1ne : ls1 ≠ [] := by
    intro Hc; rw [Hc, List.length_nil] at Hb1len
    exact Hnetake (List.length_eq_zero_iff.1 Hb1len.symm)
  rw [ite_eq_left ⟨by decide, by word, by word, by word⟩]
  ihave #Hs2 := ownSlice_same_ptr_len s1 (slice.fullSlice s1 Loc (W64 0) s1.len s1.len)
    DFrac.discard _ Hls1ne
    (by simp only [slice.fullSlice, sliceIndexRef]; rw [show sint.Z (W64 0) = 0 from rfl,
          go.arrayIndexRef_0])
    (by simp only [slice.fullSlice]; word)
    (by simp only [slice.fullSlice]; word) $$ Hs1
  ihave Hf : memstorageFields ms σ $$ [HhardState Hents_f Hents_cap Hcs_firstIndex Hcs_lastIndex Hcs_entries Hcs_term Hcs_snapshot]
  · unfold memstorageFields
    iexists _, _, _, _, _, _, _, _
    iframe HhardState Hents_f Hcs_firstIndex Hcs_lastIndex Hcs_entries Hcs_term Hcs_snapshot Hents_cap
    isplitr
    · iunfold entsRO; iunfold entsPts; iexists ls; iframe Hls Hbig
    ipureintro
    exact ⟨Hd0', Hd1'⟩
  wp_auto
  -- the deferred `ms.Unlock()`
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hgs_inv Hf Hcut_inv]
  · unfold memstorageInv
    iexists σL, c
    rw [Hσ]
    iframe
    ipureintro; exact Hpb_inv
  iapply HΦ
  iright
  isplitr
  · ipureintro; rfl
  isplitr
  · iunfold entsRO; iunfold entsPts; iexists ls1; iframe Hs2 Hb1
  isplitr
  · ipureintro
    rw [← HE]
    refine ⟨Hnetake, ?_, ?_, ?_, List.take_prefix _ _⟩
    · rw [List.length_take, HE0len]; omega
    · intro e He
      have H1 := List.mem_of_mem_take He
      rw [HE] at H1
      exact List.mem_of_mem_drop H1
    · simp only [slice.fullSlice]
  unfold ownMemoryStorage
  iframe # ∗
  ipureintro
  exact Hbounded

end proof

end EtcdGrove
end Perennial
