/- Port of election_proof/proof_MemoryStorage__Entries.v. -/
module

public import Spec.go_etcd_io.raft.v3.MemoryStorage__Entries
public import Spec.go_etcd_io.raft.v3.MemoryStorage__lastIndex
public import Spec.go_etcd_io.raft.v3.limitSize

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
    (wp_MemoryStorage_lastIndex : MemoryStorage.lastIndex.spec (GF := GF) (hG := hG))
    (wp_limitSize : limitSize.spec (GF := GF) (hG := hG)) :
    MemoryStorage.Entries.spec (GF := GF) (hG := hG) := by
  intro ms γs σv lo hi maxSize
  wp_start as ⟨Hms, %Hrangev, %Hpf⟩
  iunfold ownMemoryStorage at Hms
  icases Hms with ⟨#Hinit, #Hmu, Hview, %Hbounded⟩
  wp_apply wp_with_defer as %defer defer
  -- `ms.Lock()`: the method of the embedded `sync.Mutex`
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
  iunfold memstorageInv at Hinv
  icases Hinv with ⟨%σ, Hinv⟩
  iNamedSuffix Hinv "_inv"
  -- below the pending batch the contents `σ` answer as the view `σv` (2026-10-10)
  icases memView_agree γs σv σ $$ Hview Hgs_inv with ⟨%Hvw, Hview, Hgs_inv⟩
  obtain ⟨Hrange, Htk, Hprev⟩ := memView_entries σv σ Hvw lo hi Hrangev Hpf
  iNamed Hfields_inv
  icases Hents with #Hents
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hents
  simp only [List.length_cons] at Hlen
  icases ownSlice_elem_acc (sint.Z (W64 0)) dummy es DFrac.discard (dummy :: σ.ents) (by word) rfl
    $$ Hents with ⟨#He, -⟩
  rw [ite_eq_left ⟨by word, by word⟩]
  iStructNamed He
  wp_auto
  obtain ⟨Hd0, Hd1⟩ := Hdummy
  wp_if_destruct
  · exfalso; rw [Hd0] at Hif; omega
  ihave Hf : memstorageFields ms σ $$ [HhardState Hsnapshot Hvoters Hents_f Hents_cap Hcs_firstIndex Hcs_lastIndex Hcs_entries Hcs_term Hcs_snapshot]
  · unfold memstorageFields
    iexists _, _, _, _, _, _, _, _, _, _
    iframe HhardState Hsnapshot Hvoters Hents_f Hcs_firstIndex Hcs_lastIndex Hcs_entries Hcs_term Hcs_snapshot Hents Hents_cap
    ipureintro
    exact ⟨Hsnap_id, Hd0, Hd1⟩
  wp_apply wp_MemoryStorage_lastIndex ms σ Hpb_inv $$ [$Hf] as %li ⟨%Hli, Hf⟩
  iclear Hents He Term Index Type' Data
  rw [Hd0]
  unfold memstorageFields
  iNamed Hf
  icases Hents with #Hents
  ihave %Hlen2 := ownSlice_len _ _ _ $$ Hents
  ihave %Hwf2 := ownSlice_wf _ _ _ $$ Hents
  simp only [List.length_cons] at Hlen2
  obtain ⟨Hd0', Hd1'⟩ := Hdummy
  wp_if_destruct
  · exfalso; word
  wp_if_destruct
  · exfalso; word
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
  icases (ownSlice_slice (lo - σ.prev.index') (hi - σ.prev.index') es DFrac.discard (dummy :: σ.ents)
      ⟨by word, by word, by word⟩).1 $$ Hents with ⟨-, #Hsub, -⟩
  rw [HE0] at *
  wp_apply wp_limitSize $$ [$Hsub] as %s1 %nlim ⟨%Hn, #Hs1, -⟩
  ihave %Hs1len := ownSlice_len _ _ _ $$ Hs1
  ihave %Hs1wf := ownSlice_wf _ _ _ $$ Hs1
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
  rw [ite_eq_left ⟨by decide, by word, by word, by word⟩]
  ihave #Hs2 := ownSlice_same_ptr_len s1 (slice.fullSlice s1 raftpb.Entry (W64 0) s1.len s1.len)
    DFrac.discard _ Hnetake
    (by simp only [slice.fullSlice, sliceIndexRef]; rw [show sint.Z (W64 0) = 0 from rfl,
          go.arrayIndexRef_0])
    (by simp only [slice.fullSlice]; word)
    (by simp only [slice.fullSlice]; word) $$ Hs1
  ihave Hf : memstorageFields ms σ $$ [HhardState Hsnapshot Hvoters Hents_f Hents_cap Hcs_firstIndex Hcs_lastIndex Hcs_entries Hcs_term Hcs_snapshot]
  · unfold memstorageFields
    iexists _, _, _, _, _, _, _, _, _, _
    iframe HhardState Hsnapshot Hvoters Hents_f Hcs_firstIndex Hcs_lastIndex Hcs_entries Hcs_term Hcs_snapshot Hents Hents_cap
    ipureintro
    exact ⟨Hsnap_id, Hd0', Hd1'⟩
  wp_auto
  -- the deferred `ms.Unlock()`
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hgs_inv Hf]
  · unfold memstorageInv
    iexists σ
    iframe
    ipureintro; exact Hpb_inv
  iapply HΦ
  iframe Hs2
  isplitr
  · ipureintro
    rw [← Htk, ← Hprev]
    refine ⟨Hnetake, ?_, ?_, ?_, List.take_prefix _ _⟩
    · rw [List.length_take, HE0len]; omega
    · intro e He
      exact List.mem_of_mem_drop (List.mem_of_mem_take He)
    · simp only [slice.fullSlice]
  unfold ownMemoryStorage
  iframe # ∗
  ipureintro
  exact Hbounded

end proof

end EtcdGrove
end Perennial
