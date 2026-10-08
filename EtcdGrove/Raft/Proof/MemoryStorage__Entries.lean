/- Port of election_proof/proof_MemoryStorage__Entries.v. -/
import EtcdGrove.Raft.Spec.MemoryStorage__Entries
import EtcdGrove.Raft.Spec.MemoryStorage__lastIndex
import EtcdGrove.Raft.Spec.limitSize

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem MemoryStorage.Entries.wp_proof
    (wp_MemoryStorage_lastIndex : MemoryStorage.lastIndex.spec (GF := GF) (hG := hG))
    (wp_limitSize : limitSize.spec (GF := GF) (hG := hG)) :
    MemoryStorage.Entries.spec (GF := GF) (hG := hG) := by
  intro ms prev ents ss lo hi maxSize
  wp_start as ⟨Hms, %Hrange⟩
  iunfold ownMemoryStorage at Hms
  icases Hms with ⟨%γ, Hms⟩
  iNamed Hms
  wp_apply wp_with_defer as %defer defer
  wp_pures; wp_alloc ms_ptr as ms; wp_pures; wp_alloc maxSize_ptr as maxSize; wp_pures
  wp_alloc hi_ptr as hi; wp_pures; wp_alloc lo_ptr as lo; wp_pures; wp_load; wp_pures
  -- `ms.Lock()`: the method of the embedded `sync.Mutex`
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
  wp_pures; wp_load; wp_pures; wp_load; wp_pures; wp_store; wp_pures; wp_load; wp_pures; wp_load
  wp_pures
  iNamedSuffix Hinv "_inv"
  ihave %Heq := ghostVar_agree $$ Hgs Hgs_inv
  simp only [Prod.mk.injEq] at Heq
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := Heq
  iNamed Hfields_inv
  icases Hents with #Hents
  wp_load; wp_pures; wp_store; wp_pures; wp_load; wp_pures; wp_load; wp_pures
  ihave %Hlen := ownSlice_len _ _ _ $$ Hents
  simp only [List.length_cons] at Hlen
  icases ownSlice_elem_acc (sint.Z (W64 0)) dummy es DFrac.discard (dummy :: ents) (by word) rfl
    $$ Hents with ⟨#He, -⟩
  rw [ite_eq_left ⟨by word, by word⟩]
  iStructNamed He
  wp_pures; wp_load; wp_pures; wp_alloc offset_ptr as offset; wp_pures; wp_store; wp_pures; wp_load
  wp_load; wp_pures
  obtain ⟨Hd0, Hd1⟩ := Hdummy
  wp_if_destruct
  · exfalso; rw [Hd0] at Hif; omega
  wp_load; wp_load; wp_pures
  ihave Hf : memstorageFields ms prev ents ss $$ [HhardState Hsnapshot Hvoters Hents_f HcallStats]
  · unfold memstorageFields
    iexists _, _, _, _, _, _
    iframe HhardState Hsnapshot Hvoters Hents_f HcallStats Hents
    ipureintro
    exact ⟨Hsnap_id, Hd0, Hd1⟩
  wp_apply wp_MemoryStorage_lastIndex ms prev ents ss Hbounded $$ [$Hf] as %li ⟨%Hli, Hf⟩
  wp_pures
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
  · wp_load; wp_pures; wp_load; wp_pures
  wp_load; wp_pures; wp_load; wp_pures
    exfalso; word
  wp_if_destruct
  · exfalso; word
  wp_load; wp_pures; wp_load; wp_pures; wp_load; wp_load; wp_pures; wp_load; wp_load; wp_pures
  iclear ms hi lo offset
  have Hlo' : sint.Z (lo - prev.index') = uint.Z lo - uint.Z prev.index' := by word
  have Hhi' : sint.Z (hi - prev.index') = uint.Z hi - uint.Z prev.index' := by word
  rw [ite_eq_left ⟨by word, by word, by word⟩]
  wp_pures; wp_load; wp_pures; iclear maxSize
  -- the sub-slice `ents[lo-offset:hi-offset]` is `E0`
  have Hlon : sint.nat (lo - prev.index') = (uint.Z lo - uint.Z prev.index' - 1).toNat + 1 := by
    word
  have Hhin : sint.nat (hi - prev.index') = (uint.Z hi - uint.Z prev.index' - 1).toNat + 1 := by
    word
  have HE0 : subslice (sint.nat (lo - prev.index')) (sint.nat (hi - prev.index')) (dummy :: ents) =
      (ents.take (uint.Z hi - uint.Z prev.index' - 1).toNat).drop
        (uint.Z lo - uint.Z prev.index' - 1).toNat := by
    rw [Hlon, Hhin]; simp [subslice]
  have HE0len : ((ents.take (uint.Z hi - uint.Z prev.index' - 1).toNat).drop
      (uint.Z lo - uint.Z prev.index' - 1).toNat).length =
      (uint.Z hi - uint.Z lo).toNat := by
    simp only [List.length_drop, List.length_take]; omega
  icases (ownSlice_slice (lo - prev.index') (hi - prev.index') es DFrac.discard (dummy :: ents)
      ⟨by word, by word, by word⟩).1 $$ Hents with ⟨-, #Hsub, -⟩
  rw [HE0] at *
  wp_apply wp_limitSize $$ [$Hsub] as %s1 %nlim ⟨%Hn, #Hs1, -⟩
  wp_pures; wp_alloc ents_ptr as ents; wp_pures; wp_store; wp_pures; wp_load; wp_pures; wp_load
  wp_pures; wp_load; wp_pures; iclear ents
  ihave %Hs1len := ownSlice_len _ _ _ $$ Hs1
  ihave %Hs1wf := ownSlice_wf _ _ _ $$ Hs1
  have HE0ne : (ents.take (uint.Z hi - uint.Z prev.index' - 1).toNat).drop
      (uint.Z lo - uint.Z prev.index' - 1).toNat ≠ [] := by
    intro Hc; rw [Hc, List.length_nil] at HE0len; omega
  have Hn1 := Hn.2 HE0ne
  have Hnetake : ((ents.take (uint.Z hi - uint.Z prev.index' - 1).toNat).drop
      (uint.Z lo - uint.Z prev.index' - 1).toNat).take nlim ≠ [] := by
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
  ihave Hf : memstorageFields ms prev ents ss $$ [HhardState Hsnapshot Hvoters Hents_f HcallStats]
  · unfold memstorageFields
    iexists _, _, _, _, _, _
    iframe HhardState Hsnapshot Hvoters Hents_f HcallStats Hents
    ipureintro
    exact ⟨Hsnap_id, Hd0', Hd1'⟩
  wp_pures; wp_load; wp_pures
  -- the deferred `ms.Unlock()`
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hgs_inv Hf]
  · unfold memstorageInv
    iexists prev, ents, ss
    iframe
  wp_pures
  iapply HΦ
  iframe Hs2
  isplitr
  · ipureintro
    refine ⟨Hnetake, ?_, ?_, ?_, List.take_prefix _ _⟩
    · rw [List.length_take, HE0len]; omega
    · intro e He
      exact List.mem_of_mem_drop (List.mem_of_mem_take He)
    · simp only [slice.fullSlice]
  unfold ownMemoryStorage
  iexists γ
  iframe # ∗
  ipureintro
  exact ⟨Hbounded, Hss⟩

end proof

end EtcdGrove
end Perennial
