/-
`MemoryStorage.LastIndex` (U8 v2 step 3): the end agrees with the lock's half.
-/
module

public import Spec.go_etcd_io.raft.v3.MemoryStorage__LastIndex
public import Spec.go_etcd_io.raft.v3.MemoryStorage__lastIndex

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem MemoryStorage.LastIndex.wp_proof
    (wp_MemoryStorage_lastIndex : MemoryStorage.lastIndex.spec (GF := GF) (hG := hG)) :
    MemoryStorage.LastIndex.spec (GF := GF) (hG := hG) := by
  intro ms γs e
  wp_start as ⟨#Hlock, Hend⟩
  iunfold memStorLock at Hlock
  icases Hlock with ⟨#Hinit, #Hmu⟩
  wp_auto
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
  iunfold memstorageInv at Hinv
  icases Hinv with ⟨%p, %ents, %M, %sv, Hinv⟩
  iNamedSuffix Hinv "_inv"
  iunfold memEnd at Hend
  icases Hend with ⟨Hen, Hek⟩
  icases ghostVar_agree γs.en _ _ _ _ $$ Hen Hen_inv with %He
  have Hb := Hok_inv.1
  have Hpb : uint.Z (memPhys p ents).prev.index' + ((memPhys p ents).ents.length : Int) < 2^61 := by
    simp only [memPhys]; word
  iunfold memstorageFields at Hfields_inv
  icases Hfields_inv with ⟨%hp, %es, %dummy, %nfi, %nli, %nen, %nte, %nsn, Hfields_inv⟩
  iNamed Hfields_inv
  wp_auto
  ihave Hf : memstorageFields ms (memPhys p ents) $$ [HhardState Hents_f Hents Hents_cap Hcs_firstIndex Hcs_lastIndex Hcs_entries Hcs_term Hcs_snapshot]
  · unfold memstorageFields
    iexists hp, es, dummy, _, _, _, _, _
    simp only [named]
    iframe
    ipureintro; exact Hdummy
  wp_apply wp_MemoryStorage_lastIndex _ _ Hpb $$ [$Hf] as %li ⟨%Hli, Hfields_inv⟩
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hfields_inv Hlog_inv Hen_inv Hcp_inv Hsx_inv Hlk_inv]
  · unfold memstorageInv
    iexists p, ents, M, sv
    simp only [named]
    iframe # ∗
    ipureintro; exact Hok_inv
  iapply HΦ
  isplitl [Hen Hek]
  · iunfold memEnd; iframe
  ipureintro
  simp only [memPhys] at Hli
  word

end proof

end EtcdGrove
end Perennial
