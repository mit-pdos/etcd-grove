/-
Port of election_proof/proof_MemoryStorage__LastIndex.v.
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
theorem MemoryStorage.LastIndex.wp_proof
    (wp_MemoryStorage_lastIndex : MemoryStorage.lastIndex.spec (GF := GF) (hG := hG)) :
    MemoryStorage.LastIndex.spec (GF := GF) (hG := hG) := by
  intro ms prev ents ss
  wp_start as Hms
  iNamed Hms
  iunfold ownMemoryStorage at Hms
  icases Hms with ⟨%γ, Hms⟩
  iNamed Hms
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
  iunfold memstorageInv at Hinv
  icases Hinv with ⟨%prev0, %ents0, %ss0, Hinv⟩
  iNamedSuffix Hinv "_inv"
  iunfold memstorageFields at Hfields_inv
  icases Hfields_inv with ⟨%hs, %snap, %es, %dummy, %cs, %voters, Hfields_inv⟩
  iNamed Hfields_inv
  icombine Hgs Hgs_inv gives %Heq
  obtain ⟨_, Heq⟩ := Heq
  simp only [Prod.mk.injEq] at Heq
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := Heq
  wp_auto
  ihave Hf : memstorageFields ms prev ents ss $$ [HhardState Hsnapshot Hvoters Hents_f Hents HcallStats]
  · unfold memstorageFields
    iexists hs, snap, es, dummy, _, voters
    simp only [named]
    iframe
    ipureintro; exact ⟨Hsnap_id, Hdummy⟩
  wp_apply wp_MemoryStorage_lastIndex _ _ _ _ Hbounded $$ [$Hf] as %li ⟨%Hli, Hf⟩
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hgs_inv Hf]
  · unfold memstorageInv
    iexists prev, ents, ss
    simp only [named]
    iframe
  iapply HΦ
  isplitr
  · ipureintro; exact Hli
  unfold ownMemoryStorage
  iexists γ
  simp only [named]
  iframe Hinit Hmu Hgs
  ipureintro; exact ⟨Hbounded, Hss⟩

end proof

end EtcdGrove
end Perennial
