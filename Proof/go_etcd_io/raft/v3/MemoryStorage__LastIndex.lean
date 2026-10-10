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
  intro ms γs σ
  wp_start as ⟨Hms, %Hpnil⟩
  iunfold ownMemoryStorage at Hms
  icases Hms with ⟨#Hinit, #Hmu, Hview, %Hbounded⟩
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
  iunfold memstorageInv at Hinv
  icases Hinv with ⟨%σ0, Hinv⟩
  iNamedSuffix Hinv "_inv"
  -- with nothing pending the contents are the view (2026-10-10)
  icases memView_agree γs σ σ0 $$ Hview Hgs_inv with ⟨%Hvw, Hview, Hgs_inv⟩
  have Heq : σ0 = σ := Hvw.2.2.2 Hpnil
  subst Heq
  iunfold memstorageFields at Hfields_inv
  icases Hfields_inv with ⟨%hs, %snap, %es, %dummy, %cs, %voters, Hfields_inv⟩
  iNamed Hfields_inv
  wp_auto
  ihave Hf : memstorageFields ms σ0 $$ [HhardState Hsnapshot Hvoters Hents_f Hents Hents_cap HcallStats]
  · unfold memstorageFields
    iexists hs, snap, es, dummy, _, voters
    simp only [named]
    iframe
    ipureintro; exact ⟨Hsnap_id, Hdummy⟩
  wp_apply wp_MemoryStorage_lastIndex _ _ Hpb_inv $$ [$Hf] as %li ⟨%Hli, Hf⟩
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hgs_inv Hf]
  · unfold memstorageInv
    iexists σ0
    simp only [named]
    iframe
    ipureintro; exact Hpb_inv
  iapply HΦ
  isplitr
  · ipureintro; exact Hli
  unfold ownMemoryStorage
  simp only [named]
  iframe Hinit Hmu Hview
  ipureintro; exact Hbounded

end proof

end EtcdGrove
end Perennial
