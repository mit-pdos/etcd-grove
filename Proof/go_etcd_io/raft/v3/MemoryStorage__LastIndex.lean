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
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
theorem MemoryStorage.LastIndex.wp_proof
    (wp_MemoryStorage_lastIndex : MemoryStorage.lastIndex.spec (GF := GF) (hG := hG)) :
    MemoryStorage.LastIndex.spec (GF := GF) (hG := hG) := by
  intro ms γs σ
  wp_start as ⟨Hms, %Hpnil⟩
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
  -- with nothing pending the contents have the view's entries (2026-10-10); (D19i part 1) the
  -- cut keeps the last index
  icases memCut_view γs σ σ0 c $$ Hview Hgs_inv Hcut_inv
    with ⟨%Hvc, -, Hview, Hgs_inv, Hcut_inv⟩
  obtain ⟨Hvw, Hcok, -⟩ := Hvc
  have Hlast := memCut_stLast Hcok
  have Hpb' : uint.Z (memCut σ0 c).prev.index' + ((memCut σ0 c).ents.length : Int) < 2^61 := by
    unfold EtcdGrove.stLast at Hlast; omega
  iunfold memstorageFields at Hfields_inv
  icases Hfields_inv with ⟨%hp, %es, %dummy, %nfi, %nli, %nen, %nte, %nsn, Hfields_inv⟩
  iNamed Hfields_inv
  wp_auto
  ihave Hf : memstorageFields ms (memCut σ0 c) $$ [HhardState Hents_f Hents Hents_cap Hcs_firstIndex Hcs_lastIndex Hcs_entries Hcs_term Hcs_snapshot]
  · unfold memstorageFields
    iexists hp, es, dummy, _, _, _, _, _
    simp only [named]
    iframe
    ipureintro; exact Hdummy
  wp_apply wp_MemoryStorage_lastIndex _ _ Hpb' $$ [$Hf] as %li ⟨%Hli, Hf⟩
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hgs_inv Hf Hcut_inv]
  · unfold memstorageInv
    iexists σ0, c
    simp only [named]
    iframe
    ipureintro; exact Hpb_inv
  iapply HΦ
  isplitr
  · ipureintro
    have He := Hvw.2.2.2 Hpnil
    unfold EtcdGrove.stLast at Hlast
    rw [Hli, Hlast, He, Hvw.1]
  unfold ownMemoryStorage
  simp only [named]
  iframe Hinit Hmu Hview Hsn
  ipureintro; exact Hbounded

end proof

end EtcdGrove
end Perennial
