/-
Port of election_proof/proof_MemoryStorage__Snapshot.v.
-/
module

public import Spec.go_etcd_io.raft.v3.MemoryStorage__Snapshot

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

theorem MemoryStorage.Snapshot.wp_proof :
    MemoryStorage.Snapshot.spec (GF := GF) (hG := hG) := by
  intro ms γs σ esu
  wp_start as ⟨Hms, #Hesu⟩
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
  -- the contents have the view's snapshot (2026-10-10)
  icases memView_agree γs σ σ0 $$ Hview Hgs_inv with ⟨%Hvw, Hview, Hgs_inv⟩
  iunfold memstorageFields at Hfields_inv
  icases Hfields_inv with ⟨%hs, %snap, %es, %dummy, %cs, %voters, Hfields_inv⟩
  iNamed Hfields_inv
  wp_auto
  icases Hvoters with #Hvoters
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hgs_inv HhardState Hsnapshot Hents_f Hents Hents_cap HcallStats]
  · inext
    unfold memstorageInv memstorageFields
    iexists σ0
    iframe Hgs_inv
    isplitl
    · iexists hs, snap, es, dummy, _, voters
      iframe # ∗
      ipureintro; exact ⟨Hsnap_id, Hdummy⟩
    ipureintro; exact Hpb_inv
  iapply HΦ
  isplitl [Hview]
  · unfold ownMemoryStorage
    iframe # ∗
    ipureintro; exact Hbounded
  iright
  isplitr
  · ipureintro
    exact ⟨rfl, Hsnap_id.trans Hvw.2.1⟩
  iexists voters
  iexact Hvoters

end proof

end EtcdGrove
end Perennial
