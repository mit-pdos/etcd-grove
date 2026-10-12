/-
Port of election_proof/proof_MemoryStorage__FirstIndex.v.
-/
module

public import Spec.go_etcd_io.raft.v3.MemoryStorage__FirstIndex
public import Spec.go_etcd_io.raft.v3.MemoryStorage__firstIndex

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

theorem MemoryStorage.FirstIndex.wp_proof
    (wp_MemoryStorage_firstIndex : MemoryStorage.firstIndex.spec (GF := GF) (hG := hG)) :
    MemoryStorage.FirstIndex.spec (GF := GF) (hG := hG) := by
  intro ms γs σ
  wp_start as Hpre
  iNamed Hpre
  iunfold ownMemoryStorage at Hms
  iNamed Hms
  wp_auto
  wp_apply wp_with_defer as %defer defer
  -- `ms.Lock()`: the method of the embedded `sync.Mutex`
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
  iunfold memstorageInv at Hinv
  icases Hinv with ⟨%σ0, Hinv⟩
  iNamedSuffix Hinv "_inv"
  -- the contents agree with the view on the boundary (2026-10-10)
  icases memView_agree γs σ σ0 $$ Hview Hgs_inv with ⟨%Hvw, Hview, Hgs_inv⟩
  iNamed Hfields_inv
  icases typedPointsto_not_null_dup _ _ _ $$ HcallStats with ⟨HcallStats, %Hcs_nn⟩
  iStructNamed HcallStats
  wp_auto
  ihave Hf : memstorageFields ms σ0 $$ [HhardState Hsnapshot Hvoters Hents_f Hents Hents_cap firstIndex lastIndex term entries snapshot initialState]
  · unfold memstorageFields
    iexists hs, snap, es, dummy, { cs with firstIndex' := cs.firstIndex' + W64 1 }, voters
    iframe
    isplitr
    · ipureintro; exact Hsnap_id
    isplitr
    · ipureintro; exact Hdummy
    iapply typedPointsto_combine _ _ _ Hcs_nn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  wp_apply wp_MemoryStorage_firstIndex ms σ0 Hpb_inv $$ [$Hf] as %fi ⟨%Hfi, Hf⟩
  -- the deferred `ms.Unlock()`
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hgs_inv Hf]
  · unfold memstorageInv
    iexists σ0
    iframe
    ipureintro; exact Hpb_inv
  iapply HΦ
  isplitr
  · ipureintro; rw [← Hvw.1]; exact Hfi
  unfold ownMemoryStorage
  iframe # ∗
  ipureintro
  exact Hbounded

end proof

end EtcdGrove
end Perennial
