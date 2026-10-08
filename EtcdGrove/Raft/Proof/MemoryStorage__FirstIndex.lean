/-
Port of election_proof/proof_MemoryStorage__FirstIndex.v.
-/
import EtcdGrove.Raft.Spec.MemoryStorage__FirstIndex
import EtcdGrove.Raft.Spec.MemoryStorage__firstIndex

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

theorem MemoryStorage.FirstIndex.wp_proof
    (wp_MemoryStorage_firstIndex : MemoryStorage.firstIndex.spec (GF := GF) (hG := hG)) :
    MemoryStorage.FirstIndex.spec (GF := GF) (hG := hG) := by
  intro ms ⟨prev, ents, ss⟩
  dsimp only at *
  wp_start as Hpre
  iNamed Hpre
  iunfold ownMemoryStorage at Hms
  icases Hms with ⟨%γ, Hms⟩
  iNamed Hms
  wp_apply wp_with_defer as %defer defer
  -- `ms.Lock()`: the method of the embedded `sync.Mutex`
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
  iNamedSuffix Hinv "_inv"
  ihave %Heq := ghostVar_agree $$ Hgs Hgs_inv
  subst Heq
  iNamed Hfields_inv
  icases typedPointsto_not_null_dup _ _ _ $$ HcallStats with ⟨HcallStats, %Hcs_nn⟩
  iStructNamed HcallStats
  wp_auto
  ihave Hf : memstorageFields ms { prev := prev, ents := ents, ss := ss } $$ [HhardState Hsnapshot Hvoters Hents_f Hents firstIndex lastIndex term entries snapshot initialState]
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
  wp_apply wp_MemoryStorage_firstIndex ms { prev := prev, ents := ents, ss := ss } Hbounded $$ [$Hf] as %fi ⟨%Hfi, Hf⟩
  -- the deferred `ms.Unlock()`
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hgs_inv Hf]
  · unfold memstorageInv
    iexists { prev := prev, ents := ents, ss := ss }
    iframe
  iapply HΦ
  isplitr
  · ipureintro; exact Hfi
  unfold ownMemoryStorage
  iexists γ
  iframe # ∗
  ipureintro
  exact ⟨Hbounded, Hss⟩

end proof

end EtcdGrove
end Perennial
