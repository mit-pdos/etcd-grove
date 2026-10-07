/-
Port of election_proof/proof_MemoryStorage__Snapshot.v.
-/
import EtcdGrove.Raft.ElectionProof.Spec.MemoryStorage__Snapshot

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

theorem MemoryStorage.Snapshot.wp_proof :
    MemoryStorage.Snapshot.spec (GF := GF) (hG := hG) := by
  intro ms prev ents ss esu
  wp_start as ⟨Hms, #Hesu⟩
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
  icombine Hgs Hgs_inv gives % ⟨_, Heq⟩
  simp only [Prod.mk.injEq] at Heq
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := Heq
  wp_auto
  icases Hvoters with #Hvoters
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hgs_inv HhardState Hsnapshot Hents_f Hents HcallStats]
  · inext
    unfold memstorageInv memstorageFields
    iexists prev, ents, ss
    iframe Hgs_inv
    iexists hs, snap, es, dummy, _, voters
    iframe # ∗
    ipureintro; exact ⟨Hsnap_id, Hdummy⟩
  iapply HΦ
  isplitl [Hgs]
  · unfold ownMemoryStorage
    iexists γ
    iframe # ∗
    ipureintro; exact ⟨Hbounded, Hss⟩
  iright
  isplitr
  · ipureintro
    refine ⟨rfl, Hsnap_id, ?_⟩
    rw [← Hsnap_id] at Hss
    exact Hss
  iexists voters
  iexact Hvoters

end proof

end EtcdGrove
end Perennial
