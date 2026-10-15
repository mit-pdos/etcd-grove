/-
Port of election_proof/proof_MemoryStorage__Snapshot.v.
-/
module

public import Raft37.Spec.go_etcd_io.raft.v3.MemoryStorage__Snapshot
public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.EnsureSnapshot
public import Spec.google_golang_org.protobuf.proto.CloneSnapshot

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

theorem MemoryStorage.Snapshot.wp_proof
    (wp_EnsureSnapshot : raftpb.EnsureSnapshot.spec (GF := GF) (hG := hG))
    (wp_CloneSnapshot : proto.CloneSnapshot.spec (GF := GF) (hG := hG)) :
    MemoryStorage.Snapshot.spec (GF := GF) (hG := hG) := by
  intro ms γs σ esu
  wp_start as ⟨Hms, #Hesu⟩
  iunfold ownMemoryStorage at Hms
  icases Hms with ⟨#Hinit, #Hmu, Hview, Hsn, %Hbounded⟩
  iunfold memSnapOwn at Hsn
  icases Hsn with ⟨%sp, %sv, Hsnapshot, Hsnap, %Hsnap_id⟩
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
  iunfold memstorageInv at Hinv
  icases Hinv with ⟨%σ0, Hinv⟩
  iNamedSuffix Hinv "_inv"
  iunfold memstorageFields at Hfields_inv
  icases Hfields_inv with ⟨%hp, %es, %dummy, %nfi, %nli, %nen, %nte, %nsn, Hfields_inv⟩
  iNamed Hfields_inv
  wp_auto
  wp_apply wp_EnsureSnapshot sp (some sv) $$ [Hsnap] as %r ⟨Hr, -⟩
  · simp only [snapOpt]; iexact Hsnap
  ihave Hr := ownSnapE_weaken $$ Hr
  simp only [Option.getD_some]
  wp_apply wp_CloneSnapshot.1 r (DFrac.own 1) sv $$ [Hr] as %p' ⟨Hr, Hp'⟩
  · iframe Hr
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hgs_inv HhardState Hents_f Hents Hents_cap Hcs_firstIndex Hcs_lastIndex Hcs_entries Hcs_term Hcs_snapshot]
  · inext
    unfold memstorageInv memstorageFields
    iexists σ0
    iframe Hgs_inv
    isplitl
    · iexists hp, es, dummy, _, _, _, _, _
      iframe # ∗
      ipureintro; exact Hdummy
    ipureintro; exact Hpb_inv
  iapply HΦ
  isplitl [Hview Hsnapshot Hr]
  · unfold ownMemoryStorage memSnapOwn
    iframe # ∗
    isplitl
    · iexists r, sv
      iframe
      ipureintro; exact Hsnap_id
    ipureintro; exact Hbounded
  iright
  isplitr
  · ipureintro; rfl
  iexists sv
  iframe Hp'
  ipureintro
  exact ⟨Hsnap_id.1, Hsnap_id.2.2, Hsnap_id.2.1⟩

end proof

end EtcdGrove
end Perennial
