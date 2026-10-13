/- `MemoryStorage.ApplySnapshot` (`storage.go:207`), proved 2026-10-12 (Lean-first). -/
module

public import Spec.go_etcd_io.raft.v3.MemoryStorage__ApplySnapshot

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

theorem MemoryStorage.ApplySnapshot.wp_proof :
    MemoryStorage.ApplySnapshot.spec (GF := GF) (hG := hG) := by
  intro ms γs σ hs snap snap' voters eood Hidle Hbnd
  wp_start as ⟨Hms, Hmeta, #Hvoters', #Herr⟩
  iunfold ownMemoryStorage at Hms
  icases Hms with ⟨#Hinit, #Hmu, Hview, %Hbounded⟩
  iunfold memStorMeta at Hmeta
  icases Hmeta with ⟨%n, %voters0, Hmeta⟩
  iNamedSuffix Hmeta "_m"
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
  iunfold memstorageInv at Hinv
  icases Hinv with ⟨%σp, Hinv⟩
  iNamedSuffix Hinv "_inv"
  icases memView_agree γs σ σp $$ Hview Hgs_inv with ⟨%Hvw, Hview, Hgs_inv⟩
  have Hσp : σp = σ := Hvw.2.2.2 Hidle
  subst Hσp
  iunfold memstorageFields at Hfields_inv
  icases Hfields_inv with ⟨%hs0, %snap0, %es, %dummy, %nfi, %nli, %nen, %nte, %nsn, %voters1,
    Hfields_inv⟩
  iNamed Hfields_inv
  -- the two halves of `snapshot` make the whole field
  icombine Hsnapshot_m Hsnapshot gives %Heq
  subst Heq
  ihave Hsnap := (ptsto_halves _ _).2 $$ [Hsnapshot_m Hsnapshot]
  · iframe Hsnapshot_m Hsnapshot
  have Hss : σp.ss.index' = snap.Metadata'.Index' := by rw [← Hsnap_id]; rfl
  wp_auto
  wp_if_destruct
  rotate_left
  wp_if_destruct
  · -- `ErrSnapOutOfDate`: nothing changes
    icases (ptsto_halves _ _).1 $$ Hsnap with ⟨Hsnapshot_m, Hsnapshot⟩
    wp_method_call
    wp_call
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hgs_inv HhardState Hsnapshot Hvoters Hents_f
      Hents Hents_cap Hcs_firstIndex Hcs_lastIndex Hcs_entries Hcs_term Hcs_snapshot]
    · inext
      unfold memstorageInv memstorageFields
      iexists σp
      iframe Hgs_inv
      isplitl
      · iexists hs0, snap, es, dummy, nfi, nli, nen, nte, nsn, voters1
        iframe # ∗
        ipureintro; exact ⟨Hsnap_id, Hdummy⟩
      ipureintro; exact Hpb_inv
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rw [Hss]; exact ⟨by assumption, Hif, rfl⟩
    isplitl [Hview]
    · unfold ownMemoryStorage
      iframe # ∗
      ipureintro; exact Hbounded
    unfold memStorMeta
    iexists n, voters0
    iframe # ∗
  -- the snapshot is applied (either because the storage had none or because it is newer)
  all_goals
    have Hnot : ¬ (σp.ss.index' ≠ W64 0 ∧
        uint.Z snap'.Metadata'.Index' ≤ uint.Z σp.ss.index') := by
      rw [Hss]; intro ⟨h1, h2⟩
      first
        | exact h1 ‹snap.Metadata'.Index' = W64 0›
        | exact ‹¬ uint.Z snap'.Metadata'.Index' ≤ uint.Z snap.Metadata'.Index'› h2
    wp_apply wp_slice_literal
    try (isplitr; (ipureintro; rfl))
    iintro %sl_ptr ⟨Hsl, Hsl_cap⟩
    imod ownSlice_persist $$ Hsl with #Hsl
    wp_auto
    imod memView_set γs σp σp (memStorApplied snap') Hidle rfl $$ Hview Hgs_inv
      with ⟨-, Hview, Hgs_inv⟩
    icases (ptsto_halves _ _).1 $$ Hsnap with ⟨Hsnapshot_m, Hsnapshot⟩
    wp_method_call
    wp_call
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hgs_inv HhardState Hsnapshot Hents_f
      Hsl_cap Hcs_firstIndex Hcs_lastIndex Hcs_entries Hcs_term Hcs_snapshot]
    · inext
      unfold memstorageInv memstorageFields
      iexists memStorApplied snap'
      iframe Hgs_inv
      isplitl
      · simp only [memStorApplied, snapId]
        iexists hs0, snap', _, _, nfi, nli, nen, nte, nsn, voters
        iframe # ∗
        ipureintro; exact ⟨rfl, rfl, rfl⟩
      ipureintro; simp only [memStorApplied, snapId, List.length_nil]; word
    iapply HΦ
    iright
    isplitr
    · ipureintro; exact ⟨Hnot, rfl⟩
    isplitl [Hview]
    · unfold ownMemoryStorage
      iframe # ∗
      ipureintro; simp only [memStorApplied, snapId, List.length_nil]; word
    unfold memStorMeta
    iexists n, voters
    iframe # ∗

end proof

end EtcdGrove
end Perennial
