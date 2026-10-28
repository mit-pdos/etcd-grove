/- `MemoryStorage.SetHardState` (`storage.go:127`), proved 2026-10-12 (Lean-first). -/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.MemoryStorage__SetHardState

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem MemoryStorage.SetHardState.wp_proof :
    MemoryStorage.SetHardState.spec (GF := GF) (hG := hG) := by
  intro ms γs hs st hs'
  wp_start as ⟨Hmeta, #Hst⟩
  iunfold memStorMeta at Hmeta
  icases Hmeta with ⟨%n, %hp, Hmeta⟩
  iNamed Hmeta
  wp_auto
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
  iunfold memstorageInv at Hinv
  icases Hinv with ⟨%σp, %c, Hinv⟩
  iNamedSuffix Hinv "_inv"
  iunfold memstorageFields at Hfields_inv
  icases Hfields_inv with ⟨%hp0, %es, %dummy, %nfi, %nli, %nen, %nte, %nsn, Hfields_inv⟩
  iNamedSuffix Hfields_inv "_f"
  icombine HhardState HhardState_f gives %Heq
  subst Heq
  ihave HhardState := (ptsto_halves _ _).2 $$ [HhardState HhardState_f]
  · iframe HhardState HhardState_f
  wp_auto
  icases (ptsto_halves _ _).1 $$ HhardState with ⟨HhardState, HhardState_f⟩
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hgs_inv HhardState_f
    Hents_f_f Hents_f Hents_cap_f Hcs_firstIndex_f Hcs_lastIndex_f Hcs_entries_f Hcs_term_f
    Hcs_snapshot_f Hcut_inv]
  · inext
    unfold memstorageInv memstorageFields
    iexists σp, c
    iframe Hgs_inv Hcut_inv
    isplitl
    · iexists st, es, dummy, nfi, nli, nen, nte, nsn
      iframe
      ipureintro; exact Hdummy_f
    ipureintro; exact Hpb_inv
  iapply HΦ
  unfold memStorMeta
  iexists n, st
  iframe # ∗

end proof

end EtcdGrove
end Perennial
