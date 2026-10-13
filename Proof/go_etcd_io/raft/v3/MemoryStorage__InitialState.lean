/- `MemoryStorage.InitialState` (`storage.go:121`), proved 2026-10-12 (Lean-first). -/
module

public import Spec.go_etcd_io.raft.v3.MemoryStorage__InitialState

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

theorem MemoryStorage.InitialState.wp_proof :
    MemoryStorage.InitialState.spec (GF := GF) (hG := hG) := by
  intro ms γs hs snap
  wp_start as Hmeta
  iunfold memStorMeta at Hmeta
  icases Hmeta with ⟨%n, %voters, Hmeta⟩
  iNamed Hmeta
  wp_auto
  -- a nested field load through a half points-to: split the snapshot, then its metadata
  icases typedPointsto_not_null_dup _ _ _ $$ Hsnapshot with ⟨Hsnapshot, %Hs_nn⟩
  iStructNamedSuffix Hsnapshot "_s"
  icases typedPointsto_not_null_dup _ _ _ $$ Metadata_s with ⟨Metadata_s, %Hm_nn⟩
  iStructNamedSuffix Metadata_s "_m"
  wp_auto
  iapply HΦ
  ihave Metadata_s : (ms.[MemoryStorage, go!"snapshot"]).[raftpb.Snapshot, go!"Metadata"]
      ↦{DFrac.own (1 : Qp).half} snap.Metadata' $$ [ConfState_m Index_m Term_m]
  · iapply typedPointsto_combine _ _ _ Hm_nn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  ihave Hsnapshot : ms.[MemoryStorage, go!"snapshot"] ↦{DFrac.own (1 : Qp).half} snap
      $$ [Data_s Metadata_s]
  · iapply typedPointsto_combine _ _ _ Hs_nn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  unfold memStorMeta
  iexists _, voters
  iframe # ∗

end proof

end EtcdGrove
end Perennial
