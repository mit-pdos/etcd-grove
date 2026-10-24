/-
Proof of `bootstrapWALFromSnapshot(cfg, snapshot, ci)`
(`Spec/go_etcd_io/etcd/server/v3/etcdserver/bootstrapWALFromSnapshot.lean`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrapWALFromSnapshot
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrappedWAL__CommitedEntries
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrappedWAL__fillBackendAheadGap
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrappedWAL__NewConfigChangeEntries
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrappedWAL__AppendAndCommitEntries

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver
  go_etcd_io.etcd.server.v3.config go_etcd_io.etcd.server.v3.etcdserver.cindex
  go_etcd_io.raft.v3 go_uber_org

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

set_option maxHeartbeats 0 in
theorem bootstrapWALFromSnapshot.wp_proof
    (wp_CommitedEntries : bootstrappedWAL.CommitedEntries.spec (GF := GF))
    (wp_fillBackendAheadGap : bootstrappedWAL.fillBackendAheadGap.spec (GF := GF))
    (wp_NewConfigChangeEntries : bootstrappedWAL.NewConfigChangeEntries.spec (GF := GF))
    (wp_AppendAndCommitEntries : bootstrappedWAL.AppendAndCommitEntries.spec (GF := GF))
    (wp_ID_String : types.ID.String_ptr.spec (GF := GF))
    (wp_String : zap.String.spec (GF := GF))
    (wp_Uint64 : zap.Uint64.spec (GF := GF))
    (wp_Info : zap.Logger.Info.spec (GF := GF)) :
    bootstrapWALFromSnapshot.spec (GF := GF) := by
  intro cfg snapshot ci w st ents snap metaPtr hs0 es0 ccEnts sv mv ciIdx
    c1 es1 es2 es3 hs3 esFinal hsFinal Hlg Hwf0 Hforce
  wp_start as Hpre
  iNamed Hpre
  ihave #Hpkgr : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  ihave #Hpkgt : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.types $$ []
  · iPkgInit
  ihave #Hpkgz : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  (try wp_auto)
  iunfold openWALFromSnapshotOk at Hopen
  wp_apply Hopen as ⟨#Hsave, Hst, Hents, Hcap, #Hsnap, Hmeta⟩
  (try wp_auto)
  obtain ⟨bw_ptr, rfl⟩ : ∃ bw_ptr, bw_ptr = «$r0_ptr» := ⟨«$r0_ptr», rfl⟩
  irename «$r0» => Hbw
  cases Hif : cfg.ForceNewCluster'
  case true =>
    -- `cfg.ForceNewCluster' = true`
    (try wp_auto)
    obtain ⟨Hc1_ge, Hlen_bound, Hc1_u64⟩ := Hforce Hif
    icases Hci with (%Hfc | #Hci)
    · cases Hfc
    icases Hcc with (%Hfc | #Hcc)
    · cases Hfc
    iunfold ciConsistentIndexOk at Hci
    wp_apply Hci
    (try wp_auto)
    wp_apply wp_hsPts_GetCommit st (DFrac.own 1) hs0 $$ [$Hpkgr $Hst] as Hst
    (try wp_auto)
    wp_apply wp_max2_uint64 hs0.Commit' ciIdx
    (try wp_auto)
    icases hsPts_not_null st (DFrac.own 1) hs0 $$ Hst with ⟨%Hstnn, Hst⟩
    icases hsPts_Commit_acc st hs0 $$ Hst with ⟨%pc, HstC, Hst_close⟩
    (try wp_auto)
    imod cellRO_alloc «$r0_ptr» c1 $$ «$r0» with #HcC1
    ihave Hst := Hst_close $$ %«$r0_ptr» %c1 HstC HcC1
    wp_apply wp_CommitedEntries bw_ptr (DFrac.own 1) (DFrac.own 1)
      (bootstrappedWAL.mk cfg.Logger' true w st ents snap metaPtr)
      sv { hs0 with Commit' := c1 } es0 Hlg Hwf0 Hc1_ge
      $$ [$Hpkg $Hbw $Hst $Hents $Hcap]
      as %ents1 ⟨Hbw, Hst, Hents1, Hcap1⟩
    (try wp_auto)
    have Hwf1 : PlogWf (snapId sv) es1 :=
      PlogWf_take (snapId sv) es0 (uint.Z c1 - uint.Z sv.Metadata'.Index').toNat Hwf0
    have Hlast1_le : uint.Z (walLastIndex sv es1) ≤ uint.Z c1 := by
      have Hlast1 := walLastIndex_plogWf sv es1 Hwf1
      have Htake_len : es1.length ≤ (uint.Z c1 - uint.Z sv.Metadata'.Index').toNat :=
        List.length_take_le _ _
      omega
    have Hc1_lt : uint.Z ({ hs0 with Commit' := c1 } : HardStateM).Commit' + 1 < 2 ^ 64 := by
      simp only []; omega
    have Hgap_len : (es1.length : Int) +
        (uint.Z ({ hs0 with Commit' := c1 } : HardStateM).Commit' - uint.Z (walLastIndex sv es1)) < 2 ^ 63 := by
      simp only []; omega
    wp_apply wp_fillBackendAheadGap bw_ptr
      (bootstrappedWAL.mk cfg.Logger' true w st ents1 snap metaPtr)
      sv { hs0 with Commit' := c1 } es1 Hlg Hlast1_le Hc1_lt Hgap_len
      $$ [$Hpkg $Hbw $Hst $Hents1 $Hcap1 $Hsnap $Hsave]
      as ⟨%ents2, Hbw, Hst, Hents2, Hcap2⟩
    (try wp_auto)
    obtain ⟨Hwf2, Hlast2⟩ := plogWf_append_gapEntries sv es1 hs0.Term' c1 Hwf1 Hlast1_le
    wp_apply wp_NewConfigChangeEntries bw_ptr (DFrac.own 1) (DFrac.own 1) (DFrac.own 1) (DFrac.own 1)
      (bootstrappedWAL.mk cfg.Logger' true w st ents2 snap metaPtr)
      sv { hs0 with Commit' := c1 } es2 ccEnts mv Hlg
      $$ [$Hpkg $Hbw $Hst $Hents2 $Hmeta $Hsnap $Hcc]
      as %cs ⟨Hbw, Hst, Hents2, Hmeta, Hcs, Hcscap, %Hcc_props⟩
    (try wp_auto)
    have Hlen_app2 : (es2.length : Int) + (ccEnts.length : Int) < 2 ^ 63 := by
      have : es2.length = es1.length + (gapEntries hs0.Term' (walLastIndex sv es1) c1).length := by
        simp [es2]
      rw [gapEntries_length] at this
      omega
    wp_apply wp_AppendAndCommitEntries bw_ptr
      (bootstrappedWAL.mk cfg.Logger' true w st ents2 snap metaPtr)
      cs (DFrac.own 1) { hs0 with Commit' := c1 } es2 ccEnts Hlen_app2
      $$ [$Hpkg $Hbw $Hst $Hents2 $Hcap2 $Hcs $Hsave]
      as ⟨%ents3, Hbw, Hst, Hents3, Hcap3, -⟩
    (try wp_auto)
    icases typedPointsto_not_null_dup _ _ _ $$ Hmeta with ⟨Hmeta, %Hmnn⟩
    iStructNamedSuffix Hmeta "M"
    (try wp_auto)
    wp_apply wp_ID_String _ (DFrac.own 1) mv.clusterID' $$ [$Hpkgt $clusterIDM] as %s_cid ⟨clusterIDM, -⟩
    (try wp_auto)
    wp_apply wp_String $$ [$Hpkgz] as %f0 -
    (try wp_auto)
    wp_apply wp_ID_String _ (DFrac.own 1) mv.nodeID' $$ [$Hpkgt $nodeIDM] as %s_nid ⟨nodeIDM, -⟩
    (try wp_auto)
    wp_apply wp_String $$ [$Hpkgz] as %f1 -
    (try wp_auto)
    wp_apply wp_Uint64 $$ [$Hpkgz] as %f2 -
    (try wp_auto)
    wp_apply wp_hsPts_GetCommit st (DFrac.own 1) hs3 $$ [$Hpkgr $Hst] as Hst
    (try wp_auto)
    wp_apply wp_Uint64 $$ [$Hpkgz] as %f3 -
    (try wp_auto)
    wp_apply wp_slice_literal
    isplitr; · ipureintro; rfl
    iintro %fsl ⟨-, -⟩
    (try wp_auto)
    wp_apply (wp_Info cfg.Logger') $$ [$Hpkgz]
    · ipureintro; exact Hlg
    (try wp_auto)
    ihave Hmeta : metaPtr ↦ mv $$ [nodeIDM clusterIDM]
    · iapply typedPointsto_combine _ _ _ Hmnn
      simp only [TypedPointsto.typedPointstoDef, named]
      iframe
    have Hwf3 : PlogWf (snapId sv) es3 := by
      have Hlast2_wf := walLastIndex_plogWf sv es2 Hwf2
      have Hlast2' : uint.Z (walLastIndex sv es2) = uint.Z c1 := Hlast2
      apply plogWf_append_consecutive (snapId sv) es2 ccEnts Hwf2
      intro i e he
      have hcc := Hcc_props.2 i e he
      simp only [snapId] at hcc ⊢
      omega
    iapply HΦ
    simp only [esFinal, hsFinal, Hif, ↓reduceIte]
    iexists ents3
    iframe Hbw Hsave Hst Hents3 Hcap3 Hsnap Hmeta
    ipureintro; exact Hwf3
  case false =>
    -- `cfg.ForceNewCluster' = false`
    (try wp_auto)
    icases typedPointsto_not_null_dup _ _ _ $$ Hmeta with ⟨Hmeta, %Hmnn⟩
    iStructNamedSuffix Hmeta "M"
    (try wp_auto)
    wp_apply wp_ID_String _ (DFrac.own 1) mv.clusterID' $$ [$Hpkgt $clusterIDM] as %s_cid ⟨clusterIDM, -⟩
    (try wp_auto)
    wp_apply wp_String $$ [$Hpkgz] as %f0 -
    (try wp_auto)
    wp_apply wp_ID_String _ (DFrac.own 1) mv.nodeID' $$ [$Hpkgt $nodeIDM] as %s_nid ⟨nodeIDM, -⟩
    (try wp_auto)
    wp_apply wp_String $$ [$Hpkgz] as %f1 -
    (try wp_auto)
    wp_apply wp_hsPts_GetCommit st (DFrac.own 1) hs0 $$ [$Hpkgr $Hst] as Hst
    (try wp_auto)
    wp_apply wp_Uint64 $$ [$Hpkgz] as %f2 -
    (try wp_auto)
    wp_apply wp_slice_literal
    isplitr; · ipureintro; rfl
    iintro %fsl ⟨-, -⟩
    (try wp_auto)
    wp_apply (wp_Info cfg.Logger') $$ [$Hpkgz]
    · ipureintro; exact Hlg
    (try wp_auto)
    ihave Hmeta : metaPtr ↦ mv $$ [nodeIDM clusterIDM]
    · iapply typedPointsto_combine _ _ _ Hmnn
      simp only [TypedPointsto.typedPointstoDef, named]
      iframe
    iapply HΦ
    simp only [esFinal, hsFinal, Hif, Bool.false_eq_true, ↓reduceIte]
    iexists ents
    iframe Hbw Hsave Hst Hents Hcap Hsnap Hmeta
    ipureintro; exact Hwf0

end proof

end EtcdGrove
end Perennial
