/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/bootstrapWALFromBackend.lean`
(etcd-io/etcd#19693; pr-verify, 2026-10-17). Lean-first (no Rocq counterpart). Its callees:
`schema.ReadConsistentIndex` (proved), `schema.ReadConfStateFromBackend` (proved, over the trust
boundary `UnsafeConfStateFromBackend`), `openWALFromPosition` (the trust boundary), raft's
`HardState.GetCommit` (proved), and the log line's `zap` and `types.ID.String` (trust boundary).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrapWALFromBackend
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.ReadConsistentIndex
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.ReadConfStateFromBackend
public import Spec.go_etcd_io.raft.v3.raftpb.HardState__GetCommit
public import Spec.go_uber_org.zap.Logger__Info
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Uint64
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String_ptr

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `p.GetCommit()` on a hard state that is `nil` or read-only (`hsOpt`): the record's commit
index (raft's getter, both cases). -/
theorem raftpb.HardState.wp_GetCommit_opt
    (wp_GetCommit : raftpb.HardState.GetCommit.spec (GF := GF) (hG := hG))
    (p : Loc) (hs : HardStateM) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ hsOpt p hs }}
      (App (Val (p @!! go.GoType.PointerType raftpb.HardState.ty @!! go!"GetCommit")) (Val #()))
    {{ RET #hs.Commit'; True }} := by
  iintro %Φ ⟨#Hpkg, Hst⟩ HΦ
  iunfold hsOpt at Hst
  icases Hst with (⟨%Hstn, %Hhs⟩ | #Hro)
  · subst Hstn; subst Hhs
    iapply wp_GetCommit.2 $$ [] HΦ
    iexact Hpkg
  · iapply (wp_GetCommit.1 p hs) $$ [] HΦ
    iframe Hpkg Hro

set_option maxHeartbeats 0 in
theorem bootstrapWALFromBackend.wp_proof
    (wp_RCI : schema.ReadConsistentIndex.spec (GF := GF) (hG := hG))
    (wp_RCS : schema.ReadConfStateFromBackend.spec (GF := GF) (hG := hG))
    (wp_open : openWALFromPosition.spec (GF := GF) (hG := hG))
    (wp_GetCommit : raftpb.HardState.GetCommit.spec (GF := GF) (hG := hG))
    (wp_Info : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (wp_String : zap.String.spec (GF := GF) (hG := hG))
    (wp_Uint64 : zap.Uint64.spec (GF := GF) (hG := hG))
    (wp_IDString : types.ID.String_ptr.spec (GF := GF) (hG := hG)) :
    bootstrapWALFromBackend.spec (GF := GF) (hG := hG) := by
  intro cv be m0 Hforce Hlg
  wp_start as #Hbe
  iunfold bootBackendOk at Hbe
  icases Hbe with ⟨%bi, %Hbi, #HReadTx⟩
  subst Hbi
  ihave #Hsch : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema $$ []
  · iPkgInit
  (try wp_auto)
  -- `schema.ReadConsistentIndex(be.ReadTx())`: the backend's position
  wp_apply HReadTx as %rt ⟨#Hmrt, #Hcrt⟩
  wp_apply_core (wp_RCI rt ⊤ (fun m => iprop(⌜m = m0⌝))) $$ [] [HΦ be cfg]
  · iframe Hsch Hmrt
  iapply readCIAU_const
  (try wp_auto)
  -- `schema.ReadConfStateFromBackend(cfg.Logger, be.ReadTx())`
  wp_apply HReadTx as %rt2 ⟨#Hmrt2, #Hcrt2⟩
  wp_apply (wp_RCS cv.Logger' rt2) as %cs Hcs
  · iframe #
  (try wp_auto)
  -- `openWALFromPosition(cfg, pos)`
  wp_apply wp_open as %w %st %ents %mdp ⟨%hs, %p, %mv, #Hst, Hents, %Hafter, Hmd⟩
  (try wp_auto)
  rw [Hforce]
  (try wp_auto)
  icases typedPointsto_not_null_dup _ _ _ $$ Hmd with ⟨Hmd, %Hmdnn⟩
  iStructNamedSuffix Hmd "M"
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  wp_apply wp_IDString $$ [$clusterIDM] as %s1 clusterIDM
  wp_apply wp_String as %f0 -
  (try wp_auto)
  wp_apply wp_IDString $$ [$nodeIDM] as %s2 nodeIDM
  wp_apply wp_String as %f1 -
  (try wp_auto)
  -- `bwal.st.GetCommit()`: the WAL's hard state, `nil` or read-only
  wp_apply (raftpb.HardState.wp_GetCommit_opt wp_GetCommit st hs) $$ []
  · iframe #
  wp_apply wp_Uint64 as %f2 -
  (try wp_auto)
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %fsl ⟨-, -⟩
  (try wp_auto)
  wp_apply wp_Info _ _ _ $$ []
  · iframe #; ipureintro; exact Hlg
  (try wp_auto)
  ihave Hmd : mdp ↦ mv $$ [nodeIDM clusterIDM]
  · iapply typedPointsto_combine _ _ _ Hmdnn
    simp only [TypedPointsto.typedPointstoDef, named]
    iframe
  iapply HΦ
  iexists _, hs, p, mv
  iframe «$r0» Hcs Hst Hents Hmd
  ipureintro
  exact ⟨⟨rfl, rfl, rfl⟩, Hafter⟩

end proof

end EtcdGrove
end Perennial
