/-
The proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/bootstrapRaft.lean` (claim #34, stage 4,
2026-11-25): the new cluster's branch (`!bwal.haveWAL && cfg.NewCluster`, `bootstrap.go:538-539`), over
the cluster's `MemberIDs` (its ids are `bootGo.ps`: `bootGo.ids_eq_ps`) and `bootstrapRaftFromCluster`.
Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrapRaft
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrapRaftFromCluster
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__MemberIDsMem

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [MemStorReg GF]

theorem bootstrapRaft.wp_proof
    (hIDs : membership.RaftCluster.MemberIDs.specMem (GF := GF) (hG := hG))
    (hFC : bootstrapRaftFromCluster.spec (GF := GF) (hG := hG)) :
    bootstrapRaft.spec (GF := GF) (hG := hG) := by
  intro cfg U c w bc bw dq dqw Hnc Hcok Hmok Hidr Hune Hhw Hst Hents Hsnap
  wp_start as ⟨#Hzlg, Hc, Hw, #Hrc, #Hcid, Hmem, Hauth⟩
  ihave #Hmpkg : isPkgInit (PROP := IProp GF)
      pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership $$ []
  · iPkgInit
  icases typedPointsto_not_null_dup _ _ _ $$ Hc with ⟨Hc, %Hcnn⟩
  iStructNamedPrefix Hc "C"
  icases typedPointsto_not_null_dup _ _ _ $$ Hw with ⟨Hw, %Hwnn⟩
  iStructNamedPrefix Hw "W"
  wp_auto
  ipersist cfg
  ihave #Hcf := cfg
  iStructNamedSuffix Hcf "F"
  rw [Hhw]
  try rw [Hnc]
  try wp_auto
  -- `cluster.cl.MemberIDs()`
  wp_apply (hIDs bc.cl' (bootGo.memMap U cfg.InitialClusterToken')) $$ [Hmem]
    as %s ⟨%ids, Hs, %Hids, Hmem⟩
  · iframe Hmem; iframe #
  have hids := bootGo.ids_eq_ps U cfg.InitialClusterToken' Hmok.2.1 ids Hids.1 Hids.2
  subst hids
  try wp_auto
  ihave Hw : (w ↦{dqw} bw : IProp GF) $$ [Wlg WhaveWAL Ww Wst Wents Wsnapshot Wmeta']
  · iapply typedPointsto_combine _ _ _ Hwnn
    simp only [TypedPointsto.typedPointstoDef, Hhw]
    iframe
  -- `bootstrapRaftFromCluster(cfg, cluster.cl, ids, bwal)`
  wp_apply (hFC cfg U bc.cl' s w bw (DFrac.own 1) dqw Hcok Hmok Hidr Hune Hst Hents Hsnap)
    $$ [Hs Hw Hmem Hauth] as %r ⟨%bv, Hr, Hb, -, Hw, Hmem⟩
  · iframe Hs Hw Hmem Hauth; iframe #
  try wp_auto
  iapply HΦ
  iexists bv
  iframe Hr Hb Hw Hmem
  iapply typedPointsto_combine _ _ _ Hcnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

end proof

end EtcdGrove
end Perennial
