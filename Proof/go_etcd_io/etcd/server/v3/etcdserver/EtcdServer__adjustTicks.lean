/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__adjustTicks.lean`: `s.adjustTicks()`
(`server.go`): the logger (`s.Logger()`, with a slot borrowed from `GoAttach`'s `lgMu` pool), the
cluster's size (`len(s.cluster.Members())`); a single member logs and fast-forwards its ticks
(`s.r.advanceTicks(ElectionTicks - 1)`); otherwise, the tick advance being off
(`InitialElectionTickAdvance` false, `srvMonitorsOff`), it logs and returns. Lean-first; until
prove-ps2-srv (2026-11-22) a names-only trust-boundary axiom.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__adjustTicks
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Logger
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__MemberID
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.raftNode__advanceTicks
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.tickToDur
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__Members
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Int
public import Spec.go_uber_org.zap.Logger__Info
public import GeneratedProof.go_etcd_io.etcd.client.pkg.v3.types

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

set_option maxHeartbeats 1600000 in
theorem EtcdServer.adjustTicks.wp_proof
    (hLg : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (hMembers : membership.RaftCluster.Members.spec (GF := GF) (hG := hG))
    (hMid : EtcdServer.MemberID.spec (GF := GF) (hG := hG))
    (hIDS : types.ID.String.spec (GF := GF) (hG := hG))
    (hZS : zap.String.spec (GF := GF) (hG := hG))
    (hZI : zap.Int'.spec (GF := GF) (hG := hG))
    (hTD : tickToDur.spec (GF := GF) (hG := hG))
    (hInfo : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (hAdv : raftNode.advanceTicks.spec (GF := GF) (hG := hG)) :
    EtcdServer.adjustTicks.spec (GF := GF) (hG := hG) := by
  intro on s E ρ Er γn
  wp_start as ⟨#Hreq, #HlgOk, #Hpool, H1, #Hoff, #Hrn⟩
  ihave ⟨⟨%rv, #Hrf⟩, -⟩ := (isServerReqM_split _ _ _ _).1 $$ Hreq
  iunfold srvReqFieldsAtM at Hrf
  icases Hrf with ⟨-, -, -, -, -, -, -, -, -, #Het, #Htm, -, -, -, -, #Hmid, -, #Hcl, -, #Hpeers,
    -⟩
  iunfold srvPeersOk at Hpeers
  icases Hpeers with ⟨-, #Hrc, -⟩
  iunfold srvMonitorsOff at Hoff
  icases Hoff with ⟨-, -, -, -, #Hie⟩
  iunfold srvLoggerOk at HlgOk
  icases HlgOk with ⟨%l, #Hlgf, #Hlgok⟩
  ihave #Pmb : isPkgInit (PROP := IProp GF)
    pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership $$ []
  · iPkgInit
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Ptypes : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.types $$ []
  · iPkgInit
  -- `lg := s.Logger()`, with a slot of `GoAttach`'s pool
  wp_auto_lc 1
  imod raftPool_borrowL (srvLgReader s) ⊤ (fun _ _ => CoPset.mem_full) $$ [Hlc1 H1] with ⟨Hlr, Hloan⟩
  · iframe Hlc1 H1; iexact Hpool
  wp_apply hLg s l $$ [Hlr] as ⟨-, Hlr⟩
  · iframe #; iframe Hlr
  iapply fupd_wp
  imod raftLoanL_giveBack (srvLgReader s) ⊤ (fun _ _ => CoPset.mem_full) $$ [Hloan Hlr] with H1
  · iframe
  imodintro
  (try wp_auto)
  -- `clusterN := len(s.cluster.Members())`
  wp_apply (membership.RaftCluster.Members.spec_static hMembers rv.cluster) $$ [] as %sl ⟨%ms, Hms⟩
  · iframe #
  iunfold membership.membersAt at Hms
  icases Hms with ⟨Hsl, -⟩
  ihave %Hsll := ownSlice_len $$ Hsl
  (try wp_auto)
  wp_if_destruct
  · -- a single member: log, then fast-forward
    wp_apply hMid s rv.memberID $$ []
    · iframe #
    -- `s.MemberID().String()`: `MethodResolve` of `types.ID`, whose underlying type is no interface
    haveI : go.NotInterface go.uint64 := ⟨by unfold go.uint64; trivial⟩
    wp_auto
    wp_apply_core hIDS rv.memberID
    · iframe #
    iintro %ids -
    (try wp_auto)
    wp_apply hZS as %f0 -
    (try wp_auto)
    wp_apply hZI as %f1 -
    (try wp_auto)
    wp_apply hTD as %d0 -
    (try wp_auto)
    wp_apply hZS as %f2 -
    (try wp_auto)
    wp_apply hZI as %f3 -
    (try wp_auto)
    wp_apply hTD as %d1 -
    (try wp_auto)
    wp_apply hZS as %f4 -
    (try wp_auto)
    wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field)
    isplitr
    · ipureintro; rfl
    iintro %fs ⟨-, -⟩
    (try wp_auto)
    wp_apply hInfo l _ _ $$ []
    · iframe #
    (try wp_auto)
    wp_apply hAdv Er γn (srvRAddr s) _ $$ []
    · iframe #
    (try wp_auto)
    iapply HΦ
    iexact H1
  · -- several members: the tick advance off (`srvMonitorsOff`), log and return
    (try wp_auto)
    wp_apply hZI as %f0 -
    (try wp_auto)
    wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field)
    isplitr
    · ipureintro; rfl
    iintro %fs ⟨-, -⟩
    (try wp_auto)
    wp_apply hInfo l _ _ $$ []
    · iframe #
    (try wp_auto)
    iapply HΦ
    iexact H1

end proof

end EtcdGrove
end Perennial
