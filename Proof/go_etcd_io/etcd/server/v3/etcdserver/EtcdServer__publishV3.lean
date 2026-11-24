/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__publishV3.lean` (`server.go`), over its body
(prove-ps2-srvgoroutines, 2026-11-24, etcd-grove#42; until then a trust-boundary axiom): the request
`ClusterMemberAttrSetRequest{Member_ID: s.MemberID(), MemberAttributes: {Name, ClientUrls}}` of the
server's attributes (`srvAttrsRO`), then the retry loop: a non-blocking receive on `s.stopping` (closed: a
log line, return), `context.WithTimeout(s.ctx, timeout)`, `s.raftRequest` with the monitors' permission
(`srvMonitorPermitM`, `monitorReq`), `cancel()`, and on success `close(s.readych)` and a log line, on an
error a log line and another round. The log lines format the attributes field by field (the fork's
bc2b5f4d0), over the proved `fmt.Sprintf` of strings and `strings.Join`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__publishV3
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__MemberID
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Logger
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__raftRequest
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__ID
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Duration
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Logger__Info
public import Spec.go_uber_org.zap.Logger__Warn
public import Perennial.Spec.fmt.Sprintf
public import Perennial.Spec.strings.Join
public import Proof.fmt.OutLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.StopChan
public import Proof.context.LibKeys
public import Proof.context.LibKeysChain
public import Proof.context.ReqKeys
public import Proof.go_etcd_io.etcd.server.v3.auth.InvAuth

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]

/-- `&pb.InternalRaftRequest{ClusterMemberAttrSet: r}` for `r` holding `m`. -/
def irrMemberAttrSet (m : apply.MemberAttrModel) : apply.IRRModel :=
  { apply.irrEmpty with clusterMemberAttrSet := some m }

/-- `publishV3`'s request is a monitor's (`monitorReq`): it names the server's own id. -/
theorem monitorReq_irrMemberAttrSet (lid : w64) (name : GoString) (urls : List GoString) :
    monitorReq lid (irrMemberAttrSet ⟨lid, name, urls⟩) := by
  unfold monitorReq irrMemberAttrSet
  refine ⟨⟨?_, ?_, ?_, Or.inl ?_⟩, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩ <;> intro _ h <;> simp_all [apply.irrEmpty, apply.IRRModel.txn]
  · simp [apply.needAdminPermission, apply.irrEmpty]
  · simp [apply.noSideEffect, apply.irrEmpty]
  · simp [apply.dispatchKind, apply.irrEmpty]
  · intro a h; simp only [Option.some.injEq] at h; rw [← h]
  · intro v h; simp [apply.irrEmpty] at h

end defs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem EtcdServer.publishV3.wp_proof
    (hMID : EtcdServer.MemberID.spec (GF := GF) (hG := hG))
    (hLg : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (hRR : EtcdServer.raftRequest.spec (GF := GF) (hG := hG))
    (hIDS : types.ID.String.spec (GF := GF) (hG := hG))
    (hCID : membership.RaftCluster.ID.spec (GF := GF) (hG := hG))
    (hZS : zap.String.spec (GF := GF) (hG := hG))
    (hZD : zap.Duration.spec (GF := GF) (hG := hG))
    (hZE : zap.Error.spec (GF := GF) (hG := hG))
    (hInfo : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (hWarn : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (wp_Sprintf : _root_.Perennial.fmt.Sprintf.spec (GF := GF) (hG := hG))
    (wp_Join : _root_.Perennial.strings.Join.spec (GF := GF) (hG := hG)) :
    EtcdServer.publishV3.spec (GF := GF) (hG := hG) := by
  intro on s d E ρ γr
  wp_start as ⟨%Hon, #Hperm, Hrc, #HrP, G1, #Hrd, #HNR⟩
  subst Hon
  iunfold srvMonitorPermitM at Hperm
  icases Hperm with ⟨#Hreq, ⟨%l, #Hlgf, #Hlgok⟩, ⟨%lid, #Hmid, #Hprop⟩⟩
  iunfold srvReadyCloser at Hrc
  icases Hrc with ⟨Hch, #Hattr, Hlt, HRD⟩
  iunfold srvAttrsRO at Hattr
  icases Hattr with ⟨%name, %sl, %urls, #Hname, #Hcu, #Hsl⟩
  iunfold isServerReadM at Hrd
  icases Hrd with ⟨%vd, #Hvd⟩
  iunfold srvReadFieldsAtM at Hvd
  icases Hvd with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, ⟨%log₀, #Hlb, -⟩, -, -, -, -, -, -, -,
    #Hstpf, #Hstpc, -, #Hlck⟩
  trace_state
  sorry

end proof

end EtcdGrove
end Perennial
