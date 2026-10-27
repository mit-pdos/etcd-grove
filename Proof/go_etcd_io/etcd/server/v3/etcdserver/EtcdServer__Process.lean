/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__Process.lean`. Lean-first (no Rocq
counterpart); D21 stage M2 (2026-10-19).

The logger read under `lgMu` (the borrowed reader slot); `IsIDRemoved` is `false` (static
membership); the message's `To` is the member's (the network's promise), so both `403` branches
are dead; a `MsgApp` is counted (`RecvAppendReq` over `proto.Size`, trust-boundary axioms, D21h
(A)); the delivered message is what the node API's `node.Step` takes (`stepIn_of_recv`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Process
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Logger
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__MemberID
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__IsIDRemoved
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.ServerStats__RecvAppendReq
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String
public import Spec.google_golang_org.protobuf.proto.SizeMessage
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetFrom
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetTo
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetType

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

theorem EtcdServer.Process.wp_proof
    (wp_Logger : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (wp_IsIDRemoved : membership.RaftCluster.IsIDRemoved.spec (GF := GF) (hG := hG))
    (wp_MemberID : EtcdServer.MemberID.spec (GF := GF) (hG := hG))
    (wp_GetFrom : raftpb.Message.GetFrom.spec (GF := GF) (hG := hG))
    (wp_GetTo : raftpb.Message.GetTo.spec (GF := GF) (hG := hG))
    (wp_GetType : raftpb.Message.GetType.spec (GF := GF) (hG := hG))
    (wp_String : types.ID.String.spec (GF := GF) (hG := hG))
    (wp_SizeMessage : proto.SizeMessage.spec (GF := GF) (hG := hG))
    (wp_RecvAppendReq : v2stats.ServerStats.RecvAppendReq.spec (GF := GF) (hG := hG)) :
    EtcdServer.Process.spec (GF := GF) (hG := hG) := by
  intro γn γd s id ctx cd ml
  wp_start as ⟨#Hok, #Hctx, Hlr, Hrecv⟩
  iunfold srvProcOk at Hok
  icases Hok with ⟨%l, %c, %st, %γ, #Hlg, %Hlgnn, #Hid, %Hγid, #Hcl, #Hrc, #Hstat, %Hstnn, #Hn,
    #Hsi, #Hcok, %HN⟩
  ihave #Hmpkg : isPkgInit (PROP := IProp GF)
      pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership $$ []
  · iPkgInit
  ihave #Hpbpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  ihave #Htypkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.types $$ []
  · iPkgInit
  ihave #Hprpkg : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto $$ []
  · iPkgInit
  ihave #Hv2pkg : isPkgInit (PROP := IProp GF)
      pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats $$ []
  · iPkgInit
  iunfold netRecv at Hrecv
  icases Hrecv with ⟨%sm, %sm', Hm, %Hw, #HP, HO, #HS⟩
  obtain ⟨⟨Hmsg, Hents, Hsnap, Hctx'⟩, Hto, Hrs'⟩ := Hw
  wp_auto
  wp_apply wp_Logger s l $$ [Hlr] as ⟨-, Hlr⟩
  · iframe #; iframe Hlr; ipureintro; exact Hlgnn
  (try wp_auto)
  -- `s.cluster.IsIDRemoved(m.GetFrom())`: `false`
  wp_apply wp_GetFrom.1 ml _ _ _ sm' $$ [Hm] as Hm
  · iframe #; iframe Hm
  (try wp_auto)
  wp_apply (membership.RaftCluster.IsIDRemoved.spec_static wp_IsIDRemoved c sm'.msg.From')
  · iframe #
  (try wp_auto)
  -- `s.MemberID() != m.GetTo()`: the message is addressed to `id`
  wp_apply wp_MemberID s id
  · iframe #
  wp_apply wp_GetTo.1 ml _ _ _ sm' $$ [Hm] as Hm
  · iframe #; iframe Hm
  have HTo : sm'.msg.To' = id := by rw [Hmsg]; exact Hto
  rw [HTo]
  (try wp_auto)
  -- a `MsgApp` counted in the stats
  wp_apply wp_GetType.1 ml _ _ _ sm' $$ [Hm] as Hm
  · iframe #; iframe Hm
  (try wp_auto)
  wp_if_destruct
  · wp_apply wp_GetFrom.1 ml _ _ _ sm' $$ [Hm] as Hm
    · iframe #; iframe Hm
    (try wp_auto)
    wp_apply wp_String sm'.msg.From' as %fs -
    (try wp_auto)
    wp_apply wp_SizeMessage ml _ _ _ sm' $$ [Hm] as %sz ⟨Hm, -⟩
    · iframe #; iframe Hm
    (try wp_auto)
    wp_apply wp_RecvAppendReq st fs sz
    · iframe #; ipureintro; exact Hstnn
    (try wp_auto)
    (try wp_auto)
    -- `s.r.Step(ctx, m)`: raft's, of what the network delivered
    ihave Hrecv : netRecv γn γ.id γd ml $$ [Hm HO]
    · iunfold netRecv
      iexists sm, sm'
      iframe Hm HO HP HS
      ipureintro
      exact ⟨⟨Hmsg, Hents, Hsnap, Hctx'⟩, by rw [Hγid]; exact Hto, Hrs'⟩
    imod (stepIn_of_recv γn γ HN ml) $$ [Hcok Hrecv] with Hstep
    · iframe Hcok Hrecv
    iunfold rnStepIfc at Hsi
    icases Hsi with ⟨%ni, %Hni, #HStep, -, -⟩
    have Hni' : ni = ⟨go.GoType.PointerType node.ty, #γ.nl⟩ :=
      (GoInterface.ok.inj Hni).symm
    subst Hni'
    rw [method_unfold (t := go.GoType.PointerType raftNode.ty) (m := go!"Step")]
    wp_pures
    rw [method_unfold (t := go.GoType.PointerType raftNodeConfig.ty) (m := go!"Step")]
    wp_pures
    (try wp_auto)
    wp_apply HStep $$ %ctx %cd %ml [Hstep] as %err #Herr
    · iframe Hctx Hstep
    (try wp_auto)
    iapply HΦ
    iframe Hlr Herr
  · (try wp_auto)
    -- `s.r.Step(ctx, m)`: raft's, of what the network delivered
    ihave Hrecv : netRecv γn γ.id γd ml $$ [Hm HO]
    · iunfold netRecv
      iexists sm, sm'
      iframe Hm HO HP HS
      ipureintro
      exact ⟨⟨Hmsg, Hents, Hsnap, Hctx'⟩, by rw [Hγid]; exact Hto, Hrs'⟩
    imod (stepIn_of_recv γn γ HN ml) $$ [Hcok Hrecv] with Hstep
    · iframe Hcok Hrecv
    iunfold rnStepIfc at Hsi
    icases Hsi with ⟨%ni, %Hni, #HStep, -, -⟩
    have Hni' : ni = ⟨go.GoType.PointerType node.ty, #γ.nl⟩ :=
      (GoInterface.ok.inj Hni).symm
    subst Hni'
    rw [method_unfold (t := go.GoType.PointerType raftNode.ty) (m := go!"Step")]
    wp_pures
    rw [method_unfold (t := go.GoType.PointerType raftNodeConfig.ty) (m := go!"Step")]
    wp_pures
    (try wp_auto)
    wp_apply HStep $$ %ctx %cd %ml [Hstep] as %err #Herr
    · iframe Hctx Hstep
    (try wp_auto)
    iapply HΦ
    iframe Hlr Herr

end proof

end EtcdGrove
end Perennial
