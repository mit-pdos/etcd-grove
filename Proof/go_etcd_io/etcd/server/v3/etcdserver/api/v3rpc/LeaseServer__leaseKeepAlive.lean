/-
Proof of the spec of the same name (etcd-io/etcd#21960). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer__leaseKeepAlive
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.isClientCtxErr
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.togRPCError
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.header__fill
public import Spec.errors.Is
public import Spec.go_uber_org.zap.Logger__Debug
public import Spec.go_uber_org.zap.Logger__Warn
public import Spec.go_uber_org.zap.Error
public import Spec.github_com.prometheus.client_golang.prometheus.CounterVec__WithLabelValues

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api
  go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

set_option hygiene false in
/-- A failed receive or send: the context's error and `isClientCtxErr` choose the log (`Debug`,
or `Warn` and the failure counter labelled `lbl`), then `k` (the return). -/
local macro "log_fail" lbl:term:max k:tactic : tactic => `(tactic| (
  (try wp_auto)
  wp_bind (App (Val #(methods si.ty go!"Context" si.v)) (Val #()))
  iapply HCtx
  · itrivial
  iintro !> -
  wp_auto
  wp_apply +noauto HErrU $$ [] as %cerr -
  wp_auto
  wp_apply hICE as %bc -
  wp_if_destruct
  · wp_apply hZE as %f -
    wp_apply wp_slice_literal (l := [f])
    isplitr
    · ipureintro; rfl
    iintro %fsl -
    wp_auto
    wp_apply hZW S.lg _ _ $$ []
    · iframe #; ipureintro; exact Hnn.2
    wp_apply wp_slice_literal (V := GoString) [$lbl, go!"lease-keepalive"]
    isplitr
    · ipureintro; rfl
    iintro %lsl -
    wp_auto
    wp_apply hCV cvF _ as %cnt ⟨%cnti, %Hcnt, #Hcs⟩
    subst Hcnt
    iunfold prometheus.counterSpec at Hcs
    wp_apply Hcs
    (try wp_auto)
    $k
  · wp_apply hZE as %f -
    wp_apply wp_slice_literal (l := [f])
    isplitr
    · ipureintro; rfl
    iintro %fsl -
    wp_auto
    wp_apply hZD S.lg _ _ $$ []
    · iframe #; ipureintro; exact Hnn.2
    (try wp_auto)
    $k))


set_option hygiene false in
/-- The loop's return, from any tokens. -/
local macro "lk_return" : tactic => `(tactic| (
  wp_for_post
  iapply HΦ
  iunfold v3rpc.lkDone
  iexists _, _
  iframe))

set_option hygiene false in
/-- The response's send (its TTL `t`, `Httl : t = 0 ∨ S.Ren m t`), then the next iteration or,
on a failed send, the log and the return. -/
local macro "send_part" t:term:max : tactic => `(tactic| (
  (try wp_auto)
  ihave #HSend1 := HSend $$ %Lr %«$r0_ptr» %(⟨m, $t, S.cid, S.mid⟩ : v3rpc.LKRespM)
  wp_apply HSend1 $$ [Hst ID TTL Header Hfilled Revision] as %serr Hsr
  · isplitl [Hst]
    · iexact Hst
    isplitl [ID TTL Header Hfilled Revision]
    · iunfold v3rpc.lkResp
      isplitr
      · ipureintro; exact Hr0n
      iexists _, _
      iframe
    · iapply Hspec'
      iunfold v3rpc.lkDn
      iexists m
      rw [Hlen]
      iframe #
      ipureintro; exact ⟨rfl, rfl, rfl, Httl⟩
  icases Hsr with (⟨%Hse, Hst⟩ | ⟨%Hne, #Hse, %L', %HL', Hst⟩)
  · subst Hse
    wp_auto
    wp_for_post
    iframe HΦ ls stream
    iexists Lq ++ [m], Lr ++ [(⟨m, $t, S.cid, S.mid⟩ : v3rpc.LKRespM)]
    iframe Hrt Hst HR
    ipureintro; simp [Hlen]
  · rcases serr with ei | _
    rotate_left
    · exact absurd rfl Hne
    log_fail go!"send" lk_return))

/-- `errors.Is(err, target)` of an error the apply package describes (`applyErrIs`) and a
pointer-leaf target: some boolean (`serverWatchStream__recvLoop.lean`'s `v3rpc.wp_Is_applyErr`,
restated: a proof file imports only specs). -/
theorem v3rpc.wp_Is_applyErrLK (hIs : errors.Is.spec (GF := GF) (hG := hG)) (err : GoInterface)
    (e : GoInterfaceOk) (he : errLeaf e) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.errors ∗ applyErrIs err }}
      (App (App (Val (@! _root_.Perennial.errors.Is)) (Val #err)) (Val #(GoInterface.ok e)))
    {{ (b : Bool), RET #b; True }} := by
  iintro %Φ ⟨#Hpkg, #Herr⟩ HΦ
  ihave #HIsT := applyErrIs_tree err $$ Herr
  ihave ⟨%S, %M, #Ht, %HS⟩ := HIsT $$ %(GoInterface.ok e)
  iapply hIs S M err (GoInterface.ok e) (fun tii h => by cases h; exact he.1)
    (HS.2 (fun tii h => by cases h; exact he.1))
  · iframe #; ipureintro; exact HS.1
  iintro !> %b -
  iapply HΦ
  itrivial

set_option maxHeartbeats 0 in
theorem v3rpc.LeaseServer.leaseKeepAlive.wp_proof
    (hICE : v3rpc.isClientCtxErr.spec (GF := GF) (hG := hG))
    (hTog : v3rpc.togRPCError.spec (GF := GF) (hG := hG))
    (hFill : v3rpc.header.fill.spec (GF := GF) (hG := hG))
    (hIs : errors.Is.spec (GF := GF) (hG := hG))
    (hZD : zap.Logger.Debug.spec (GF := GF) (hG := hG))
    (hZW : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (hZE : zap.Error.spec (GF := GF) (hG := hG))
    (hCV : prometheus.CounterVec.WithLabelValues.spec (GF := GF) (hG := hG)) :
    v3rpc.LeaseServer.leaseKeepAlive.spec (GF := GF) (hG := hG) := by
  intro p S st γs Up Dn ci cd Lq0 Lr0
  wp_start as ⟨#Hls, #Hstream, #Hspec, Hrt0, Hst0, %Hlen0, HR⟩
  ihave #Hspec' := Hspec
  iunfold v3rpc.lkStreamSpec at Hspec'
  ihave #Hls' := Hls
  iunfold v3rpc.isLeaseServer at Hls'
  icases Hls' with ⟨%Hnn, #Flg, #Fle, #Hhdr, #Hle, #Hvars⟩
  iunfold v3rpc.leaseVars at Hvars
  icases Hvars with ⟨#Heof, ⟨%cvF, #HcvF⟩, #HeLNF⟩
  iunfold v3rpc.eofVar at Heof
  icases Heof with ⟨%eofE, #HeofG, %HeofL, #HeofM⟩
  iunfold errVarLeaf at HeLNF
  icases HeLNF with ⟨%eLNF, #HeLNFg, %HeLNFL, -⟩
  iunfold v3rpc.lessorOk at Hle
  icases Hle with ⟨%li, %Hli, #HRenew⟩
  ihave #Hstream' := Hstream
  iunfold v3rpc.srvStreamIs at Hstream'
  icases Hstream' with ⟨%si, %Hsi, #HRecv, #HSend, #HCtx, #Hctxis, #Hrunctx⟩
  ihave #Hctx2 := Hctxis
  iNamed Hctx2
  ihave #HErrU := HErr $$ %Broadcast.Unknown
  ihave #Perr : isPkgInit (PROP := IProp GF) pkg_id.errors $$ []
  · iPkgInit
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Pprom : isPkgInit (PROP := IProp GF) pkg_id.github_com.prometheus.client_golang.prometheus $$ []
  · iPkgInit
  wp_auto
  ihave Hinv : iprop(∃ (Lq : List w64) (Lr : List v3rpc.LKRespM),
      "Hrt" ∷ v3rpc.srvRecvTok (Req := v3rpc.pbLeaseKeepAliveRequest) γs Lq ∗
      "Hst" ∷ v3rpc.srvSendTok (Rep := v3rpc.pbLeaseKeepAliveResponse) γs Lr ∗
      "HR" ∷ S.A.revR ∗ "%Hlen" ∷ ⌜Lr.length = Lq.length⌝) $$ [Hrt0 Hst0 HR]
  · iexists Lq0, Lr0; iframe; ipureintro; exact Hlen0
  wp_for Hinv
  rw [Hsi]
  wp_apply HRecv $$ Hrt as %req %err Hrr
  icases Hrr with (⟨%Herr, %m, Hreq, HUp, Hrt⟩ | ⟨#Heofi, %Hne, Hrt, #Hcl⟩ | ⟨%Hne, #Hse, Hrt⟩)
  · -- a request
    subst Herr
    wp_apply hIs (· = GoInterface.nil) (fun _ => False) GoInterface.nil (GoInterface.ok eofE)
      (fun tii h => by cases h; exact HeofL.1.1) (by intro ii tii h; cases h) $$ [] as %b -
    · iframe #
      isplitl
      · iintro !> %ii %h; cases h
      · ipureintro; rfl
    wp_if_destruct
    rotate_left
    · wp_for_post
      iapply HΦ
      iunfold v3rpc.lkDone
      iexists Lq ++ [m], Lr
      iframe
    iunfold v3rpc.lkReqRecv at Hreq
    ihave ⟨Hrt, #Hat⟩ := v3rpc.srvRecvTok_upAtLK γs Lq m $$ Hrt
    wp_auto
    ihave %Hv1n := typedPointsto_not_null _ _ _ $$ «$v1»
    ihave %Hr0n := typedPointsto_not_null _ _ _ $$ «$r0»
    iStructNamed «$v1»
    iStructNamed «$r0»
    wp_apply hFill $$ [ClusterId MemberId RaftTerm LeaderId Revision HR] as ⟨Hfilled, %rv', Hrev'⟩
    · iframe #
      isplitl [ClusterId MemberId RaftTerm LeaderId]
      · iunfold v3rpc.hdrW
        isplitr
        · ipureintro; exact Hv1n
        iexists _, _, _, _
        iframe
      · iunfold v3rpc.hdrRevIn
        iright
        iframe
    iunfold v3rpc.hdrRevOut at Hrev'
    icases Hrev' with (⟨%Hc, -⟩ | ⟨-, Revision, HR⟩)
    · exact absurd rfl Hc.1
    (try wp_auto)
    wp_bind (App (Val #(methods si.ty go!"Context" si.v)) (Val #()))
    iapply HCtx
    · itrivial
    iintro !> -
    rw [Hli]
    wp_auto
    wp_apply HRenew as %ttl %rerr Hren
    icases Hren with (%Hren | #Hse)
    · obtain ⟨Hre, Hren⟩ := Hren
      subst Hre
      wp_apply hIs (· = GoInterface.nil) (fun _ => False) GoInterface.nil (GoInterface.ok eLNF)
        (fun tii h => by cases h; exact HeLNFL.1) (by intro ii tii h; cases h) $$ [] as %b -
      · iframe #
        isplitl
        · iintro !> %ii %h; cases h
        · ipureintro; rfl
      wp_if_destruct
      · have Httl : ttl = W64 0 ∨ S.Ren m ttl := Or.inr Hren
        send_part ttl
      · have Httl : (W64 0) = W64 0 ∨ S.Ren m (W64 0) := Or.inl rfl
        send_part (W64 0)
    · ihave #Hse' := Hse
      iunfold v3rpc.srvErrIs at Hse'
      icases Hse' with ⟨%Hen, #HaE, -⟩
      wp_apply v3rpc.wp_Is_applyErrLK hIs rerr eLNF HeLNFL $$ [] as %b -
      · iframe #
      wp_if_destruct
      · rcases rerr with ei | _
        rotate_left
        · exact absurd rfl Hen
        (try wp_auto)
        wp_apply hTog $$ [] as %e %He
        · iframe #
        lk_return
      · have Httl : (W64 0) = W64 0 ∨ S.Ren m (W64 0) := Or.inl rfl
        send_part (W64 0)
  · -- io.EOF
    iunfold v3rpc.eofIs at Heofi
    icombine Heofi HeofG gives %Heq
    subst Heq
    wp_apply hIs (· = GoInterface.ok eofE) (fun _ => False) (GoInterface.ok eofE)
      (GoInterface.ok eofE) (fun tii h => by cases h; exact HeofL.1.1)
      (_root_.Perennial.errors.treeTyped_pointer eofE _ HeofL.1.1) $$ [] as %b -
    · iframe #
      isplitl
      · iapply _root_.Perennial.errors.errorIsTree_leaf eofE _ _ HeofL.1.2.1 HeofL.1.2.2
      · ipureintro; rfl
    wp_if_destruct
    · log_fail go!"receive" lk_return
    · lk_return
  · -- another error
    iunfold v3rpc.streamErr at Hse
    icases Hse with ⟨%Hty, #HseT⟩
    ihave ⟨%S', %M, #Ht, %HS⟩ := HseT $$ %(GoInterface.ok eofE)
    wp_apply hIs S' M err (GoInterface.ok eofE) (fun tii h => by cases h; exact HeofL.1.1)
      (HS.2 (fun tii h => by cases h; exact HeofL.1.1)) $$ [] as %b -
    · iframe #; ipureintro; exact HS.1
    wp_if_destruct
    · rcases err with ei | _
      rotate_left
      · exact absurd rfl Hne
      log_fail go!"receive" lk_return
    · lk_return

end proof

end EtcdGrove
end Perennial
