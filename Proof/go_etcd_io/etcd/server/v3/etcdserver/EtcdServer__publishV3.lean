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

/-- `uint64` is not an interface type (`publishV3` calls `String()` on the server's `types.ID`). -/
instance notInterface_uint64_publish [GooseExts] : go.NotInterface go.uint64 :=
  ⟨by unfold go.uint64; trivial⟩

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

/-- `ctxValueFrom` is transitive. -/
theorem ctxValueFrom_trans' {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
    [_root_.Perennial.context.Assumptions]
    (a b c : GoInterfaceOk) :
    _root_.Perennial.context.ctxValueFrom (GF := GF) a b ∗ _root_.Perennial.context.ctxValueFrom b c ⊢
      _root_.Perennial.context.ctxValueFrom a c := by
  iintro ⟨#H1, #H2⟩
  unfold _root_.Perennial.context.ctxValueFrom
  iintro !> %k %R %hk #Hv
  iapply H2
  · ipureintro; exact hk
  iapply H1
  · ipureintro; exact hk
  iexact Hv

/-- A child of `Background()` (`ctxValueFrom`) carries no span (`trace.spanCtxOk`). -/
theorem spanCtxOk_bgFrom' {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
    [_root_.Perennial.context.Assumptions]
    (ctx : GoInterfaceOk) :
    isPkgInit (PROP := IProp GF) pkg_id.context ∗
      _root_.Perennial.context.ctxValueFrom (GF := GF) _root_.Perennial.context.backgroundCtxVal ctx ⊢
      trace.spanCtxOk ctx := by
  iintro ⟨#Hpkg, #Hf⟩
  iapply trace.spanCtxOk_of_spanCtxOkC
  iframe Hpkg
  iapply trace.spanCtxOkC_from _root_.Perennial.context.backgroundCtxVal ctx
  iframe Hf
  unfold trace.spanCtxOkC
  iexists (· = interface.nil)
  isplitl []
  · iintro !> %v %hv; ileft; ipureintro; exact hv
  iapply _root_.Perennial.context.ctxValue_background

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
  wp_start as ⟨%Hon, Hperm, Hrc, #HrP, G1, #Hrd, #HNR⟩
  subst Hon
  iunfold srvMonitorPermitM at Hperm
  icases Hperm with ⟨#Hreq, #HlgOk, ⟨%lid, #Hmid, #Hprop⟩⟩
  iunfold srvLoggerOk at HlgOk
  icases HlgOk with ⟨%l, #Hlgf, #Hlgok⟩
  iunfold srvReadyCloser at Hrc
  icases Hrc with ⟨Hch, #Hattr, Hlt, HRD⟩
  iunfold srvAttrsRO at Hattr
  icases Hattr with ⟨%name, %sl, %urls, #Hname, #Hcu, #Hsl⟩
  iunfold isServerReadM at Hrd
  icases Hrd with ⟨%vd, #Hvd⟩
  iunfold srvReadFieldsAtM at Hvd
  icases Hvd with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, ⟨%log₀, #Hlb, -⟩, -, -, -, -, -, -, -,
    #Hstpf, #Hstpc, -, #Hlck⟩
  wp_auto
  wp_apply +noauto hMID s lid
  · iframe #
  wp_auto_lc 1
  -- the request `&ClusterMemberAttrSetRequest{Member_ID: lid, MemberAttributes: &Attributes{name, sl}}`,
  -- read-only
  ihave ⟨Hv1, %Hv1nn⟩ := typedPointsto_not_null_dup _ _ _ $$ «$v1»
  ihave ⟨Hr0, %Hr0nn⟩ := typedPointsto_not_null_dup _ _ _ $$ «$r0»
  iStructNamedSuffix Hv1 "A"
  iStructNamedSuffix Hr0 "R"
  ipersist NameA
  ipersist ClientUrlsA
  ipersist Member_IDR
  ipersist MemberAttributesR
  ihave #Hmas : apply.memberAttrSetIs «$r0_ptr» ⟨lid, name, urls⟩ $$ []
  · iunfold apply.memberAttrSetIs
    isplitr
    · ipureintro; exact Hr0nn
    iexists «$v1_ptr», sl
    iframe #
    ipureintro; exact Hv1nn
  -- `lg := s.Logger()`, with a slot of `lgMu`'s pool
  imod raftPool_borrowL (srvLgReader s) ⊤ (fun _ _ => CoPset.mem_full) $$ [Hlc1 G1] with ⟨Hlr, Hloan⟩
  · iframe Hlc1 G1; iexact HrP
  wp_apply hLg s l $$ [Hlr] as ⟨-, Hlr⟩
  · iframe #; iframe Hlr
  iapply fupd_wp
  imod raftLoanL_giveBack (srvLgReader s) ⊤ (fun _ _ => CoPset.mem_full) $$ [Hloan Hlr] with G1
  · iframe
  imodintro
  (try wp_auto)
  -- the stop channel, `s.ctx`, the cluster
  iunfold stopChan at Hstpc
  icases Hstpc with ⟨%γs, #Hstop⟩
  ihave #Hstop' := Hstop
  iunfold ownStopChan at Hstop'
  icases Hstop' with ⟨%γch, #Hint, -⟩
  iunfold srvLeadCheckOk at Hlck
  icases Hlck with ⟨-, -, ⟨%ctx, %cd, #Hctxf, #Hctxi, #Hcbg⟩⟩
  ihave #Hreq' := (isServerReqM_split E.authOn s E ρ).1 $$ Hreq
  icases Hreq' with ⟨⟨%vq, #Hvq⟩, -⟩
  iunfold srvReqFieldsAtM at Hvq
  icases Hvq with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hcl, -, #Hpeers, -⟩
  iunfold srvPeersOk at Hpeers
  icases Hpeers with ⟨#Hcid, -⟩
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  ihave #Hstrs : isPkgInit (PROP := IProp GF) pkg_id.strings $$ []
  · iPkgInit
  ihave #Hctxp : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Htyp : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.types $$ []
  · iPkgInit
  ihave #Hmemp : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership $$ []
  · iPkgInit
  have hSp := fmt.Sprintf.argsWf wp_Sprintf
  wp_for
  (try wp_auto)
  -- `select { case <-s.stopping: ...; return; default: }`
  wp_apply_core chan.wp_select_nonblocking
  isplit
  · iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.nonblockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, vd.stopping, γs
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply ownStopChan_is_chan $$ Hstop
      unfold nonblockingRecvAu
      isplit
      · iapply stop_chan_nonblocking_receive_inner vd.stopping γs γch _ _ $$ Hint
        iintro -
        (try wp_auto)
        wp_apply hMID s lid
        · iframe #
        (try wp_auto)
        wp_apply hIDS lid as %ids -
        (try wp_auto)
        wp_apply hZS as %f1 -
        (try wp_auto)
        wp_apply wp_Join sl urls DFrac.discard _ $$ [] as -
        · iframe #
        (try wp_auto)
        wp_apply (wp_slice_literal (V := GoInterface) (l := [_, _]))
        isplitr
        · ipureintro; rfl
        iintro %asl ⟨Hasl, -⟩
        (try wp_auto)
        wp_apply (hSp _ _ _ _ (_root_.Perennial.fmt.ArgsWf.cons_string _ _
          (_root_.Perennial.fmt.ArgsWf.cons_string _ _ _root_.Perennial.fmt.ArgsWf.nil))) $$ [$Hasl] as %astr ⟨-, -⟩
        (try wp_auto)
        wp_apply hZS as %f2 -
        (try wp_auto)
        wp_apply hZD as %f3 -
        (try wp_auto)
        wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field)
        isplitr
        · ipureintro; rfl
        iintro %fsl ⟨-, -⟩
        (try wp_auto)
        wp_apply hWarn l _ _ $$ []
        · iframe #
        (try wp_auto)
        wp_for_post
        iapply HΦ
        iframe G1
      · itrivial
    iapply BigAndL.bigAndL_nil.2
    itrivial
  -- `default`: a round. `ctx, cancel := context.WithTimeout(s.ctx, timeout)`, a child of `Background()`
  (try wp_auto)
  wp_apply context.wp_WithTimeout ctx cd d $$ [] as %cctx %γc %cancel %dl ⟨#Hcancel, #Hcctx, #Hcf⟩
  · iframe #
  ihave #Hcbg' := ctxValueFrom_trans' _ _ _ $$ [Hcbg Hcf]
  · iframe Hcbg Hcf
  ihave #Hlib := context.libCtxOk_bgFrom cctx $$ [Hctxp Hcbg']
  · iframe Hctxp Hcbg'
  ihave #Hspan := spanCtxOk_bgFrom' cctx $$ [Hctxp Hcbg']
  · iframe Hctxp Hcbg'
  ihave #Hst := startTimeOk_of_bgFrom cctx $$ [Hctxp Hcbg']
  · iframe Hctxp Hcbg'
  ihave ⟨%tok, #Htk⟩ := auth.ctxToken_of_libCtxOk cctx $$ Hlib
  ihave #HtokR : □ (⌜E.authOn = true⌝ → auth.ctxToken (GoInterface.ok cctx) tok) $$ []
  · iintro !> -; iexact Htk
  (try wp_auto)
  -- `&pb.InternalRaftRequest{ClusterMemberAttrSet: req}`, every field but `Header` read-only
  ihave ⟨Hirr, %Hirrn⟩ := typedPointsto_not_null_dup _ _ _ $$ «$a1»
  iStructNamed Hirr
  ipersist ID
  ipersist Range
  ipersist Put
  ipersist DeleteRange
  ipersist Txn
  ipersist Compaction
  ipersist LeaseGrant
  ipersist LeaseRevoke
  ipersist Alarm
  ipersist LeaseCheckpoint
  ipersist AuthEnable
  ipersist AuthDisable
  ipersist AuthStatus
  ipersist Authenticate
  ipersist AuthUserAdd
  ipersist AuthUserDelete
  ipersist AuthUserGet
  ipersist AuthUserChangePassword
  ipersist AuthUserGrantRole
  ipersist AuthUserRevokeRole
  ipersist AuthUserList
  ipersist AuthRoleList
  ipersist AuthRoleAdd
  ipersist AuthRoleDelete
  ipersist AuthRoleGet
  ipersist AuthRoleGrantPermission
  ipersist AuthRoleRevokePermission
  ipersist ClusterVersionSet
  ipersist ClusterMemberAttrSet
  ipersist DowngradeInfoSet
  ipersist DowngradeVersionTest
  ihave #HirrNo : irrNoHdrIs «$a1_ptr» (irrMemberAttrSet ⟨lid, name, urls⟩) $$ []
  · iunfold irrNoHdrIs
    simp only [irrMemberAttrSet, apply.irrEmpty, apply.optReqIs, apply.presentIs, apply.irrField]
    isplitr
    · ipureintro; exact Hirrn
    isplitr
    · have h0 : (W64 0 : w64) = 0 := by decide
      rw [h0]; iexact ID
    repeat (isplitr; · iexists _; iframe #; try (ipureintro; simp))
    iexists _; iframe #; try (ipureintro; simp)
  imod HNR with Hid
  -- `s.raftRequest(ctx, …)`, with the monitors' permission for the request
  wp_apply hRR s E ρ cctx { cd with Deadline := some dl, PDone := iprop(True), Done_gn := γc } tok «$a1_ptr» (irrMemberAttrSet ⟨lid, name, urls⟩) (fun _ _ => iprop(True))
      log₀ rfl (apply.irrDepthOk_of_txnW_none rfl) $$ [Hlt HRD Hid Header]
    as %resp %err ⟨Hlt, HRD, -⟩
  · iframe; iframe #
    iapply Hprop
    ipureintro; exact monitorReq_irrMemberAttrSet lid name urls
  (try wp_auto)
  wp_apply Hcancel
  (try wp_auto)
  by_cases he : err = GoInterface.nil
  · -- published: `close(s.readych)`, a log line, return
    subst he
    (try wp_auto)
    iunfold srvReadyCh at Hch
    icases Hch with ⟨%rdc, %γy, #Hrdf, Hown⟩
    (try wp_auto)
    wp_apply (wp_broadcast_chan_close rdc γy iprop(True)) $$ [$Hown] as -
    · iintro !>; itrivial
    (try wp_auto)
    wp_apply hMID s lid
    · iframe #
    (try wp_auto)
    wp_apply hIDS lid as %ids -
    (try wp_auto)
    wp_apply hZS as %f1 -
    (try wp_auto)
    wp_apply wp_Join sl urls DFrac.discard _ $$ [] as -
    · iframe #
    (try wp_auto)
    wp_apply (wp_slice_literal (V := GoInterface) (l := [_, _]))
    isplitr
    · ipureintro; rfl
    iintro %asl ⟨Hasl, -⟩
    (try wp_auto)
    wp_apply (hSp _ _ _ _ (_root_.Perennial.fmt.ArgsWf.cons_string _ _
      (_root_.Perennial.fmt.ArgsWf.cons_string _ _ _root_.Perennial.fmt.ArgsWf.nil))) $$ [$Hasl] as %astr ⟨-, -⟩
    (try wp_auto)
    wp_apply hZS as %f2 -
    (try wp_auto)
    wp_apply hCID vq.cluster vq.cid $$ []
    · iframe #
    (try wp_auto)
    wp_apply hIDS vq.cid as %cids -
    (try wp_auto)
    wp_apply hZS as %f3 -
    (try wp_auto)
    wp_apply hZD as %f4 -
    (try wp_auto)
    wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field)
    isplitr
    · ipureintro; rfl
    iintro %fsl ⟨-, -⟩
    (try wp_auto)
    wp_apply hInfo l _ _ $$ []
    · iframe #
    (try wp_auto)
    wp_for_post
    iapply HΦ
    iframe G1
  · -- failed: a log line, another round
    obtain ⟨ei, rfl⟩ : ∃ ei, err = GoInterface.ok ei := by
      cases err with
      | nil => exact absurd rfl he
      | ok ei => exact ⟨ei, rfl⟩
    (try wp_auto)
    (try wp_auto)
    wp_apply hMID s lid
    · iframe #
    (try wp_auto)
    wp_apply hIDS lid as %ids -
    (try wp_auto)
    wp_apply hZS as %f1 -
    (try wp_auto)
    wp_apply wp_Join sl urls DFrac.discard _ $$ [] as -
    · iframe #
    (try wp_auto)
    wp_apply (wp_slice_literal (V := GoInterface) (l := [_, _]))
    isplitr
    · ipureintro; rfl
    iintro %asl ⟨Hasl, -⟩
    (try wp_auto)
    wp_apply (hSp _ _ _ _ (_root_.Perennial.fmt.ArgsWf.cons_string _ _
      (_root_.Perennial.fmt.ArgsWf.cons_string _ _ _root_.Perennial.fmt.ArgsWf.nil))) $$ [$Hasl] as %astr ⟨-, -⟩
    (try wp_auto)
    wp_apply hZS as %f2 -
    (try wp_auto)
    wp_apply hZD as %f3 -
    (try wp_auto)
    wp_apply hZE as %f4 -
    (try wp_auto)
    wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field)
    isplitr
    · ipureintro; rfl
    iintro %fsl ⟨-, -⟩
    (try wp_auto)
    wp_apply hWarn l _ _ $$ []
    · iframe #
    (try wp_auto)
    wp_for_post
    iframe

end proof

end EtcdGrove
end Perennial
