/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__publishV3.lean`
(etcd-io/etcd#22527, branch `pr-verify/etcd-22527`; on `lean` an axiom, names-only). Lean-first
(no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__publishV3
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__raftRequest
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__waitApplyWithinRequestLimit
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__MemberID
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Logger
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__ID
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Duration
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Logger__Info
public import Spec.go_uber_org.zap.Logger__Warn
public import Spec.fmt.SprintfStruct
public import Spec.errors.Is
public import Perennial.Proof.context

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

/-- `uint64` is not an interface type (as `InvStart.lean`'s: `publishV3` calls `String()` on the
server's `types.ID`, whose underlying type is `uint64`). -/
instance notInterface_uint64_publish [FfiSyntax] : go.NotInterface go.uint64 :=
  ⟨by unfold go.uint64; trivial⟩

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- The request `publishV3` proposes: `&pb.InternalRaftRequest{ClusterMemberAttrSet: req}`. -/
def irrMemberAttr (m : apply.MemberAttrModel) : apply.IRRModel :=
  { apply.irrEmpty with clusterMemberAttrSet := some m }

/-- `errors.Is(err, v)` for an error the request path returns and an error variable's
`errors.New` error (as the read package's `read_wp_Is_var`). -/
theorem publish_wp_Is_var (hIs : errors.Is.spec (GF := GF) (hG := hG)) (err : GoInterface)
    (e : GoInterfaceOk) (hl : errLeaf e) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.errors ∗ applyErrIs err }}
      (App (App (Val (@! _root_.Perennial.errors.Is)) (Val #err)) (Val #(GoInterface.ok e)))
    {{ (b : Bool), RET #b; True }} := by
  iintro %Φ ⟨#Hp, #Herr⟩ HΦ
  ihave #HT := applyErrIs_tree err $$ Herr
  ihave ⟨%S, %M, #Htree, %HS⟩ := HT $$ %(GoInterface.ok e)
  have hpt : ptrTarget (GoInterface.ok e) := fun tii h => by cases h; exact hl.1
  iapply hIs S M err (GoInterface.ok e) hpt (HS.2 hpt) $$ [] HΦ
  iframe #; ipureintro; exact HS.1

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem EtcdServer.publishV3.wp_proof
    (hRR : EtcdServer.raftRequest.spec (GF := GF) (hG := hG))
    (hWA : EtcdServer.waitApplyWithinRequestLimit.spec (GF := GF) (hG := hG))
    (hMID : EtcdServer.MemberID.spec (GF := GF) (hG := hG))
    (hLg : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (hIDS : types.ID.String.spec (GF := GF) (hG := hG))
    (hRCID : membership.RaftCluster.ID.spec (GF := GF) (hG := hG))
    (hZS : zap.String.spec (GF := GF) (hG := hG))
    (hZD : zap.Duration.spec (GF := GF) (hG := hG))
    (hZE : zap.Error.spec (GF := GF) (hG := hG))
    (hI : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (hW : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (hSF : fmt.SprintfStruct.spec (GF := GF) (hG := hG))
    (hIs : errors.Is.spec (GF := GF) (hG := hG)) :
    EtcdServer.publishV3.spec (GF := GF) (hG := hG) := by
  intro s E ρ γr rc γrc d
  wp_start as ⟨#Hreq, #Hrd, Hres⟩
  iunfold srvPublishRes at Hres
  icases Hres with ⟨%av, %urls, %ci, %cd, %F, #Hav, #Hurls, #Hctxf, #Hctx, #Hrcf, Hrc, Hlt, HRD,
    Hlgr, #HNR, #HF⟩
  ihave #Hreq' := Hreq
  iunfold isServerReq at Hreq'
  icases Hreq' with ⟨%v, #Hv⟩
  iunfold srvReqFieldsAt at Hv
  icases Hv with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hmid, -, #Hcl, -, #Hpeers, -⟩
  iunfold srvPeersOk at Hpeers
  icases Hpeers with ⟨#Hcid, -, -⟩
  ihave #Hrd' := Hrd
  iunfold isServerRead at Hrd'
  icases Hrd' with ⟨%w, #Hw⟩
  iunfold srvReadFieldsAt at Hw
  icases Hw with ⟨-, -, -, -, -, -, -, -, -, -, #Hlgf, %Hlgnn, -, -, -, -, -, -, -, -, -, -, -,
    #Hstf, #Hst⟩
  iunfold stopChan at Hst
  icases Hst with ⟨%γst, #Hst⟩
  ihave Hinit : (srvInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨-, ⟨-, -, -, -, ⟨#HTMR, -⟩⟩, -⟩
  iunfold errVarLeaf at HTMR
  icases HTMR with ⟨%eT, #HeT, %HlT, -⟩
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Pfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  ihave #Perr : isPkgInit (PROP := IProp GF) pkg_id.errors $$ []
  · iPkgInit
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Ptypes : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.types $$ []
  · iPkgInit
  ihave #Pmem : isPkgInit (PROP := IProp GF)
      pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply hMID s v.memberID $$ []
  · iframe #
  ihave Hav2 := Hav
  iStructNamed Hav2
  (try wp_auto)
  -- the request's `ClusterMemberAttrSet`, read-only from here on
  ihave ⟨Hv1, %Hv1n⟩ := typedPointsto_not_null_dup _ _ _ $$ «$v1»
  ihave ⟨Hr0, %Hr0n⟩ := typedPointsto_not_null_dup _ _ _ $$ «$r0»
  iStructNamedPrefix Hv1 "a"
  iStructNamedPrefix Hr0 "r"
  ipersist aName
  ipersist aClientUrls
  ipersist rMember_ID
  ipersist rMemberAttributes
  ihave #Hma : apply.memberAttrSetIs «$r0_ptr» ⟨v.memberID, av.Name', urls⟩ $$ []
  · iunfold apply.memberAttrSetIs
    isplitr
    · ipureintro; exact Hr0n
    iexists «$v1_ptr», av.ClientURLs'
    iframe #
    ipureintro; exact Hv1n
  wp_apply hLg s w.lg $$ [Hlgr] as ⟨-, Hlgr⟩
  · iframe #; iframe Hlgr; ipureintro; exact Hlgnn
  (try wp_auto)
  iclear astate aunknownFields asizeCache a_ rstate runknownFields rsizeCache r_
  wp_for
  wp_apply_core chan.wp_select_nonblocking
  isplit
  · iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.nonblockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, w.stopping, γst
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply ownStopChan_is_chan $$ Hst
      iapply blocking_rcv_implies_nonblocking
      iapply stop_chan_receive _ _ _ _ _ $$ Hst
      iintro ⟨-, -⟩
      -- `<-s.stopping`: warn and return
      (try wp_auto)
      wp_apply hMID s v.memberID $$ []
      · iframe #
      wp_apply hIDS as %ids -
      wp_apply hZS as %f0 -
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %asl ⟨Hasl, -⟩
      (try wp_auto)
      wp_apply hSF _ _ av urls (DFrac.own 1) $$ [Hasl] as %str Hasl
      · iframe #; iframe Hasl
      wp_apply hZS as %f1 -
      wp_apply hZD as %f2 -
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %fsl ⟨-, -⟩
      (try wp_auto)
      wp_apply hW w.lg _ _ $$ []
      · iframe #; ipureintro; exact Hlgnn
      (try wp_auto)
      wp_for_post
      iapply HΦ
      iright; iexact Hrc
    · iapply BigAndL.bigAndL_nil.2; itrivial
  -- `default`: one attempt
  (try wp_auto)
  wp_apply context.wp_WithTimeout ci cd d $$ [] as %ctx' %γ' %cancel %dl ⟨#Hcancel, #Hctx'⟩
  · iframe #
  (try wp_auto)
  -- the fresh `InternalRaftRequest`: read-only but for its `Header`
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
  ihave #HirrNo : irrNoHdrIs «$a1_ptr» (irrMemberAttr ⟨v.memberID, av.Name', urls⟩) $$ []
  · iunfold irrNoHdrIs
    simp only [irrMemberAttr, apply.irrEmpty, apply.optReqIs, apply.presentIs, apply.irrField]
    isplitr
    · ipureintro; exact Hirrn
    isplitr
    · have h0 : (W64 0 : w64) = 0 := by decide
      rw [h0]; iexact ID
    repeat (isplitr; · iexists _; iframe #; try (ipureintro; simp))
    iexists _; iframe #; try (ipureintro; simp)
  ihave HN1 := HNR
  imod HN1
  wp_apply hRR s E ρ ctx' _ «$a1_ptr» (irrMemberAttr ⟨v.memberID, av.Name', urls⟩)
      (fun _ => iprop(True)) F rfl $$ [Hlt HRD HN1 Header] as %resp %err ⟨Hlt, HRD, Hres⟩
  · iframe # Hlt HRD HN1
    isplitr
    · iunfold reqPropOk; ileft; ipureintro
      refine ⟨?_, ?_, rfl⟩
      · simp [plainReq, irrMemberAttr, apply.irrEmpty, apply.dispatchKind]
      · simp [writeKind, irrMemberAttr, apply.irrEmpty, apply.dispatchKind]
    iexists _; iexact Header
  iclear state unknownFields sizeCache
  (try wp_auto)
  wp_apply Hcancel
  (try wp_auto)
  icases Hres with (⟨%Herr, -⟩ | ⟨%Hre, #HaE, -⟩)
  · -- `case nil`: close `readych`, log, return
    subst Herr
    (try wp_auto)
    wp_apply wp_broadcast_chan_close (ty := go.ChannelType go.ChanDir.sendrecv (go.StructType []))
      rc γrc iprop(True) $$ [Hrc] as Hrc
    · iframe Hrc; iintro !>; itrivial
    (try wp_auto)
    wp_apply hMID s v.memberID $$ []
    · iframe #
    wp_apply hIDS as %ids -
    wp_apply hZS as %f0 -
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %asl ⟨Hasl, -⟩
    (try wp_auto)
    wp_apply hSF _ _ av urls (DFrac.own 1) $$ [Hasl] as %str Hasl
    · iframe #; iframe Hasl
    wp_apply hZS as %f1 -
    wp_apply hRCID v.cluster v.cid $$ []
    · iframe #
    wp_apply hIDS as %ids2 -
    wp_apply hZS as %f2 -
    wp_apply hZD as %f3 -
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %fsl ⟨-, -⟩
    (try wp_auto)
    wp_apply hI w.lg _ _ $$ []
    · iframe #; ipureintro; exact Hlgnn
    (try wp_auto)
    wp_for_post
    iapply HΦ
    ileft; iexact Hrc
  · -- `default`: warn; after "too many requests", wait for apply; retry
    obtain ⟨-, Hne⟩ := Hre
    cases err with
    | nil => exact absurd rfl Hne
    | ok ei =>
    (try wp_auto)
    wp_apply hMID s v.memberID $$ []
    · iframe #
    wp_apply hIDS as %ids -
    wp_apply hZS as %f0 -
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %asl ⟨Hasl, -⟩
    (try wp_auto)
    wp_apply hSF _ _ av urls (DFrac.own 1) $$ [Hasl] as %str Hasl
    · iframe #; iframe Hasl
    wp_apply hZS as %f1 -
    wp_apply hZD as %f2 -
    wp_apply hZE as %f3 -
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %fsl ⟨-, -⟩
    (try wp_auto)
    wp_apply hW w.lg _ _ $$ []
    · iframe #; ipureintro; exact Hlgnn
    (try wp_auto)
    wp_apply publish_wp_Is_var hIs (GoInterface.ok ei) eT HlT $$ [] as %b -
    · iframe #
    cases b
    · (try wp_auto)
      wp_for_post
      iframe
    · (try wp_auto)
      wp_apply hWA s E γr d $$ [] as -
      · iframe #
      (try wp_auto)
      wp_for_post
      iframe

end proof

end EtcdGrove
end Perennial
