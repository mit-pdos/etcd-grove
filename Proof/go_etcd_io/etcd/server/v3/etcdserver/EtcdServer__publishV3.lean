/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__publishV3.lean` (etcd-io/etcd#22525:
the publish loop with the snapshot check). Lean-first (no Rocq counterpart); see `InvPublish.lean`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__publishV3
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__raftRequest
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__hasPublishedAttributes
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__MemberID
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Logger
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__ID
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String
public import Spec.go_etcd_io.etcd.pkg.v3.notify.Notifier__Receive
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Duration
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Logger__Warn
public import Spec.go_uber_org.zap.Logger__Info
public import Spec.fmt.SprintfAttrs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ProposerLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.PublishPool

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

set_option hygiene false in
/-- The log lines' fields: the member id's `String()`, `zap.String` of it, `fmt.Sprintf("%+v",
s.attributes)` and `zap.String` of that. -/
local macro "pub_log_attrs" : tactic => `(tactic| (
  wp_apply hMID s id $$ []
  · iframe #
  wp_apply hIDS as %ids -
  wp_apply hZS as %f0 -
  (try wp_auto)
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %asl ⟨Hasl, -⟩
  (try wp_auto)
  wp_apply hSA _ _ a cus _ _ $$ [Hasl] as %str ⟨-, -⟩
  · iframe #; iframe Hasl
  wp_apply hZS as %f1 -
  (try wp_auto)))

set_option hygiene false in
/-- The log call: the fields' slice literal and `Warn`. -/
local macro "pub_log_warn" : tactic => `(tactic| (
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %fsl ⟨-, -⟩
  (try wp_auto)
  wp_apply hW _ _ _ $$ []
  · iframe #; ipureintro; exact Hlgn
  (try wp_auto)))

set_option hygiene false in
/-- The log call: the fields' slice literal and `Info`. -/
local macro "pub_log_info" : tactic => `(tactic| (
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %fsl ⟨-, -⟩
  (try wp_auto)
  wp_apply hI _ _ _ $$ []
  · iframe #; ipureintro; exact Hlgn
  (try wp_auto)))

set_option hygiene false in
/-- Published (`Hdone : pubDone c id a cus`): `close(s.readych)`, the log line, return with
`readych` closed. -/
local macro "pub_close_ready" : tactic => `(tactic| (
  iunfold srvReady at Hready
  icases Hready with ⟨%rch, %γrch, #Hrch, Hrbc⟩
  (try wp_auto)
  wp_apply (wp_broadcast_chan_close rch γrch iprop(⌜pubDone c id a cus⌝)) $$ [Hrbc] as Hrbc
  · iframe Hrbc; iintro !>; ipureintro; exact Hdone
  (try wp_auto)
  pub_log_attrs
  wp_apply hRCID c cid $$ []
  · iframe #
  wp_apply hIDS as %cids -
  wp_apply hZS as %f2 -
  wp_apply hZD as %f3 -
  (try wp_auto)
  pub_log_info
  wp_for_post
  iapply HΦ
  iframe Hlt Hrd Hlr
  iright
  isplitl [Hrbc]
  · iunfold srvReady; iexists rch, γrch; iframe Hrch Hrbc
  ipureintro; exact Hdone))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem EtcdServer.publishV3.wp_proof
    (hMID : EtcdServer.MemberID.spec (GF := GF) (hG := hG))
    (hLg : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (hRcv : notify.Notifier.Receive.spec (GF := GF) (hG := hG))
    (hHPA : EtcdServer.hasPublishedAttributes.spec (GF := GF) (hG := hG))
    (hRR : EtcdServer.raftRequest.spec (GF := GF) (hG := hG))
    (hRCID : membership.RaftCluster.ID.spec (GF := GF) (hG := hG))
    (hIDS : types.ID.String.spec (GF := GF) (hG := hG))
    (hZS : zap.String.spec (GF := GF) (hG := hG))
    (hZD : zap.Duration.spec (GF := GF) (hG := hG))
    (hZE : zap.Error.spec (GF := GF) (hG := hG))
    (hW : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (hI : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (hSA : fmt.SprintfAttrs.spec (GF := GF) (hG := hG)) :
    EtcdServer.publishV3.spec (GF := GF) (hG := hG) := by
  intro s E ρ c id a cus n d
  wp_start as ⟨#Hreq, #Hpf, Hlt, Hrd, Hlr, Hslots, Hready⟩
  ihave #Hpf' := Hpf
  iunfold srvPubFields at Hpf'
  icases Hpf' with ⟨#Hma, ⟨%cid, #Hcid⟩, ⟨%l, #Hlgf, %Hlgn⟩, ⟨%ctx, %cd, #Hctxf, #Hctx⟩,
    ⟨%st, #Hstf, #Hst⟩, #Hnf, ⟨%F, #HF⟩, #HNR, %Hbound⟩
  ihave #Hma' := Hma
  iunfold srvMemberAttrs at Hma'
  icases Hma' with ⟨#Hidf, #Hcf, #Hrc, #Haf, #Hcus⟩
  ihave Ha2 := Haf
  iStructNamed Ha2
  ihave #Pmem : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership $$ []
  · iPkgInit
  ihave #Pnot : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.notify $$ []
  · iPkgInit
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Pfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  ihave #Ptypes : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.types $$ []
  · iPkgInit
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Patom : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  -- the snapshot check's reader-slot pool: one slot for this thread, the rest pooled
  have hM : 2 ≤ Int.toNat sync.rwmutex.actualMaxReaders := maxReaders_ge2
  icases replicate_take1 _ _ (by omega) $$ Hslots with ⟨Hslot, Hslots⟩
  imod pub_pool_alloc n _ $$ Hslots with ⟨%γp, #Hpool⟩
  have hK : threadBound GF ≤ Int.toNat sync.rwmutex.actualMaxReaders - 1 := by omega
  (try wp_auto)
  wp_apply hMID s id $$ []
  · iframe #
  (try wp_auto)
  -- the request, read-only from here
  ihave ⟨Hv1, %Hv1n⟩ := typedPointsto_not_null_dup _ _ _ $$ «$v1»
  ihave ⟨Hr0, %Hr0n⟩ := typedPointsto_not_null_dup _ _ _ $$ «$r0»
  iStructNamedPrefix Hv1 "pa_"
  iStructNamedPrefix Hr0 "pr_"
  ipersist pa_Name
  ipersist pa_ClientUrls
  ipersist pr_Member_ID
  ipersist pr_MemberAttributes
  ihave #HmAS : apply.memberAttrSetIs «$r0_ptr» ⟨id, a.Name', cus⟩ $$ []
  · iunfold apply.memberAttrSetIs
    isplitr
    · ipureintro; exact Hr0n
    iexists «$v1_ptr», a.ClientURLs'
    iframe #
    ipureintro; exact Hv1n
  ipersist s
  ipersist timeout
  ipersist req
  wp_apply hLg s l $$ [Hlr] as ⟨-, Hlr⟩
  · iframe #; iframe Hlr; ipureintro; exact Hlgn
  (try wp_auto)
  ipersist lg
  ihave HI : iprop(srvLeadTimeReader s ∗ E.RD ∗ srvLgReader s ∗ notifyReader n ∗
      srvReady s iprop(⌜pubDone c id a cus⌝) .Pending) $$ [Hlt Hrd Hlr Hslot Hready]
  · iframe
  iclear pa_state pa_unknownFields pa_sizeCache pr_state pr_unknownFields pr_sizeCache
  wp_for HI
  icases HI with ⟨Hlt, Hrd, Hlr, Hslot, Hready⟩
  ihave #Hst' := Hst
  iunfold stopChan at Hst'
  icases Hst' with ⟨%γst, #Hstc⟩
  wp_apply_core chan.wp_select_nonblocking_alt [iprop(True)]
    iprop(srvLeadTimeReader s ∗ E.RD ∗ srvLgReader s ∗ notifyReader n ∗
      srvReady s iprop(⌜pubDone c id a cus⌝) .Pending ∗
      (srvLeadTimeReader s ∗ E.RD ∗ srvLgReader s ∗
        (srvReady s iprop(⌜pubDone c id a cus⌝) .Pending ∨
          srvReady s iprop(⌜pubDone c id a cus⌝) .Done ∗ ⌜pubDone c id a cus⌝) -∗ Φ #()))
    $$ [] [Hlt Hrd Hlr Hslot Hready HΦ] []
  · iapply BigSepL2.bigSepL2_singleton.2
    iintro ⟨Hlt, Hrd, Hlr, Hslot, Hready, HΦ⟩
    simp only [chan.nonblockingAltClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, st, γst
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply ownStopChan_is_chan $$ Hstc
    iapply stop_chan_nonblocking_receive st γst iprop(True) _ _ .Unknown $$ Hstc
    isplit
    · -- stopping: the warning, and return with `readych` open
      iintro ⟨-, -⟩
      (try wp_auto)
      pub_log_attrs
      wp_apply hZD as %f2 -
      (try wp_auto)
      pub_log_warn
      wp_for_post
      iapply HΦ
      iframe Hlt Hrd Hlr
      ileft
      iexact Hready
    · iintro -
      iframe
  · iframe
  iintro ⟨Hlt, Hrd, Hlr, Hslot, Hready, HΦ⟩ -
  (try wp_auto)
  -- `ctx, cancel := context.WithTimeout(s.ctx, timeout)`
  wp_apply context.wp_WithTimeout ctx cd d $$ [] as %cctx %γc %cancel %dl ⟨#Hcancel, #Hcctx⟩
  · iframe #
  (try wp_auto)
  ipersist ctx
  ipersist cancel
  -- `var publishedBySnapshot atomic.Bool`, under its invariant
  have hz : (zero_val sync.atomic.Bool') =
      ({ _0' := zero_val _, v' := sync.atomic.b32w false } : sync.atomic.Bool') := rfl
  ihave Hpb : sync.atomic.ownBool publishedBySnapshot_ptr (DFrac.own 1) false $$ [publishedBySnapshot]
  · simp only [sync.atomic.ownBool_unseal, sync.atomic.ownBoolDef]
    rw [← hz]; iexact publishedBySnapshot
  imod inv_alloc pubFlagN ⊤ (pubFlagInv publishedBySnapshot_ptr c id a cus) $$ [Hpb] with #Hflag
  · inext; iunfold pubFlagInv; iexists false; iframe Hpb; ipureintro; intro h; cases h
  -- `s.snapshotApplied.Receive()`, the goroutine's argument
  wp_apply hRcv n $$ [Hslot] as %ch0 ⟨Hslot, #Hch0⟩
  · iframe #; iframe Hslot
  (try wp_auto)
  -- the snapshot check's goroutine
  wp_apply wp_fork_tok_body $$ []
  · iintro Htok
    wp_auto_lc 1
    imod pub_pool_take n γp _ hK $$ [$Hpool $Htok $Hlc1] with ⟨Hgs, Hrcpt⟩
    ihave HI2 : iprop((∃ ch : Loc, applied_ptr ↦ ch ∗ notifyChan ch) ∗ notifyReader n ∗
        ownToks γp 1) $$ [applied Hgs Hrcpt]
    · iframe Hgs Hrcpt; iexists ch0; iframe applied; iexact Hch0
    wp_for HI2
    icases HI2 with ⟨⟨%ch, Happ, #Hch⟩, Hgs, Hrcpt⟩
    wp_auto_lc 1
    ihave #Hcctx' := Hcctx
    iNamed Hcctx'
    wp_apply HDone as %chD %γD #HcD
    ihave #Hch' := Hch
    iunfold notifyChan at Hch'
    icases Hch' with ⟨%γch, #Hbc⟩
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- a snapshot was applied: check the membership
      simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch, γch
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply ownBroadcastChan_is_chan $$ Hbc
      iapply broadcast_chan_receive _ _ _ _ _ $$ Hbc
      iintro ⟨-, -⟩
      (try wp_auto)
      wp_apply hRcv n $$ [Hgs] as %ch' ⟨Hgs, #Hch2⟩
      · iframe #; iframe Hgs
      (try wp_auto)
      wp_apply hHPA s c id a cus $$ [] as %b %Hb
      · iframe #
      (try wp_auto)
      wp_if_destruct
      · (try wp_auto)
        wp_for_post
        simp only [named]
        iframe Hgs Hrcpt
        iexists ch'
        iframe Happ Hch2
      · -- held: set the flag, cancel the attempt, exit
        imod pub_pool_give n γp _ $$ [$Hpool $Hgs $Hrcpt $Hlc1] with Htok
        wp_apply_core sync.atomic.Bool.wp_Store $$ [] [-]
        · iexact Patom
        iinv Hflag with Hi Hclose
        all_goals try exact CoPset.subseteq_top
        iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
        iintro Hmask
        inext
        iunfold pubFlagInv at Hi
        icases Hi with ⟨%b0, Hb0, -⟩
        iexists b0
        iframe Hb0
        iintro Hb1
        imod Hmask with -
        imod Hclose $$ [Hb1] with -
        · inext; iunfold pubFlagInv; iexists true; iframe Hb1; ipureintro; intro _; exact Hb rfl
        imodintro
        (try wp_auto)
        wp_apply Hcancel
        (try wp_auto)
        wp_for_post
        iexact Htok
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- the attempt's context is done: exit
      simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, chD, γD
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply context.isContextDone_is_chan $$ HcD
      iapply context.isContextDone_receive _ _ _ _ $$ HcD
      iintro ⟨-, -⟩
      imod pub_pool_give n γp _ $$ [$Hpool $Hgs $Hrcpt $Hlc1] with Htok
      (try wp_auto)
      wp_for_post
      iexact Htok
    iapply BigAndL.bigAndL_nil.2
    itrivial
  (try wp_auto)
  -- `s.raftRequest(ctx, &pb.InternalRaftRequest{ClusterMemberAttrSet: req})`
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
  ihave #HirrNo : irrNoHdrIs «$a1_ptr» (pubReq id a cus) $$ []
  · iunfold irrNoHdrIs
    simp only [pubReq, irrMemberAttrSet, apply.irrEmpty, apply.optReqIs, apply.presentIs,
      apply.irrField]
    isplitr
    · ipureintro; exact Hirrn
    isplitr
    · have h0 : (W64 0 : w64) = 0 := by decide
      rw [h0]; iexact ID
    repeat (isplitr; · iexists _; iframe #; try (ipureintro; simp))
    iexists _; iframe #; try (ipureintro; simp)
  imod HNR with Hcred
  wp_apply hRR s E ρ cctx _ «$a1_ptr» (pubReq id a cus) (fun _ => iprop(True)) F rfl
      $$ [Hlt Hrd Hcred Header] as %resp %err ⟨Hlt, Hrd, Hres⟩
  · iframe # Hlt Hrd Hcred
    isplitl []
    · iunfold reqPropOk; ileft; ipureintro
      refine ⟨?_, ?_, rfl⟩ <;>
        simp [plainReq, writeKind, apply.dispatchKind, pubReq, irrMemberAttrSet, apply.irrEmpty]
    iexists _; iexact Header
  (try wp_auto)
  icases Hres with (⟨%Herr, %hm, %rq', %lb, %Hwire, Hok, -⟩ | ⟨%Hre, -, -⟩)
  · -- the request applied: published by the member's own entry
    subst Herr
    iunfold appliedOk at Hok
    icases Hok with ⟨%x, %x', %o, %skip, %Hstep0, -⟩
    have Hdone : pubDone c id a cus := Or.inr ⟨hm, rq', x, x', o, skip, Hwire, Hstep0.1⟩
    (try wp_auto)
    wp_apply Hcancel
    (try wp_auto)
    pub_close_ready
  · -- the attempt failed
    obtain ⟨-, Hne⟩ := Hre
    (try wp_auto)
    wp_apply Hcancel
    (try wp_auto)
    rcases err with ei | _
    · (try wp_auto)
      -- `publishedBySnapshot.Load()`
      wp_apply_core sync.atomic.Bool.wp_Load $$ [] [-]
      · iexact Patom
      iinv Hflag with Hi Hclose
      all_goals try exact CoPset.subseteq_top
      iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
      iintro Hmask
      inext
      iunfold pubFlagInv at Hi
      icases Hi with ⟨%b0, Hb0, %Hb0h⟩
      iexists b0
      iframe Hb0
      iintro Hb0
      imod Hmask with -
      imod Hclose $$ [Hb0] with -
      · inext; iunfold pubFlagInv; iexists b0; iframe Hb0; ipureintro; exact Hb0h
      imodintro
      (try wp_auto)
      cases b0
      · -- not published by a snapshot: log, and the next attempt
        (try wp_auto)
        pub_log_attrs
        wp_apply hZD as %f2 -
        wp_apply hZE as %f3 -
        (try wp_auto)
        pub_log_warn
        wp_for_post
        simp only [named]
        iframe
      · -- the snapshot check saw the attributes: published
        have Hdone : pubDone c id a cus := Or.inl (Hb0h rfl)
        (try wp_auto)
        pub_close_ready
    · exact absurd rfl Hne

end proof

end EtcdGrove
end Perennial
