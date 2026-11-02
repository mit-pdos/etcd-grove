module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer__leaseKeepAlive
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.togRPCError
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.header__fill
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.isClientCtxErr
public import Perennial.Spec.errors.Is
public import Spec.errors.Is
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvWatch
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ServerKV
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- The receiver's token knows the request at each position it received. -/
private theorem srvRecvTok_upAtK (γ : StreamNames) (L : List KaReqM) (q : KaReqM) :
    srvRecvTok (GF := GF) (Req := pbLeaseKeepAliveRequest) γ (L ++ [q]) ⊢
      srvRecvTok (Req := pbLeaseKeepAliveRequest) γ (L ++ [q]) ∗
        upAt (Req := pbLeaseKeepAliveRequest) γ L.length q := by
  unfold srvRecvTok upAt monoListIdxOwn
  iintro ⟨H1, #H2⟩
  iframe H1 H2
  ipureintro
  simp

set_option hygiene false in
/-- The loop's return of a stream error, logged (`Debug` for a client's context error, else `Warn`
and `streamFailures` counted): the label slice `lbl` (`"receive"` or `"send"`). -/
local macro "ka_log_ret" lbl:term:max : tactic => `(tactic| (
    wp_auto
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
      iintro %fs -
      wp_auto
      wp_apply hZW lg _ _ $$ []
      · iframe #; ipureintro; exact Hlg
      wp_apply wp_slice_literal (V := GoString) [$lbl, go!"lease-keepalive"]
      isplitr
      · ipureintro; rfl
      iintro %lsl ⟨Hlsl, -⟩
      wp_auto
      wp_apply hCV cvF _ [go!"Type", go!"API"] _ _ $$ [Hlsl] as %c ⟨%ci', %Hc, #Hcs, -⟩
      · iframe #; iframe Hlsl; ipureintro
        exact ⟨HcvFl, prometheus.labelValuesOk_two _ _ _ _ (by decide) (by decide)⟩
      subst Hc
      iunfold prometheus.counterSpec at Hcs
      icases Hcs with ⟨#Hcs, -⟩
      wp_apply Hcs
      wp_for_post
      iapply HΦ
      iframe; iframe #
    · wp_apply hZE as %f -
      wp_apply wp_slice_literal (l := [f])
      isplitr
      · ipureintro; rfl
      iintro %fs -
      wp_auto
      wp_apply hZD lg _ _ $$ []
      · iframe #; ipureintro; exact Hlg
      wp_for_post
      iapply HΦ
      iframe; iframe #))

/-- The `j`th response `(id, ttl)` of the `j`th request `q` (`q.id = id`): its `Dn`, from the stream's
specification, given a TTL of `0` or the check's verdict. -/
private theorem ka_dn (s : Loc) (E : apply.AEnv GF) (γl : GName) (γs : StreamNames)
    (tok : Option GoString) (Dn : Nat → (w64 × w64) → IProp GF) (j : Nat) (q : KaReqM)
    (id ttl : w64) (hid : q.id = id) :
    v3rpc.kaStreamSpec s E γl γs tok Dn ∗ upAt (Req := pbLeaseKeepAliveRequest) γs j q ∗
      (⌜ttl = W64 0⌝ ∨ v3rpc.leaseCheckT s E tok q.nb
        (fun info => leaseKeysVerdictFrom E.authMode q.nb info γl q.mb id .write)) ⊢
      Dn j (id, ttl) := by
  subst hid
  iintro ⟨#Hs, #Hu, Hv⟩
  iunfold v3rpc.kaStreamSpec at Hs
  icases Hs $$ %j %(q.id, ttl) with ⟨-, Hb⟩
  iapply Hb
  iunfold v3rpc.kaDn
  iexists q
  iframe Hu
  isplitr
  · ipureintro; rfl
  iexact Hv

set_option hygiene false in
/-- The response `(req.ID, $t)` sent (its `Dn` in `HDn`): the loop goes on, or a failed `Send` is
logged and returned. -/
local macro "ka_send" t:term:max : tactic => `(tactic| (
    (try wp_auto)
    ipersist Header
    ipersist ID
    ipersist TTL
    ihave #Hmsg : keepAliveRespMsg «$r0_ptr» (v.ID', $t) $$ []
    · iunfold keepAliveRespMsg
      isplitr
      · ipureintro; exact Hrn0
      iexists _
      iframe #
    wp_bind (App (Val #(methods si.ty go!"Send" si.v)) (Val #«$r0_ptr»))
    ihave #HSd := HSend $$ %Ld %«$r0_ptr» %(v.ID', $t)
    iapply HSd $$ [Hstt HDn]
    · iframe; iframe #
    iintro !> %serr Hsr
    icases Hsr with (⟨%Hserr, Hstt⟩ | ⟨%Hne', #Hse', Hstt⟩)
    rotate_left
    · rcases serr with ei | _
      · ka_log_ret go!"send"
      · exact absurd rfl Hne'
    subst Hserr
    (try wp_auto)
    wp_for_post
    iframe
    iexists (L ++ [q]), (Ld ++ [(v.ID', $t)])
    iframe
    ipureintro; simp [Hlen]))

theorem v3rpc.LeaseServer.leaseKeepAlive.wp_proof
    (hIs : errors.Is.spec (GF := GF) (hG := hG))
    (hTog : v3rpc.togRPCError.spec (GF := GF) (hG := hG))
    (hFill : v3rpc.header.fill.spec (GF := GF) (hG := hG))
    (hICE : v3rpc.isClientCtxErr.spec (GF := GF) (hG := hG))
    (hZD : zap.Logger.Debug.spec (GF := GF) (hG := hG))
    (hZW : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (hZE : zap.Error.spec (GF := GF) (hG := hG))
    (hCV : prometheus.CounterVec.WithLabelValues.spec (GF := GF) (hG := hG)) :
    v3rpc.LeaseServer.leaseKeepAlive.spec (GF := GF) (hG := hG) := by
  intro p s A cid mid E γl S' st γs Up Dn ci cd
  wp_start as ⟨#Hls, #HRn, #Hst, #Hspec, #HUp, Hrt, Hstt, HS, HR⟩
  ihave #Hls' := Hls
  iunfold v3rpc.leaseServerAt at Hls'
  icases Hls' with ⟨%Hpn, #Hhdr, #Hle, %lg, %Hlg, #Hlgf⟩
  ihave #Hst' := Hst
  iunfold srvStreamIs at Hst'
  icases Hst' with ⟨%si, %Hsi, #HRecv, #HSend, #HCtx, #Hctxis, #Hrunctx⟩
  iunfold v3rpc.raftLeaseRenew at HRn
  ihave #Hlp : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease $$ []
  · iPkgInit
  ihave ⟨%eNF, #HNF, #HNFe, %HNFl⟩ := v3rpc.leaseNotFoundErr $$ Hlp
  ihave #Pio : isPkgInit (PROP := IProp GF) pkg_id.io $$ []
  · iPkgInit
  ihave #Heof := v3rpc.eofVar_of_init $$ Pio
  iunfold v3rpc.eofVar at Heof
  icases Heof with ⟨%eofE, #HeofG, %HeofL, #HeofM⟩
  ihave #Perr : isPkgInit (PROP := IProp GF) pkg_id.errors $$ []
  · iPkgInit
  ihave #Pv3 : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc $$ []
  · iPkgInit
  ihave #Hvars := v3rpc.watchVars_of_init $$ [Pv3]
  · iframe #; iunfold v3rpc.eofVar; iexists eofE; iframe #; ipureintro; exact HeofL
  iunfold v3rpc.watchVars at Hvars
  icases Hvars with ⟨-, #Hwpv⟩
  iunfold v3rpc.watchPkgVars at Hwpv
  icases Hwpv with ⟨-, -, -, -, -, -, -, -, -, -, -, -, #HstreamF, -, -, -, -, -, -, -⟩
  icases HstreamF with ⟨%cvF, #HcvF, %HcvFl⟩
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Hctx2 := Hctxis
  iNamed Hctx2
  ihave #HErrU := HErr $$ %Broadcast.Unknown
  wp_auto
  ihave Hinv : iprop(∃ (L : List KaReqM) (Ld : List (w64 × w64)),
      "Hrt" ∷ srvRecvTok (Req := pbLeaseKeepAliveRequest) γs L ∗
      "Hstt" ∷ srvSendTok (Rep := pbLeaseKeepAliveResponse) γs Ld ∗
      "%Hlen" ∷ ⌜Ld.length = L.length⌝ ∗ "HS" ∷ S' ∗ "HR" ∷ A.revR) $$ [Hrt Hstt HS HR]
  · iexists [], []; iframe; ipureintro; rfl
  wp_for Hinv
  rw [Hsi]
  wp_apply HRecv $$ Hrt as %req %err Hrr
  icases Hrr with (⟨%Herr, %q, ⟨%v, Hreq, %Hqv⟩, HUpq, Hrt⟩ | ⟨#Heofi, %Hne, Hrt, #Hcl⟩ |
    ⟨%Hne, #Hse, Hrt⟩)
  · -- a request
    subst Herr
    wp_apply hIs (· = GoInterface.nil) (fun _ => False) GoInterface.nil (GoInterface.ok eofE)
      (fun tii h => by cases h; exact HeofL.1.1) (by intro ii tii h; cases h) $$ [] as %b ⟨%Hb, -, -⟩
    · iframe #
      isplitl
      · iintro !> %ii %h; cases h
      · ipureintro; rfl
    have hb : b = false := by simpa using Hb (Or.inl rfl)
    subst hb
    wp_auto
    -- `ls.hdr.fill(resp.Header)`
    ihave %Hvn := typedPointsto_not_null _ _ _ $$ «$v1»
    iStructNamed «$v1»
    ihave Hwh : v3rpc.hdrW «$v1_ptr» $$ [ClusterId MemberId RaftTerm LeaderId]
    · iunfold v3rpc.hdrW
      isplitr
      · ipureintro; exact Hvn
      iexists _, _, _, _
      iframe
    imod (v3rpc.hdrRev_in ⊤ A.revR «$v1_ptr» _) $$ [Revision HR] with ⟨Hin, Hkeep⟩
    · iframe
    wp_apply (hFill _ s A cid mid «$v1_ptr» _) $$ [Hwh Hin] as ⟨-, %r', Hout⟩
    · iframe; iframe #
    ihave ⟨HR, -⟩ := v3rpc.hdrRev_out A.revR «$v1_ptr» _ r' $$ [Hkeep Hout]
    · iframe
    iclear state unknownFields sizeCache
    -- `ls.le.LeaseRenew(stream.Context(), lease.LeaseID(req.ID))`
    (try wp_auto)
    wp_bind (App (Val #(methods si.ty go!"Context" si.v)) (Val #()))
    iapply HCtx
    · itrivial
    iintro !> -
    wp_auto
    ihave #HUp' := HUp
    iunfold v3rpc.kaUpOk at HUp'
    ihave #HUq := HUp' $$ HUpq
    iunfold v3rpc.kaUp at HUq
    icases HUq with ⟨#Hnb, #Hmb⟩
    ihave #HRn' := HRn $$ %ci %cd %v.ID' %q.nb %q.mb
    wp_apply HRn' $$ [HS] as %ttl %rerr ⟨HS, Hans⟩
    · iframe; iframe #
    (try wp_auto)
    ihave ⟨Hrt, #Hupq⟩ := srvRecvTok_upAtK γs L q $$ Hrt
    ihave %Hrn0 := typedPointsto_not_null _ _ _ $$ «$r0»
    iStructNamed «$r0»
    iunfold v3rpc.renewAns at Hans
    icases Hans with (⟨%He, Hchk⟩ | ⟨%Hne, #Hae⟩)
    · subst He
      wp_apply hIs (· = GoInterface.nil) (fun _ => False) GoInterface.nil (GoInterface.ok eNF)
        (fun tii h => by cases h; exact HNFl.1) (by intro ii tii h; cases h) $$ [] as %b ⟨%Hb, -, -⟩
      · iframe #
        isplitl
        · iintro !> %ii %h; cases h
        · ipureintro; rfl
      have hb : b = false := by simpa using Hb (Or.inl rfl)
      subst hb
      ihave HDn : Dn Ld.length (v.ID', ttl) $$ [Hchk]
      · rw [Hlen]
        iapply (ka_dn s E γl γs _ Dn L.length q v.ID' ttl Hqv)
        iframe #
        iright
        iapply v3rpc.leaseCheckT_of_from
        iexact Hchk
      ka_send ttl
    · cases rerr with
      | nil => exact absurd rfl Hne
      | ok ei =>
        ihave #HIsT := applyErrIs_tree _ $$ Hae
        ihave ⟨%S0, %M0, #Ht0, %HS0⟩ := HIsT $$ %(GoInterface.ok eNF)
        wp_apply hIs S0 M0 (GoInterface.ok ei) (GoInterface.ok eNF)
          (fun tii h => by cases h; exact HNFl.1) (HS0.2 (fun tii h => by cases h; exact HNFl.1))
          $$ [] as %b -
        · iframe #; ipureintro; exact HS0.1
        cases b with
        | true =>
          ihave HDn : Dn Ld.length (v.ID', W64 0) $$ []
          · rw [Hlen]
            iapply (ka_dn s E γl γs _ Dn L.length q v.ID' (W64 0) Hqv)
            iframe #
            ileft; ipureintro; rfl
          ka_send (W64 0)
        | false =>
          wp_auto
          wp_apply hTog $$ [] as %e -
          · iapply srvErrIs_of_applyErrIs _ Hne $$ Hae
          (try wp_auto)
          wp_for_post
          iapply HΦ
          iframe; iframe #
  · -- io.EOF
    iunfold eofIs at Heofi
    icombine Heofi HeofG gives %Heq
    subst Heq
    wp_apply hIs (· = GoInterface.ok eofE) (fun _ => False) (GoInterface.ok eofE)
      (GoInterface.ok eofE) (fun tii h => by cases h; exact HeofL.1.1)
      (_root_.Perennial.errors.treeTyped_pointer eofE _ HeofL.1.1) $$ [] as %b ⟨-, %Hb2, -⟩
    · iframe #
      isplitl
      · iapply _root_.Perennial.errors.errorIsTree_leaf eofE _ _ HeofL.1.2.1 HeofL.1.2.2
      · ipureintro; rfl
    have hb : b = true := Hb2 _ rfl HeofL.1.1 rfl
    subst hb
    wp_auto
    wp_for_post
    iapply HΦ
    iframe; iframe #
  · -- another error
    iunfold streamErr at Hse
    icases Hse with ⟨%Hty, #HseT⟩
    ihave ⟨%S, %M, #Ht, %HS⟩ := HseT $$ %(GoInterface.ok eofE)
    wp_apply hIs S M err (GoInterface.ok eofE) (fun tii h => by cases h; exact HeofL.1.1)
      (HS.2 (fun tii h => by cases h; exact HeofL.1.1)) $$ [] as %b -
    · iframe #; ipureintro; exact HS.1
    wp_if_destruct
    rotate_left
    · wp_for_post
      iapply HΦ
      iframe; iframe #
    rcases err with ei | _
    · ka_log_ret go!"receive"
    · exact absurd rfl Hne

end proof

end EtcdGrove
end Perennial
