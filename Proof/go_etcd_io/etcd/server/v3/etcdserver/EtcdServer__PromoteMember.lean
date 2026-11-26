/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart); auth-mediation M2 (2026-11-20).
The forwarding follows `LeaseRenew`'s (`EtcdServer__LeaseRenew.lean`), over a `context.WithTimeout`
child of an `isContext`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__PromoteMember
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__promoteMember
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__waitLeader
public import Spec.go_etcd_io.etcd.server.v3.config.ServerConfig__ReqTimeout
public import Spec.github_com.prometheus.client_golang.prometheus.CounterVec__WithLabelValues
public import Spec.errors.Is
public import Spec.errors.IsCtxErr
public import Spec.errors.IsStatusErr
public import Proof.errors.CtxErr
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.SrvCtxWeak

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- An `errors.New` variable holds a pointer error (a target `errors.Is` takes). -/
private theorem errorsNewVar_ptr (X msg : GoString) :
    EtcdGrove.errorsNewVar (GF := GF) X msg ⊢
      ∃ e : GoInterfaceOk, globalAddr X ↦□ GoInterface.ok e ∗ ⌜ptrTarget (GoInterface.ok e)⌝ := by
  iintro #Hv
  iunfold EtcdGrove.errorsNewVar at Hv
  icases Hv with ⟨%x, #Hx, -⟩
  iexists ⟨go.GoType.PointerType _root_.Perennial.errors.errorString.ty, #x⟩
  iframe Hx
  ipureintro
  intro tii h
  cases h
  exact _root_.Perennial.errors.newVar_isPointerError x

/-- `errors.Is(err, target)` of an error `errors.Is` can take and a pointer target: some boolean. -/
private theorem wp_Is_any (hIs : errors.Is.spec (GF := GF) (hG := hG)) (err target : GoInterface)
    (hpt : ptrTarget target) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.errors ∗ applyErrIs err }}
      (App (App (Val (@! _root_.Perennial.errors.Is)) (Val #err)) (Val #target))
    {{ (b : Bool), RET #b; True }} := by
  iintro %Φ ⟨#Hpk, #Hae⟩ HΦ
  ihave #HT := applyErrIs_tree _ $$ Hae
  ihave ⟨%S, %M, #Htree, %HS⟩ := HT $$ %target
  wp_apply hIs S M err target hpt (HS.2 hpt) $$ [] as %b -
  · iframe #; ipureintro; exact HS.1
  iapply HΦ; itrivial

/-- `promoteMember`'s outcome at a non-`nil` error, with what `PromoteMember` needs of the error
(`errors.Is` and `Error()` take it, its message valid UTF-8), kept. -/
private theorem promote_errFacts [_root_.Perennial.errors.Assumptions] (s : Loc) (E : apply.AEnv GF)
    (n : Nat) (tok : Option GoString) (Pin Pm : IProp GF) (Qm : GoInterface → IProp GF)
    (Qin : GoSlice → GoInterface → IProp GF) (sl : GoSlice) (err : GoInterface)
    (hne : err ≠ GoInterface.nil) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ⊢
      (memCfgAns Qin sl err ∨ (⌜err ≠ GoInterface.nil⌝ ∗ Pin ∗
        ((applyErrIs err ∗ authErrVarIs err ∗ adminWhy s E.authMode n tok err ∗ Pm) ∨
         ((∃ ai : Option go_etcd_io.etcd.server.v3.auth.AuthInfo, adminRes E.authMode ai) ∗
          memChkAns Qm err)))) -∗
      (memCfgAns Qin sl err ∨ (⌜err ≠ GoInterface.nil⌝ ∗ Pin ∗
        ((applyErrIs err ∗ authErrVarIs err ∗ adminWhy s E.authMode n tok err ∗ Pm) ∨
         ((∃ ai : Option go_etcd_io.etcd.server.v3.auth.AuthInfo, adminRes E.authMode ai) ∗
          memChkAns Qm err)))) ∗
      (applyErrIs err ∗ v3rpc.errMsgP err utf8Valid) := by
  iintro #Hpa Hout
  icases Hout with (Hc | ⟨%Hne, HPin, (⟨#Hae, #Hv, Hw, HPm⟩ | ⟨Hai, Hc⟩)⟩)
  · iunfold memCfgAns at Hc
    icases Hc with ⟨HQ, (⟨%Hen, -⟩ | ⟨%Hn2, #Hae, #Hm⟩)⟩
    · exact absurd Hen hne
    isplitl [HQ]
    · ileft; iunfold memCfgAns; iframe HQ; iright; iframe Hae Hm; ipureintro; exact Hn2
    iframe Hae Hm
  · ihave #Hm := errMsgP_of_authErrVarIs err hne $$ Hpa Hv
    isplitl [HPin Hw HPm]
    · iright; iframe HPin; isplitl []
      · ipureintro; exact Hne
      ileft; iframe Hw HPm Hae Hv
    iframe Hae Hm
  · iunfold memChkAns at Hc
    icases Hc with ⟨HQ, (%Hen | ⟨#Hae, #Hm⟩)⟩
    · exact absurd Hen hne
    isplitl [HPin Hai HQ]
    · iright; iframe HPin; isplitl []
      · ipureintro; exact Hne
      iright; iframe Hai; iunfold memChkAns; iframe HQ; iright; iframe Hae Hm
    iframe Hae Hm

set_option hygiene false in
/-- A return of an error of the forwarding (`err ≠ nil`, `Herr : applyErrIs err`): the deferred
`cancel()`, then the postcondition's last disjunct. -/
local macro "promote_err" Herr:ident : tactic => `(tactic| (
  (try wp_auto)
  (try wp_for_post)
  (try wp_for_post)
  (try wp_apply Hcancel)
  (try wp_auto)
  iapply HΦ
  iframe HRD
  iright; iright; iright
  isplitr
  · ipureintro; nofun
  iexact $Herr))

theorem EtcdServer.PromoteMember.wp_proof
    (hPM : EtcdServer.promoteMember.spec (GF := GF) (hG := hG))
    (hWl : EtcdServer.waitLeader.spec (GF := GF) (hG := hG))
    (hReqT : config.ServerConfig.ReqTimeout.spec (GF := GF) (hG := hG))
    (hWLV : prometheus.CounterVec.WithLabelValues.spec (GF := GF) (hG := hG))
    (hIs : errors.Is.spec (GF := GF) (hG := hG))
    (hIsC : errors.IsCtxErr.spec (GF := GF) (hG := hG))
    (hIsS : errors.IsStatusErr.spec (GF := GF) (hG := hG)) :
    EtcdServer.PromoteMember.spec (GF := GF) (hG := hG) := by
  intro s E ρ γr ctx cd tok id Pin Pm Qm Qin Qfw n
  wp_start as ⟨#Hq, #Hr, #Hprt, #Hau, #Hlb, #Hctx, #Hlib, #HtokC, HRD, HPin, HPm, #Hmay, #Hconf,
    #Hfw⟩
  -- `errors.IsCtxErr` takes `context`'s initialization (errors-is-axioms, 2026-11-22)
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  iunfold srvPeerRt at Hprt
  icases Hprt with ⟨%rt, #Hrtf, %Hrt⟩
  ihave Hinit : (srvInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨-, ⟨-, -, -, -, #HsEV⟩, ⟨-, -, -, -, ⟨%cS, #HcS, #HcSs⟩, ⟨%hvF, #HhvF, %HhvFl⟩, -⟩⟩
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply (hPM s E ctx cd tok id Pin Pm (memChkAns Qm) (memCfgAns Qin) n) $$ [$HRD $HPin $HPm]
    as %sl %err ⟨HRD, Hout⟩
  · iframe #
    iunfold mvcc.txnCtx; iright; iexact Hctx
  (try wp_auto)
  rcases err with ei | _
  rotate_left
  · -- `nil`: `learnerPromoteSucceed.Inc()`, the local answer
    (try wp_auto)
    iunfold prometheus.metric.counterSpec at HcSs
    icases HcSs with ⟨#HInc, -⟩
    wp_apply HInc
    (try wp_auto)
    iapply HΦ
    iframe HRD
    icases Hout with (Hc | ⟨%Hne, -⟩)
    · ileft; iexact Hc
    · exact absurd rfl Hne
  (try wp_auto)
  ihave #Pa : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth $$ []
  · iPkgInit
  ihave ⟨Hout, #Hae, #Hmsg⟩ := promote_errFacts s E n tok Pin Pm Qm Qin sl (GoInterface.ok ei)
    (by nofun) $$ Pa Hout
  ihave #Pe : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.errors $$ []
  · iPkgInit
  ihave Hei : (go_etcd_io.etcd.server.v3.etcdserver.errors.errorsInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Pe
  icases Hei with ⟨-, #HNV, -⟩
  ihave #HvNL := errorsNewVars_mem (X := go_etcd_io.etcd.server.v3.etcdserver.errors.ErrNotLeader)
    (m := go!"etcdserver: not leader")
    (by simp [go_etcd_io.etcd.server.v3.etcdserver.errors.errorsMsgs]) $$ HNV
  ihave ⟨%eNL, #HeNL, %HptNL⟩ := errorsNewVar_ptr _ _ $$ HvNL
  (try wp_auto)
  wp_apply (wp_Is_any hIs (GoInterface.ok ei) (GoInterface.ok eNL) HptNL) $$ [] as %bNL -
  · iframe #
  (try wp_auto)
  cases bNL with
  | false =>
    -- `learnerPromoteFailed.WithLabelValues(err.Error()).Inc()`, then the error
    (try wp_auto)
    iunfold v3rpc.errMsgP at Hmsg
    icases Hmsg with ⟨%ei', %Hei', #HEm⟩
    injection Hei' with Hei'
    subst Hei'
    wp_apply HEm as %msg %Hmu
    (try wp_auto)
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %lsl ⟨Hlsl, -⟩
    (try wp_auto)
    wp_apply hWLV hvF _ [go!"Reason"] [msg] _ $$ [Hlsl] as %c ⟨%ci, %Hci, #Hcs, -⟩
    · iframe #; iframe Hlsl; ipureintro
      refine ⟨HhvFl, rfl, ?_⟩
      intro v hv
      rw [List.mem_singleton] at hv
      subst hv; exact Hmu
    subst Hci
    iunfold prometheus.counterSpec at Hcs
    icases Hcs with ⟨#HInc, -⟩
    (try wp_auto)
    wp_apply HInc
    (try wp_auto)
    iapply HΦ
    iframe HRD
    icases Hout with (Hc | ⟨%Hne, HPin, (⟨#Hae', -, Hw, HPm⟩ | ⟨Hai, Hc⟩)⟩)
    · ileft; iexact Hc
    · iright; ileft; iframe HPin Hae; isplitl []
      · ipureintro; exact Hne
      ileft; iframe Hw HPm
    · iright; ileft; iframe HPin Hae; isplitl []
      · ipureintro; exact Hne
      iright; iframe Hai Hc
  | true =>
    -- off the leader: the forwarding
    iclear Hout
    (try wp_auto)
    ihave ⟨⟨%rv, #Hrf⟩, -⟩ := (isServerReqM_split _ _ _ _).1 $$ Hq
    ihave #Hrf' := Hrf
    iunfold srvReqFieldsAtM at Hrf'
    icases Hrf' with ⟨-, -, -, -, -, -, #Hfg, #Hfgok, -, #Het, #Htm, -, -, -, -, #Hmid, #Hlead, -, -,
      -, -, -, -, -, -, %Hcfg⟩
    wp_apply hReqT (structFieldRef EtcdServer go!"Cfg" s) rv.electionTicks rv.tickMs as %tmo -
    · iframe #
    (try wp_auto)
    wp_apply context.wp_WithTimeout ctx cd tmo $$ [] as %cctx %γc %cancel %dl ⟨#Hcancel, #Hcctx, -⟩
    · iframe #
    (try wp_auto)
    ihave #Hcc := Hcctx
    iunfold context.isContext at Hcc
    iNamed Hcc
    ihave #HErrU := HErr $$ %Broadcast.Unknown
    wp_for
    wp_apply HErrU $$ [] as %ce - -
    ihave #Prd : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.read $$ []
    · iPkgInit
    ihave Hri : (go_etcd_io.etcd.server.v3.etcdserver.read.readInit : IProp GF) $$ []
    · iapply isPkgInit_access $$ Prd
    icases Hri with ⟨-, -, -, -, -, -, -, -, #HDE⟩
    icases HDE with ⟨%eD, #HeD, %HlD, -⟩
    ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
    · iPkgInit
    ihave %HvD := deadlineExceeded_value _ $$ Pctx HeD
    -- (#45) the target's description, which `errors.Is` takes
    ihave #HtdD : (∃ m', go_etcd_io.etcd.cache.v3.descIs (GF := GF) (GoInterface.ok eD) m') $$ []
    · rw [HvD]
      iexists _
      iapply go_etcd_io.etcd.cache.v3.descIs_deadlineZero
    icases HsEV with ⟨-, -, -, #HECan, #HETo, -⟩
    ihave ⟨%eCan, #HeCan, #HeCanE⟩ := errVarLeaf_get _ $$ HECan
    ihave ⟨%eTo, #HeTo, #HeToE⟩ := errVarLeaf_get _ $$ HETo
    rcases ce with cei | _
    · -- the loop ends: the child is done
      (try wp_auto)
      simp only [reduceCtorEq, ↓reduceIte]
      cleanup_bool_decide
      try simp only [false_neq_true, decide_false, Bool.false_eq_true, ↓reduceIte]
      (try wp_auto)
      try simp only [_root_.decide_true, ↓reduceIte]
      (try wp_auto)
      -- `if errorspkg.Is(cctx.Err(), context.DeadlineExceeded)`
      wp_apply HErrU $$ [] as %cerr - #Hcv
      (try wp_auto)
      rcases cerr with cei2 | _
      rotate_left
      · ihave #Hso : go_etcd_io.etcd.cache.v3.statusErrOk (GF := GF) GoInterface.nil $$ []
        · iunfold go_etcd_io.etcd.cache.v3.statusErrOk; iintro !> %e %h; cases h
        wp_apply (hIsS GoInterface.nil (GoInterface.ok eD) none (Or.inr (Or.inr HvD)))
          $$ [] as %b1 -
        · iframe #; try iapply go_etcd_io.etcd.cache.v3.isDescs_none
        (try wp_auto)
        cases b1 with
        | true => promote_err HeToE
        | false => promote_err HeCanE
      · simp only [reduceCtorEq, ↓reduceIte]
        wp_apply hIsC (GoInterface.ok cei2) (GoInterface.ok eD) $$ [] as %b1 -
        · iframe #
        (try wp_auto)
        cases b1 with
        | true => promote_err HeToE
        | false => promote_err HeCanE
    (try wp_auto)
    try simp only [_root_.decide_true, ↓reduceIte]
    (try wp_auto)
    -- `leader, err := s.waitLeader(cctx)`
    wp_apply (hWl s E ρ γr cctx _) $$ [] as %ldr %lerr Hl
    · iframe #; iapply v3rpc.ctxDoneErr_of_isContext; iexact Hcctx
    (try wp_auto)
    icases Hl with (⟨%Hln, %mv, %urls, #Hm, #Hurls⟩ | ⟨%Hln, #Hle⟩)
    rotate_left
    · obtain ⟨rfl, Hne⟩ := Hln
      rcases lerr with lei | _
      · promote_err Hle
      · exact absurd rfl Hne
    subst Hln
    (try wp_auto)
    ihave %Hul := ownSlice_len $$ Hurls
    ihave #Hm2 := Hm
    iStructNamed Hm2
    iStructNamed RaftAttributes
    -- the three refusals' error variables
    ihave #HvLNR := errorsNewVars_mem (X := go_etcd_io.etcd.server.v3.etcdserver.errors.ErrLearnerNotReady)
      (m := go!"etcdserver: can only promote a learner member which is in sync with leader")
      (by simp [go_etcd_io.etcd.server.v3.etcdserver.errors.errorsMsgs]) $$ HNV
    ihave ⟨%eLNR, #HeLNR, %HptLNR⟩ := errorsNewVar_ptr _ _ $$ HvLNR
    ihave #Pmb : isPkgInit (PROP := IProp GF)
      pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership $$ []
    · iPkgInit
    ihave Hmi : (go_etcd_io.etcd.server.v3.etcdserver.api.membership.membershipInit : IProp GF) $$ []
    · iapply isPkgInit_access $$ Pmb
    icases Hmi with ⟨-, #HMV, -⟩
    ihave #HvINF := errorsNewVars_mem
      (X := go_etcd_io.etcd.server.v3.etcdserver.api.membership.ErrIDNotFound)
      (m := go!"membership: ID not found")
      (by simp [go_etcd_io.etcd.server.v3.etcdserver.api.membership.membershipErrMsgs]) $$ HMV
    ihave ⟨%eINF, #HeINF, %HptINF⟩ := errorsNewVar_ptr _ _ $$ HvINF
    ihave #HvMNL := errorsNewVars_mem
      (X := go_etcd_io.etcd.server.v3.etcdserver.api.membership.ErrMemberNotLearner)
      (m := go!"membership: can only promote a learner member")
      (by simp [go_etcd_io.etcd.server.v3.etcdserver.api.membership.membershipErrMsgs]) $$ HMV
    ihave ⟨%eMNL, #HeMNL, %HptMNL⟩ := errorsNewVar_ptr _ _ $$ HvMNL
    ihave #Hfw' := Hfw
    iunfold promoteHTTPOk at Hfw'
    (try wp_auto)
    -- `for _, url := range leader.PeerURLs`
    ihave IH : iprop(∃ (j : w64) (u : GoString), "i" ∷ i_ptr ↦ j ∗ "url" ∷ url_ptr ↦ u ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z mv.RaftAttributes'.PeerURLs'.len⌝) $$ [i url]
    · iexists W64 0, _
      simp only [named]
      iframe
      ipureintro; constructor
      · decide
      · have := Hul.2; word
    wp_for IH
    try simp only [if_decide_bool_eq_true]
    wp_if_destruct
    · have Hlt : sint.nat j < urls.length := by unfold sint.nat at *; word
      obtain ⟨u, Hu⟩ : ∃ u, urls[sint.nat j]? = some u := ⟨_, List.getElem?_eq_getElem Hlt⟩
      have Hbnd : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z mv.RaftAttributes'.PeerURLs'.len := ⟨Hj.1, Hif⟩
      rw [ite_eq_left Hbnd]
      icases ownSlice_elem_acc (sint.Z j) u _ DFrac.discard urls Hj.1 Hu $$ Hurls with ⟨#Hue, -⟩
      (try wp_auto)
      -- `resp, err := promoteMemberHTTP(cctx, url, id, s.peerRt)`
      wp_apply Hfw' $$ %cctx %u %rt as %hsl %herr ⟨HQf, #Hhe⟩
      (try wp_auto)
      rcases herr with hei | _
      rotate_left
      · -- `nil`: the leader's answer
        (try wp_auto)
        wp_for_post
        wp_for_post
        wp_apply Hcancel
        (try wp_auto)
        iapply HΦ
        iframe HRD
        iright; iright; ileft
        isplitr
        · ipureintro; rfl
        iexact HQf
      (try wp_auto)
      -- `errorspkg.Is(err, ErrLearnerNotReady) || ... ErrIDNotFound || ... ErrMemberNotLearner`
      wp_apply (wp_Is_any hIs (GoInterface.ok hei) (GoInterface.ok eLNR) HptLNR) $$ [] as %b1 -
      · iframe #
      cases b1 with
      | true => promote_err Hhe
      | false =>
        (try wp_auto)
        wp_apply (wp_Is_any hIs (GoInterface.ok hei) (GoInterface.ok eINF) HptINF) $$ [] as %b2 -
        · iframe #
        cases b2 with
        | true => promote_err Hhe
        | false =>
          (try wp_auto)
          wp_apply (wp_Is_any hIs (GoInterface.ok hei) (GoInterface.ok eMNL) HptMNL) $$ [] as %b3 -
          · iframe #
          cases b3 with
          | true => promote_err Hhe
          | false =>
            (try wp_auto)
            wp_for_post
            iframe
            iexists j + W64 1, u
            iframe
            ipureintro; constructor <;> word
    · (try wp_auto)
      wp_for_post
      iframe


end proof

end EtcdGrove
end Perennial
