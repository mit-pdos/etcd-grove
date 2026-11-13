/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__LeaseRenew.lean`. Lean-first (no
Rocq counterpart); the lease-renew plan (2026-11-01).

On the leader: `ensureLeadership`, `waitAppliedIndex` (unless `FastLeaseKeepAlive` finds the lease),
`checkLeaseRenew`, then the lessor's `Renew`; on `ErrNotPrimary` (or not the leader), the forwarding
loop: `waitLeader`, `checkLeaseRenew`, `RenewHTTP` to each of the leader's peer URLs, over the
`context.WithTimeout` child of a weak context (`v3rpc.wp_WithTimeout_weak`, k8s 7f-4 Addendum T-k).
After the loop, the child's `Err()` is `nil`, a context error or etcd's no-leader error: on a context
error the switch's default case (an unexpected context error, logged) is unreachable (`errors.Is` of
an error with itself is `true`, `errors.IsCtxErr`); otherwise (`errors.IsStatusErr`) it may be
reached, and logs and returns `ErrCanceled`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__LeaseRenew
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__checkLeaseRenew
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__ensureLeadership
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__waitAppliedIndex
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__waitLeader
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Renew
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Lookup
public import Spec.go_etcd_io.etcd.server.v3.lease.leasehttp.RenewHTTP
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__isLeader
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__FeatureEnabled
public import Spec.go_etcd_io.etcd.server.v3.config.ServerConfig__ReqTimeout
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Tracer__Start
public import Spec.go_opentelemetry_io.otel.trace.WithAttributes
public import Spec.go_opentelemetry_io.otel.attribute.Int64
public import Spec.errors.Is
public import Spec.errors.IsCtxErr
public import Spec.errors.IsStatusErr
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Logger
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Logger__Warn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.WithTimeoutWeak
public import Proof.go_etcd_io.etcd.pkg.v3.traceutil.StartLaws

@[expose] public section

set_option linter.unusedSectionVars false
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

/-- The key check over the span's context is one over the caller's: the span keeps the context's
incoming metadata (`Tracer.Start`), which is all the principal's bound reads. -/
private theorem leaseCheckFrom_ctx (s : Loc) (E : apply.AEnv GF) (c c' : GoInterface) (n : Nat)
    (K : go_etcd_io.etcd.server.v3.auth.AuthInfo → IProp GF)
    (h : metadata.incomingOf c = metadata.incomingOf c') :
    leaseCheckFrom s E c n K ⊢ leaseCheckFrom s E c' n K := by
  unfold leaseCheckFrom
  iintro (H | ⟨%info, Hb, Hk⟩)
  · ileft; iexact H
  · iright; iexists info; iframe Hk; iapply (infoBoundM_ctx _ s E c c' info h); iexact Hb

/-- The lessor's error variables `LeaseRenew` returns or compares with (`leaseInit`). -/
private theorem renewErrs [_root_.Perennial.errors.Assumptions] :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ⊢
      (∃ e : GoInterfaceOk, globalAddr go_etcd_io.etcd.server.v3.lease.ErrNotPrimary ↦□
        GoInterface.ok e ∗ applyErrIs (GoInterface.ok e) ∗ ⌜errLeaf e⌝) ∗
      (∃ e : GoInterfaceOk, globalAddr go_etcd_io.etcd.server.v3.lease.ErrLeaseNotFound ↦□
        GoInterface.ok e ∗ applyErrIs (GoInterface.ok e) ∗ ⌜errLeaf e⌝) := by
  iintro #Hpkg
  ihave Hli : (go_etcd_io.etcd.server.v3.lease.leaseInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hli with ⟨#Hnf, -, -, -, -, -, -, -, -, -, #Hnp⟩
  iunfold go_etcd_io.etcd.server.v3.lease.leaseErrVar at Hnf Hnp
  icases Hnp with ⟨%e1, #He1, %Hl1, #Hm1⟩
  icases Hnf with ⟨%e2, #He2, %Hl2, #Hm2⟩
  isplitl
  · iexists e1; iframe He1; isplitl
    · iapply applyErrIs_leaf e1 Hl1; iunfold errMsgOk; iexact Hm1
    · ipureintro; exact Hl1
  · iexists e2; iframe He2; isplitl
    · iapply applyErrIs_leaf e2 Hl2; iunfold errMsgOk; iexact Hm2
    · ipureintro; exact Hl2

/-- etcd's no-leader error is a status error (`rpctypes`' package facts). -/
private theorem noLeader_statusErrOk :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes ⊢
      □ ∀ err : GoInterface, noLeaderErr err -∗ go_etcd_io.etcd.cache.v3.statusErrOk err := by
  iintro #Hp
  ihave Hri : (go_etcd_io.etcd.cache.v3.rpctypesInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hp
  icases Hri with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨%e, #He, #Hs⟩, -⟩
  iintro !> %err #Hn
  iunfold noLeaderErr at Hn
  icases Hn with ⟨%e', #He', %Heq⟩
  icombine He He' gives %h
  subst Heq
  rw [← h]
  iexact Hs

set_option hygiene false in
/-- A return of an error (`err ≠ nil`, `Herr : applyErrIs err`): the span's `End`, then the
postcondition. -/
local macro "renew_err" Herr:ident : tactic => `(tactic| (
  (try wp_auto)
  (try wp_for_post)
  (try wp_apply Hcancel)
  (try wp_auto)
  wp_apply HEnd
  (try wp_auto)
  iapply HΦ
  iframe HRD Htok Hetok Hlgr Hrrd
  iright
  isplitr
  · ipureintro; nofun
  iexact $Herr))

set_option hygiene false in
/-- The switch on the done child's error `cerr` when it is `nil` or etcd's no-leader error
(`Hso : statusErrOk cerr`): each arm returns `ErrTimeout` or `ErrCanceled`, the default one after
logging. -/
local macro "renew_switch_weak" : tactic => `(tactic| (
  -- `case errorspkg.Is(err, context.DeadlineExceeded): return -1, errors.ErrTimeout`
  wp_apply (hIsS cerr (GoInterface.ok eD) (Or.inr (Or.inr ⟨eD, rfl, HlD.2.2.2.1⟩))) $$ [] as %b1 -
  · iframe #
  (try wp_auto)
  cases b1 with
  | true =>
    (try wp_auto)
    renew_err HeToE
  | false =>
    (try wp_auto)
    -- `case errorspkg.Is(err, context.Canceled): return -1, errors.ErrCanceled`
    wp_apply (hIsS cerr (GoInterface.ok eC) (Or.inr (Or.inl ⟨eC, rfl, HlC.1⟩))) $$ [] as %b2 -
    · iframe #
    (try wp_auto)
    cases b2 with
    | true =>
      (try wp_auto)
      renew_err HeCanE
    | false =>
      (try wp_auto)
      -- `default: s.Logger().Warn("Unexpected lease renew context error", zap.Error(err))`
      wp_apply hZE as %f2 -
      (try wp_auto)
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %fsl ⟨-, -⟩
      (try wp_auto)
      wp_apply hLg s w.lg $$ [Hlgr] as ⟨-, Hlgr⟩
      · iframe #; iframe Hlgr
      (try wp_auto)
      wp_apply hWarn w.lg $$ []
      · iframe #
      (try wp_auto)
      renew_err HeCanE))

set_option hygiene false in
/-- The forwarding to the leader (from `cctx, cancel := context.WithTimeout(...)` on). -/
local macro "renew_forward" : tactic => `(tactic| (
  wp_apply hReqT (structFieldRef EtcdServer go!"Cfg" s) rv.electionTicks rv.tickMs as %tmo -
  · iframe #
  (try wp_auto)
  wp_apply v3rpc.wp_WithTimeout_weak ctx1 cd tmo $$ [Hetok]
    as %cctx %γc %cancel %dl ⟨Hetok, #Hcancel, #Hcctx, #Hcvf, #Hccause⟩
  · iframe #; iframe Hetok; try iPkgInit
  (try wp_auto)
  ihave #Hnetw' : http.netCtxOk cctx $$ []
  · iapply http.netCtxOk_of_netCtxOkC
    isplitl []
    · iPkgInit
    iapply http.netCtxOkC_from
    iframe #
  ihave #Hcc := Hcctx
  iunfold v3rpc.ctxChildErr at Hcc
  iNamed Hcc
  wp_for
  wp_apply HErr $$ [] as %ce -
  rcases ce with cei | _
  · -- the loop ends: the context's `Err()` is not `nil`
    (try wp_auto)
    simp only [reduceCtorEq, ↓reduceIte]
    cleanup_bool_decide
    try simp only [false_neq_true, decide_false, Bool.false_eq_true, ↓reduceIte]
    (try wp_auto)
    try simp only [_root_.decide_true, ↓reduceIte]
    (try wp_auto)
    -- `err := cctx.Err()`: `nil`, a context error or etcd's no-leader error
    wp_apply HErr $$ [] as %cerr #Hcv
    ihave #Prd : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.read $$ []
    · iPkgInit
    ihave Hri : (go_etcd_io.etcd.server.v3.etcdserver.read.readInit : IProp GF) $$ []
    · iapply isPkgInit_access $$ Prd
    icases Hri with ⟨-, -, -, -, -, -, -, #HCan, #HDE⟩
    iunfold errVarLeaf at HCan
    icases HCan with ⟨%eC, #HeC, %HlC, -⟩
    icases HDE with ⟨%eD, #HeD, %HlD, -⟩
    icases HsEV with ⟨-, -, -, #HECan, #HETo, -⟩
    ihave ⟨%eCan, #HeCan, #HeCanE⟩ := errVarLeaf_get _ $$ HECan
    ihave ⟨%eTo, #HeTo, #HeToE⟩ := errVarLeaf_get _ $$ HETo
    ihave #Prt : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes $$ []
    · iPkgInit
    ihave #HsoL := noLeader_statusErrOk $$ Prt
    (try wp_auto)
    icases Hcv with (%Hcn | #HcE | #HnL)
    · -- `nil` (the model does not keep `Err()` non-nil once it was)
      ihave #Hso : go_etcd_io.etcd.cache.v3.statusErrOk (GF := GF) cerr $$ []
      · iunfold go_etcd_io.etcd.cache.v3.statusErrOk; iintro !> %e %h; rw [Hcn] at h; cases h
      renew_switch_weak
    rotate_left
    · -- etcd's no-leader error (the parent was the require-leader wrapper, cancelled)
      ihave #Hso := HsoL $$ HnL
      renew_switch_weak
    -- a context error: the default case is unreachable
    -- `case errorspkg.Is(err, context.DeadlineExceeded): return -1, errors.ErrTimeout`
    wp_apply hIsC cerr (GoInterface.ok eD) $$ [] as %b1 %Hb1
    · iframe #
    (try wp_auto)
    cases b1 with
    | true =>
      (try wp_auto)
      renew_err HeToE
    | false =>
      (try wp_auto)
      -- `case errorspkg.Is(err, context.Canceled): return -1, errors.ErrCanceled`
      wp_apply hIsC cerr (GoInterface.ok eC) $$ [] as %b2 %Hb2
      · iframe #
      (try wp_auto)
      cases b2 with
      | true =>
        (try wp_auto)
        renew_err HeCanE
      | false =>
        -- the default case: `err` is one of the two
        iunfold _root_.Perennial.context.isCtxErr at HcE
        icases HcE with (⟨#Hcv, -⟩ | ⟨#Hcv, -⟩)
        · ihave %Hag := typedPointsto_agree_wand _ _ _ _ _ $$ Hcv HeC
          exact absurd (Hb2 Hag) (by simp)
        · ihave %Hag := typedPointsto_agree_wand _ _ _ _ _ $$ Hcv HeD
          exact absurd (Hb1 Hag) (by simp)
  (try wp_auto)
  simp only [_root_.decide_true, ↓reduceIte]
  (try wp_auto)
  -- `leader, lerr := s.waitLeader(cctx)`
  wp_apply (hWl s E ρ γr cctx _) $$ [] as %ldr %lerr Hl
  · iframe #; try (iapply v3rpc.ctxDoneErr_of_child; iexact Hcctx)
  (try wp_auto)
  icases Hl with (⟨%Hln, %mv, %urls, #Hm, #Hurls⟩ | ⟨%Hln, #Hle⟩)
  rotate_left
  · obtain ⟨rfl, Hne⟩ := Hln
    rcases lerr with lei | _
    · renew_err Hle
    · exact absurd rfl Hne
  subst Hln
  (try wp_auto)
  -- `if err := s.checkLeaseRenew(ctx, id); err != nil { return 0, err }`
  wp_apply (hChk s E γl ctx1 _ id n m) $$ [HRD Htok] as %cerr ⟨HRD, Htok, #Hce, Hcok⟩
  · iframe #; iframe HRD Htok; ipureintro; exact Hbound
  rcases cerr with cei | _
  · renew_err Hce
  ihave #Hchk1 := Hcok $$ %rfl
  (try wp_auto)
  ihave %Hul := ownSlice_len $$ Hurls
  ihave #Hm2 := Hm
  iStructNamed Hm2
  iStructNamed RaftAttributes
  ihave #Plh : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease.leasehttp $$ []
  · iPkgInit
  ihave ⟨%pfx, #Hpfx⟩ : (∃ p : GoString,
      globalAddr go_etcd_io.etcd.server.v3.lease.leasehttp.LeasePrefix ↦□ p : IProp GF) $$ []
  · iapply isPkgInit_access $$ Plh
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
    -- `ttl, err := leasehttp.RenewHTTP(cctx, id, lurl, s.peerRt)`
    wp_apply hHttp cctx _ id _ rt $$ [] as %ttl %herr Hh
    · iframe #; isplitl []
      · iapply v3rpc.ctxDoneErr_of_child; iexact Hcctx
      ipureintro; exact Hrt
    (try wp_auto)
    -- `if err == nil || errorspkg.Is(err, lease.ErrLeaseNotFound) { return ttl, err }`
    icases Hh with (%Hhn | ⟨%Hhn, #Hhe⟩)
    · subst Hhn
      (try wp_auto)
      wp_for_post
      wp_for_post
      wp_apply Hcancel
      (try wp_auto)
      wp_apply HEnd
      (try wp_auto)
      iapply HΦ
      iframe HRD Htok Hetok Hlgr Hrrd
      ileft
      isplitr
      · ipureintro; rfl
      iapply leaseCheckFrom_ctx _ _ _ _ _ _ Hinc1; iexact Hchk1
    rcases herr with hei | _
    rotate_left
    · exact absurd rfl Hhn
    (try wp_auto)
    ihave #HT := applyErrIs_tree _ $$ Hhe
    ihave ⟨%S, %M, #Htree, %HS⟩ := HT $$ %(GoInterface.ok eNF)
    have hpt : ptrTarget (GoInterface.ok eNF) := fun tii h => by cases h; exact HNFl.1
    wp_apply hIs S M _ (GoInterface.ok eNF) hpt (HS.2 hpt) $$ [] as %b -
    · iframe #; ipureintro; exact HS.1
    (try wp_auto)
    cases b with
    | true =>
      (try wp_auto)
      wp_for_post
      renew_err Hhe
    | false =>
      (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, u
      iframe
      ipureintro; constructor <;> word
  · (try wp_auto)
    -- `time.Sleep(50 * time.Millisecond)`, then the next round
    try simp only [_root_.decide_true, ↓reduceIte]
    wp_apply time.wp_Sleep
    (try wp_auto)
    wp_for_post
    iframe))

set_option hygiene false in
/-- `if err := s.waitAppliedIndex(); err != nil { return 0, err }`. -/
local macro "renew_wait" : tactic => `(tactic| (
  wp_apply (hWai s E ρ γr) as %werr Hw
  · iframe #
  rcases werr with wei | _
  · icases Hw with (%Hwn | ⟨%Hwn, #Hwe⟩)
    · cases Hwn
    renew_err Hwe
  iclear Hw
  (try wp_auto)))

set_option hygiene false in
/-- The leader's tail: `checkLeaseRenew`, then the lessor's `Renew`; on `ErrNotPrimary`, the
forwarding. -/
local macro "renew_leader_tail" : tactic => `(tactic| (
  wp_apply (hChk s E γl ctx1 _ id n m) $$ [HRD Htok] as %cerr ⟨HRD, Htok, #Hce, Hcok⟩
  · iframe #; iframe HRD Htok; ipureintro; exact Hbound
  rcases cerr with cei | _
  · renew_err Hce
  ihave #Hchk1 := Hcok $$ %rfl
  (try wp_auto)
  wp_apply (hRen lp γl id) $$ [Htok] as %ttl %rerr ⟨Htok, Hre⟩
  · iframe #; iframe Htok; ipureintro; exact Hbound
  (try wp_auto)
  icases Hre with (%Hrn | ⟨%e, #He, %Hre⟩ | ⟨%e, #He, %Hre⟩)
  · subst Hrn
    (try wp_auto)
    wp_apply HEnd
    (try wp_auto)
    iapply HΦ
    iframe HRD Htok Hetok Hlgr Hrrd
    ileft
    isplitr
    · ipureintro; rfl
    iapply leaseCheckFrom_ctx _ _ _ _ _ _ Hinc1; iexact Hchk1
  all_goals (
    subst Hre
    first
      | (ihave %Hee := typedPointsto_agree_wand _ _ _ _ _ $$ He HNP
         injection Hee with Hee; subst e; ihave #Hre' := HNPe)
      | (ihave %Hee := typedPointsto_agree_wand _ _ _ _ _ $$ He HNF
         injection Hee with Hee; subst e; ihave #Hre' := HNFe)
    (try wp_auto)
    -- `if !errorspkg.Is(err, lease.ErrNotPrimary) { return -1, err }`
    ihave #HT := applyErrIs_tree _ $$ Hre'
    ihave ⟨%S, %M, #Htree, %HS⟩ := HT $$ %(GoInterface.ok eNP)
    have hpt : ptrTarget (GoInterface.ok eNP) := fun tii h => by cases h; exact HNPl.1
    wp_apply hIs S M _ (GoInterface.ok eNP) hpt (HS.2 hpt) $$ [] as %b -
    · iframe #; ipureintro; exact HS.1
    (try wp_auto)
    cases b with
    | false => renew_err Hre'
    | true =>
      (try wp_auto)
      renew_forward)))

set_option maxHeartbeats 4000000 in
theorem EtcdServer.LeaseRenew.wp_proof
    (hEns : EtcdServer.ensureLeadership.spec (GF := GF) (hG := hG))
    (hWai : EtcdServer.waitAppliedIndex.spec (GF := GF) (hG := hG))
    (hWl : EtcdServer.waitLeader.spec (GF := GF) (hG := hG))
    (hChk : EtcdServer.checkLeaseRenew.spec (GF := GF) (hG := hG))
    (hRen : lease.lessor.Renew.spec (GF := GF) (hG := hG))
    (hLk : lease.lessor.Lookup.spec (GF := GF) (hG := hG))
    (hHttp : leasehttp.RenewHTTP.spec (GF := GF) (hG := hG))
    (hIsL : EtcdServer.isLeader.spec (GF := GF) (hG := hG))
    (hFE : EtcdServer.FeatureEnabled.spec (GF := GF) (hG := hG))
    (hReqT : config.ServerConfig.ReqTimeout.spec (GF := GF) (hG := hG))
    (hStart : traceutil.Tracer.Start.spec (GF := GF) (hG := hG))
    (hWithAttr : trace.WithAttributes.spec (GF := GF) (hG := hG))
    (hInt64 : «attribute».Int64.spec (GF := GF) (hG := hG))
    (hIs : errors.Is.spec (GF := GF) (hG := hG))
    (hIsC : errors.IsCtxErr.spec (GF := GF) (hG := hG))
    (hIsS : errors.IsStatusErr.spec (GF := GF) (hG := hG))
    (hLg : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (hZE : zap.Error.spec (GF := GF) (hG := hG))
    (hWarn : zap.Logger.Warn.spec (GF := GF) (hG := hG)) :
    EtcdServer.LeaseRenew.spec (GF := GF) (hG := hG) := by
  intro s E ρ γr γl ctx cd id n m
  wp_start as ⟨#Hq, #Hr, #Hau, #Hlb, #Hlr, #Hpub, #Hmlb, #Hctx, Hetok, #Hlib, #Hnet, #Hcause, HRD, #Hpool,
    Htok, Hlgr, Hrrd, %Hbound, #Hprt⟩
  ihave #Hr' := Hr
  iunfold isServerReadM at Hr'
  icases Hr' with ⟨%w, #Hw⟩
  iunfold srvReadFieldsAtM at Hw
  icases Hw with ⟨-, -, -, -, -, -, -, -, -, #Hlgf, #Hlgn, -⟩
  iunfold srvPeerRt at Hprt
  icases Hprt with ⟨%rt, #Hrtf, %Hrt⟩
  wp_auto
  wp_apply wp_with_defer as %defer defer
  ihave Hinit : (srvInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨-, ⟨-, -, -, ⟨%tr, #Htr⟩, #HsEV⟩, -⟩
  ihave #Pattr : isPkgInit (PROP := IProp GF) pkg_id.go_opentelemetry_io.otel.«attribute» $$ []
  · iPkgInit
  ihave #Potr : isPkgInit (PROP := IProp GF) pkg_id.go_opentelemetry_io.otel.trace $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply hInt64 as %kv1 -
  (try wp_auto)
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %asl ⟨-, -⟩
  (try wp_auto)
  wp_apply hWithAttr as %opt -
  (try wp_auto)
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %osl ⟨-, -⟩
  (try wp_auto)
  ihave #Hlib' := Hlib
  iunfold context.libCtxOk at Hlib'
  icases Hlib' with ⟨-, -, -, #Hspv⟩
  wp_apply (hStart tr ctx cd _ _) $$ [] as %ctx1 %sp
    ⟨-, #Hwkw, -, %Hinc1, #Hsp, -, -, #Hlibw, #Hnetw, #Hcausew⟩
  · iframe #
  ihave #Hctx1 := Hwkw $$ Hctx
  ihave #Hlib1 := Hlibw $$ Hlib
  ihave #Hnet1 := Hnetw $$ Hnet
  ihave #Hcause1 := Hcausew $$ Hcause
  iunfold trace.isSpan at Hsp
  icases Hsp with ⟨%si, %Hsi, #HEnd, -, -⟩
  subst Hsi
  ihave ⟨⟨%rv, #Hrf⟩, -⟩ := (isServerReqM_split _ _ _ _).1 $$ Hq
  ihave #Hrf' := Hrf
  iunfold srvReqFieldsAtM at Hrf'
  icases Hrf' with ⟨-, -, -, -, -, -, #Hfg, #Hfgok, -, #Het, #Htm, -, -, -, -, #Hmid, #Hlead, -, -,
    -, -, -, -, -, -, %Hcfg⟩
  (try wp_auto)
  -- `if s.isLeader()`
  wp_apply (hIsL s rv.memberID) as %isl -
  · iframe #; iunfold srvAtomicU64 at Hlead; iunfold srvLeadInv; iexact Hlead
  ihave #Hlp : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease $$ []
  · iPkgInit
  ihave ⟨⟨%eNP, #HNP, #HNPe, %HNPl⟩, ⟨%eNF, #HNF, #HNFe, %HNFl⟩⟩ := renewErrs $$ Hlp
  ihave #Hlr' := Hlr
  iunfold srvLessorRd at Hlr'
  icases Hlr' with ⟨%lp, #Hlf, #Hinv⟩
  ihave #Hinv' := Hinv
  iunfold lease.lessorInv at Hinv'
  icases Hinv' with ⟨-, #Hpin, -, -⟩
  ihave #Htx1 : (mvcc.txnCtx (GF := GF) ctx1 cd ∨ srvCtxWeak ctx1 cd) $$ []
  · iright; iexact Hctx1
  (try wp_auto)
  cases isl with
  | true =>
    (try wp_auto)
    -- `if !s.ensureLeadership() { return -1, lease.ErrNotPrimary }`
    -- (revoke-open Q5, 2026-11-06) `ensureLeadership` takes a level of the thread token: level 0,
    -- the one the spec takes (`lessorLvl`), returned before the check and `Renew`
    wp_apply (hEns s E ρ γr lease.lessorLvl) $$ [$Hlgr $Hrrd $Htok] as %b ⟨Hlgr, Hrrd, Htok⟩
    · iframe #; ipureintro; exact Hbound
    (try wp_auto)
    cases b with
    | false =>
      (try wp_auto)
      renew_err HNPe
    | true =>
    (try wp_auto)
    -- `if s.FeatureEnabled(features.FastLeaseKeepAlive)`
    wp_apply (hFE s rv.fg _ none) as %fe -
    · iframe #; ipureintro; simp [serverFeatures]
    (try wp_auto)
    cases fe with
    | true =>
      -- `le := s.lessor.Lookup(id)`, its slot borrowed from the pool for the call (the lease-src
      -- plan), its later stripped by the next steps
      iapply fupd_wp
      imod lease.lessorRdPool_borrow γl ⊤ (fun _ _ => CoPset.mem_full) $$ [Hpool Htok]
        with ⟨Hrdo, Hback⟩
      · iframe #; iframe
      imodintro
      (try wp_auto)
      iunfold lease.lessorRdOf at Hrdo
      icases Hrdo with ⟨%lp', #Hpin', Hrd⟩
      ihave %Heq := lease.lessorPin_agree γl lp lp' $$ [$Hpin $Hpin']
      subst Heq
      wp_apply (hLk lp γl id m none) $$ [$Hrd] as %l ⟨Hrd, -, -⟩
      · iframe Hinv Hmlb
        rw [lease.lookupView_none]; itrivial
      -- the slot back, for the token
      iapply fupd_wp
      imod Hback $$ [Hrd] with Htok
      · iunfold lease.lessorRdOf; iexists lp; iframe Hpin Hrd
      imodintro
      (try wp_auto)
      wp_if_destruct
      · renew_wait
        renew_leader_tail
      · (try wp_auto)
        renew_leader_tail
    | false =>
      (try wp_auto)
      renew_wait
      renew_leader_tail
  | false =>
    (try wp_auto)
    renew_forward

end proof

end EtcdGrove
end Perennial
