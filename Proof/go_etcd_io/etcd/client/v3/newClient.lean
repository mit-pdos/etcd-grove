/-
Proof of `Spec/go_etcd_io/etcd/client/v3/newClient.lean` (pr-verify etcd#21714). Lean-first (no
Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.newClient
public import Spec.go_etcd_io.etcd.client.v3.ClientLogLevel
public import Spec.go_etcd_io.etcd.client.v3.Client__SetEndpoints
public import Spec.go_etcd_io.etcd.client.v3.Client__dialWithBalancer
public import Spec.go_etcd_io.etcd.client.v3.Client__Close
public import Spec.go_etcd_io.etcd.client.v3.Client__checkVersion
public import Spec.go_etcd_io.etcd.client.v3.Client__autoSync
public import Spec.go_etcd_io.etcd.client.v3.Client__getToken
public import Spec.go_etcd_io.etcd.client.v3.NewCluster
public import Spec.go_etcd_io.etcd.client.v3.NewKVAny
public import Spec.go_etcd_io.etcd.client.v3.NewLease
public import Spec.go_etcd_io.etcd.client.v3.NewWatcherAny
public import Spec.go_etcd_io.etcd.client.v3.NewAuth
public import Spec.go_etcd_io.etcd.client.v3.NewMaintenance
public import Spec.go_etcd_io.etcd.client.v3.credentials.NewTransportCredential
public import Spec.go_etcd_io.etcd.client.v3.credentials.NewPerRPCCredentialBundle
public import Spec.go_etcd_io.etcd.client.v3.internal.resolver.New
public import Spec.go_etcd_io.etcd.client.v3.internal.resolver.EtcdManualResolver__Close
public import Spec.go_etcd_io.etcd.client.pkg.v3.logutil.CreateDefaultZapLogger
public import Spec.go_uber_org.zap.Config__Build
public import Spec.go_uber_org.zap.Logger__Named
public import Spec.google_golang_org.grpc.MaxCallSendMsgSize
public import Spec.google_golang_org.grpc.MaxCallRecvMsgSize
public import Spec.context.TODO
public import Spec.context.WithCancelTODO
public import Perennial.Proof.strings

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3
open go_etcd_io.etcd.cache.v3 (errorStringSpec)

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `context.WithCancel(bc)` makes a cancellable child of `bc`: a context of the model with the
descriptor `s` (made `PDone := True` with a new name) and its cancel function, callable from
anywhere. What `newClient` needs of its base context (`TODO()`'s, or the configuration's). -/
def withCancelOk (bc : GoInterface) : IProp GF :=
  iprop(∃ (vs : GMap GoInterface GoInterface) (dl : Option time.Time), □ ∀ Φ : val → IProp GF,
    isPkgInit (PROP := IProp GF) pkg_id.context -∗
    ▷ (∀ (ctx' : GoInterfaceOk) (γ' : context.ContextNames) (cancel : GoFunc),
        context.cancelSpec cancel γ' iprop(True) ∗
        context.isContext ctx' { Values := vs, Deadline := dl, Done_gn := γ', PDone := iprop(True) } -∗
        Φ (PairV #(interface.ok ctx') #cancel)) -∗
    WP (App (Val (@! _root_.Perennial.context.WithCancel)) (Val #bc)) {{ Φ }})

instance withCancelOk_persistent (bc : GoInterface) : Persistent (withCancelOk (GF := GF) bc) := by
  unfold withCancelOk; infer_instance

set_option maxHeartbeats 4000000 in
theorem newClient.wp_proof
    (wp_NewTransportCredential : credentials.NewTransportCredential.spec (GF := GF) (hG := hG))
    (wp_TODO : context.TODO.spec (GF := GF) (hG := hG))
    (wp_WithCancelTODO : context.WithCancelTODO.spec (GF := GF) (hG := hG))
    (wp_Build : zap.Config.Build.spec (GF := GF) (hG := hG))
    (wp_ClientLogLevel : ClientLogLevel.spec (GF := GF) (hG := hG))
    (wp_CreateDefaultZapLogger : logutil.CreateDefaultZapLogger.spec (GF := GF) (hG := hG))
    (wp_Named : zap.Logger.Named.spec (GF := GF) (hG := hG))
    (wp_NewPerRPCCredentialBundle : credentials.NewPerRPCCredentialBundle.spec (GF := GF) (hG := hG))
    (wp_MaxCallSendMsgSize : grpc.MaxCallSendMsgSize.spec (GF := GF) (hG := hG))
    (wp_MaxCallRecvMsgSize : grpc.MaxCallRecvMsgSize.spec (GF := GF) (hG := hG))
    (wp_Errorf : fmt.Errorf.spec (GF := GF) (hG := hG))
    (wp_resolverNew : resolver.New.spec (GF := GF) (hG := hG))
    (wp_SetEndpoints : Client.SetEndpoints.spec (GF := GF) (hG := hG))
    (wp_dialWithBalancer : Client.dialWithBalancer.spec (GF := GF) (hG := hG))
    (wp_resolverClose : resolver.EtcdManualResolver.Close.spec (GF := GF) (hG := hG))
    (wp_ErrorfWrap : fmt.ErrorfWrap.spec (GF := GF) (hG := hG))
    (wp_NewCluster : NewCluster.spec (GF := GF) (hG := hG))
    (wp_NewKV : NewKVAny.spec (GF := GF) (hG := hG))
    (wp_NewLease : NewLease.spec (GF := GF) (hG := hG))
    (wp_NewWatcher : NewWatcherAny.spec (GF := GF) (hG := hG))
    (wp_NewAuth : NewAuth.spec (GF := GF) (hG := hG))
    (wp_NewMaintenance : NewMaintenance.spec (GF := GF) (hG := hG))
    (wp_getToken : Client.getToken.spec (GF := GF) (hG := hG))
    (wp_Close : Client.Close.spec (GF := GF) (hG := hG))
    (wp_checkVersion : Client.checkVersion.spec (GF := GF) (hG := hG))
    (wp_autoSync : Client.autoSync.spec (GF := GF) (hG := hG)) :
    newClient.spec (GF := GF) (hG := hG) := by
  intro cfgp cv xs
  have hi1 : 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) < (0 + 1 + 1 + 1 : Nat) := by word
  have hi2 : 0 ≤ sint.Z (W64 2) ∧ sint.Z (W64 2) < (0 + 1 + 1 + 1 : Nat) := by word
  wp_start as ⟨#Hvars, #Hcfg, #Hxs, #Hctx⟩
  ihave %Hcnn := typedPointsto_not_null _ _ _ $$ Hcfg
  wp_auto
  wp_if_destruct
  · exact absurd rfl Hcnn
  ipersist cfg
  ihave #Hcf := Hcfg
  iStructNamedPrefix Hcf "F"
  ihave #Hpctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  wp_auto
  wp_join iprop(∃ tc : google_golang_org.grpc.credentials.TransportCredentials, creds_ptr ↦ tc)
    with [creds] as ⟨%tc, creds⟩
  · wp_apply wp_NewTransportCredential as %tc' -
    wp_join_done
  -- the token/user exclusion check: its condition (`&&`, `||`) to a value, once
  wp_join (Q := fun v => iprop(⌜v = #(Bool.and (!decide (cv.Token' = go!""))
      (Bool.or (!decide (cv.Username' = go!"")) (!decide (cv.Password' = go!""))))⌝))
    at (App (Val (GoInstruction (Convert go.untypedBool go.bool))) _)
  · wp_if_destruct
    all_goals (try wp_auto)
    all_goals (try wp_if_destruct)
    all_goals (try wp_auto)
    all_goals (ipureintro; simp_all)
  rename_i v
  iintro %Hv
  subst Hv
  iunfold newClientVars at Hvars
  icases Hvars with ⟨⟨%eME, #HeME, #HeMEs⟩, ⟨%eNE, #HeNE, #HeNEs⟩, ⟨%dsl, #Hdsl⟩, ⟨%oW, #HoW⟩,
    ⟨%oS, #HoS⟩, ⟨%oR, #HoR⟩⟩
  generalize hb : Bool.and (!decide (cv.Token' = go!""))
      (Bool.or (!decide (cv.Username' = go!"")) (!decide (cv.Password' = go!""))) = b
  cases b
  rotate_left
  · -- a token with a user name or password: `ErrMutuallyExclusiveCfg`
    wp_auto
    iapply HΦ
    iright
    isplitr
    · ipureintro; rfl
    iexists eME
    iframe #
    isplitr
    · ipureintro; rfl
    unfold newClientErr
    ileft
    iframe #
    ipureintro
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hb
    exact hb
  wp_apply wp_TODO
  wp_join iprop(∃ bc : _root_.Perennial.context.Context, baseCtx_ptr ↦ bc ∗ withCancelOk bc)
    at (if: _ then _ else _) with [baseCtx] as ⟨%bc, baseCtx, #HWC⟩
  · iunfold cfgCtxOk at Hctx
    icases Hctx with (%Hn | ⟨%ci, %s, %Hci, #Hci⟩)
    · -- no `Context` in the configuration: `TODO()`'s
      rw [Hn]
      wp_auto
      wp_join_done
      iexists _
      iframe
      unfold withCancelOk
      iexists ∅, none
      iintro !> %Φ' #Hp HΦ'
      wp_apply wp_WithCancelTODO as %ctx' %γ' %cancel ⟨#Hcan, #Hc'⟩
      iapply HΦ'
      iframe #
    · -- the configuration's
      rw [Hci]
      wp_auto
      wp_join_done
      iexists _
      iframe
      unfold withCancelOk
      iexists s.Values, s.Deadline
      iintro !> %Φ' #Hp HΦ'
      wp_apply context.wp_WithCancel_any ci s as %ctx' %γ' %cancel ⟨#Hcan, #Hc'⟩
      · iframe #
      iapply HΦ'
      iframe #
  iunfold withCancelOk at HWC
  icases HWC with ⟨%cvs, %cdl, #HWC⟩
  wp_apply HWC as %ctx' %γ' %cancel ⟨#Hcan, #Hctx'⟩
  -- the logger: the configuration's, or built
  wp_join iprop(∃ (lg : Loc) (err : GoInterface), lg_ptr ↦ lg ∗ err_ptr ↦ err ∗
      ((⌜err = GoInterface.nil⌝ ∗ ⌜lg ≠ null⌝) ∨
        (∃ e : GoInterfaceOk, ⌜err = GoInterface.ok e⌝ ∗ errorStringSpec e ∗ ⌜cv.Logger' = null⌝)))
    with [lg err] as ⟨%lg, %err, lg, err, Hlgerr⟩
  · -- none in the configuration
    wp_if_destruct
    · -- no `LogConfig`: the default logger, named
      wp_apply wp_ClientLogLevel as %lv -
      wp_apply wp_CreateDefaultZapLogger as %lg0 %err0 Hle
      wp_if_destruct
      · wp_join_done
        iexists _, _
        iframe
        icases Hle with (⟨%He, %Hn⟩ | ⟨%e, %He, #Hes⟩)
        · exact absurd rfl Hn
        iright
        iexists e
        iframe #
        ipureintro; exact ⟨He, ‹_›⟩
      · wp_apply wp_Named lg0 _ Hif as %l %Hl
        wp_join_done
        iexists _, _
        iframe
        icases Hle with (⟨%He, %Hn⟩ | ⟨%e, %He, #Hes⟩)
        · ileft
          ipureintro; exact ⟨He, Hl⟩
        iright
        iexists e
        iframe #
        ipureintro; exact ⟨He, ‹_›⟩
    · -- `LogConfig.Build()`
      wp_apply wp_Build as %lg0 %err0 Hle
      wp_join_done
      iexists _, _
      iframe
      icases Hle with (⟨%He, %Hn⟩ | ⟨%e, %He, #Hes⟩)
      · ileft
        ipureintro; exact ⟨He, Hn⟩
      iright
      iexists e
      iframe #
      ipureintro; exact ⟨He, ‹_›⟩
  · -- the configuration's
    iexists _, _
    iframe
    ileft
    ipureintro; exact ⟨rfl, Hif⟩
  icases Hlgerr with (⟨%He, %Hlgnn⟩ | ⟨%e, %He, #Hes, %HnoLg⟩)
  rotate_left
  · -- the logger's construction failed
    subst He
    wp_auto
    iapply HΦ
    iright
    isplitr
    · ipureintro; rfl
    iexists e
    iframe #
    isplitr
    · ipureintro; rfl
    unfold newClientErr
    iright; ileft
    ipureintro; exact HnoLg
  subst He
  wp_auto
  ipersist client
  ihave %Hcl := typedPointsto_not_null _ _ _ $$ «$r0»
  iStructNamedPrefix «$r0» "C"
  ihave Hlg0 : sync.atomic.ownPointer (hG := hG) (T' := go_uber_org.zap.Logger)
      (clientLgAddr «$r0_ptr») (DFrac.own 1) null $$ [Clg]
  · rw [sync.atomic.ownPointer_unseal]; unfold sync.atomic.ownPointerDef; iexact Clg
  wp_bind (App (Val #(methods _ _ _)) (Val _))
  iapply (sync.atomic.Pointer.wp_Store (T' := go_uber_org.zap.Logger) go_uber_org.zap.Logger.ty
    (clientLgAddr «$r0_ptr») lg)
  · iPkgInit
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists null
  iframe Hlg0
  iintro Hlg1
  imod Hmask with -
  imod isClientLogger_alloc' «$r0_ptr» lg Hlgnn $$ Hlg1 with #HcLg
  imodintro
  wp_auto
  -- the user name and password
  wp_join iprop(∃ (u p : GoString)
      (a : _root_.Perennial.go_etcd_io.etcd.client.v3.credentials.PerRPCCredentialsBundle),
      structFieldRef go_etcd_io.etcd.client.v3.Client go!"Username" «$r0_ptr» ↦ u ∗
      structFieldRef go_etcd_io.etcd.client.v3.Client go!"Password" «$r0_ptr» ↦ p ∗
      structFieldRef go_etcd_io.etcd.client.v3.Client go!"authTokenBundle" «$r0_ptr» ↦ a) at next
    with [CUsername CPassword CauthTokenBundle] as ⟨%u0, %p0, %a0, CUsername, CPassword, CauthTokenBundle⟩
  · wp_if_destruct
    all_goals (try wp_auto)
    all_goals (try wp_if_destruct)
    all_goals (try wp_auto)
    all_goals (try (wp_apply wp_NewPerRPCCredentialBundle as %b %Hb))
    all_goals (try wp_auto)
    all_goals (try wp_join_done)
    all_goals (iexists _, _, _; iframe)
  -- the token: a bundle with it
  wp_join iprop(∃ (t : GoString)
      (a : _root_.Perennial.go_etcd_io.etcd.client.v3.credentials.PerRPCCredentialsBundle),
      structFieldRef go_etcd_io.etcd.client.v3.Client go!"Token" «$r0_ptr» ↦ t ∗
      structFieldRef go_etcd_io.etcd.client.v3.Client go!"authTokenBundle" «$r0_ptr» ↦ a ∗
      ⌜t = cv.Token'⌝ ∗ ⌜t ≠ go!"" → a ≠ GoInterface.nil⌝) at next
    with [CToken CauthTokenBundle] as ⟨%t0, %a1, CToken, CauthTokenBundle, %Ht0, %Hta⟩
  · wp_if_destruct
    · try wp_auto
      try wp_join_done
      iexists _, _
      iframe
      ipureintro
      exact ⟨Hif.symm, fun h => absurd rfl h⟩
    · try wp_auto
      wp_apply wp_NewPerRPCCredentialBundle as %b %Hb
      try wp_auto
      try wp_join_done
      iexists _, _
      iframe
      ipureintro
      exact ⟨rfl, fun _ => Hb⟩
  -- the message size limits: a size error, or the call options
  wp_join (Q := fun v => iprop(
      (⌜v = executeVal⌝ ∗ ∃ co : GoSlice,
        structFieldRef go_etcd_io.etcd.client.v3.Client go!"callOpts" «$r0_ptr» ↦ co) ∨
      (∃ e : GoInterfaceOk, ⌜v = returnVal (PairV #null #(GoInterface.ok e))⌝ ∗ errorStringSpec e ∗
        ⌜0 < sint.Z cv.MaxCallRecvMsgSize' ∧
          sint.Z cv.MaxCallRecvMsgSize' < sint.Z cv.MaxCallSendMsgSize'⌝)))
    at (if: _ then _ else _) with [CcallOpts]
  · by_cases hS : sint.Z (W64 0) < sint.Z cv.MaxCallSendMsgSize' <;>
    by_cases hR : sint.Z (W64 0) < sint.Z cv.MaxCallRecvMsgSize' <;>
    by_cases hRS : sint.Z cv.MaxCallRecvMsgSize' < sint.Z cv.MaxCallSendMsgSize'
    all_goals (repeat (first | wp_auto |
      simp only [hS, hR, hRS, decide_true, decide_false, Bool.not_true, Bool.not_false] |
      wp_apply wp_MaxCallSendMsgSize as %o1 - | wp_apply wp_MaxCallRecvMsgSize as %o2 -))
    · -- the receive limit below the send limit: the size error
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, -⟩
      wp_apply wp_Errorf $$ [$Hsl] as %e ⟨-, #HeS⟩
      · fmt_args_ok
      iright
      iexists e
      isplitr
      · ipureintro; rfl
      isplitr
      · rw [show errorStringSpec e = EtcdGrove.fmt.stringMethodSpec e go!"Error" from rfl]
        iexact HeS
      ipureintro
      refine ⟨by word, ?_⟩
      first | trivial | exact hRS
    · -- the call options, with the configured limits
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, Hslc⟩
      repeat (first | wp_auto |
        rw [decide_eq_true hS] | rw [decide_eq_false hS] | rw [decide_eq_true hR] |
        rw [decide_eq_false hR] |
        wp_apply wp_MaxCallSendMsgSize as %o1 - | wp_apply wp_MaxCallRecvMsgSize as %o2 - |
        (wp_apply wp_store_slice_index $$ [Hsl] as Hsl
         iframe; ipureintro
         simp only [go.arrayLiteralSize, List.length_cons, List.length_nil, List.length_set]
         first | exact hi1 | exact hi2))
      ileft
      isplitr
      · ipureintro; trivial
      iexists _
      iexact CcallOpts
    · -- the call options, with the configured limits
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, Hslc⟩
      repeat (first | wp_auto |
        rw [decide_eq_true hS] | rw [decide_eq_false hS] | rw [decide_eq_true hR] |
        rw [decide_eq_false hR] |
        wp_apply wp_MaxCallSendMsgSize as %o1 - | wp_apply wp_MaxCallRecvMsgSize as %o2 - |
        (wp_apply wp_store_slice_index $$ [Hsl] as Hsl
         iframe; ipureintro
         simp only [go.arrayLiteralSize, List.length_cons, List.length_nil, List.length_set]
         first | exact hi1 | exact hi2))
      ileft
      isplitr
      · ipureintro; trivial
      iexists _
      iexact CcallOpts
    · -- the call options, with the configured limits
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, Hslc⟩
      repeat (first | wp_auto |
        rw [decide_eq_true hS] | rw [decide_eq_false hS] | rw [decide_eq_true hR] |
        rw [decide_eq_false hR] |
        wp_apply wp_MaxCallSendMsgSize as %o1 - | wp_apply wp_MaxCallRecvMsgSize as %o2 - |
        (wp_apply wp_store_slice_index $$ [Hsl] as Hsl
         iframe; ipureintro
         simp only [go.arrayLiteralSize, List.length_cons, List.length_nil, List.length_set]
         first | exact hi1 | exact hi2))
      ileft
      isplitr
      · ipureintro; trivial
      iexists _
      iexact CcallOpts
    · -- the receive limit below the send limit: the size error
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, -⟩
      wp_apply wp_Errorf $$ [$Hsl] as %e ⟨-, #HeS⟩
      · fmt_args_ok
      iright
      iexists e
      isplitr
      · ipureintro; rfl
      isplitr
      · rw [show errorStringSpec e = EtcdGrove.fmt.stringMethodSpec e go!"Error" from rfl]
        iexact HeS
      ipureintro
      refine ⟨by word, ?_⟩
      first | trivial | exact hRS
    · -- the call options, with the configured limits
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, Hslc⟩
      repeat (first | wp_auto |
        rw [decide_eq_true hS] | rw [decide_eq_false hS] | rw [decide_eq_true hR] |
        rw [decide_eq_false hR] |
        wp_apply wp_MaxCallSendMsgSize as %o1 - | wp_apply wp_MaxCallRecvMsgSize as %o2 - |
        (wp_apply wp_store_slice_index $$ [Hsl] as Hsl
         iframe; ipureintro
         simp only [go.arrayLiteralSize, List.length_cons, List.length_nil, List.length_set]
         first | exact hi1 | exact hi2))
      ileft
      isplitr
      · ipureintro; trivial
      iexists _
      iexact CcallOpts
    · -- no limit configured: the default call options
      ileft
      isplitr
      · itrivial
      iexists _
      iexact CcallOpts
    · -- no limit configured: the default call options
      ileft
      isplitr
      · itrivial
      iexists _
      iexact CcallOpts

  rename_i v
  iintro (⟨%Hv, %co, CcallOpts⟩ | ⟨%e, %Hv, #Hes, %Hsz⟩)
  rotate_left
  · -- the size error
    subst Hv
    wp_auto
    iapply HΦ
    iright
    isplitr
    · ipureintro; rfl
    iexists e
    iframe #
    isplitr
    · ipureintro; rfl
    unfold newClientErr
    iright; iright; ileft
    ipureintro; exact Hsz
  subst Hv
  wp_auto
  wp_apply wp_resolverNew as %r -
  · iframe #
  ihave %Hxlen := ownSlice_len _ _ _ $$ Hxs
  wp_if_destruct
  · -- no endpoints
    iunfold context.cancelSpec at Hcan
    wp_apply Hcan as -
    · imodintro; itrivial
    wp_apply errors.wp_New as %e ⟨%Hpe, #He⟩
    iapply HΦ
    iright
    isplitr
    · ipureintro; rfl
    iexists e
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply go_etcd_io.etcd.cache.v3.errorStringSpec_of_msg $$ He
    unfold newClientErr
    iright; iright; iright; ileft
    ipureintro
    apply List.eq_nil_of_length_eq_zero
    word
  ipersist CepMu
  ipersist Cresolver
  wp_apply wp_SetEndpoints «$r0_ptr» «$v5_ptr» r slice.nil cv.Endpoints' xs $$ [Cendpoints]
  · iframe
    iframe #
  -- the dial: the fields read from here on are fixed
  ipersist Ccfg
  ipersist Ccreds
  ipersist Cctx
  ipersist Ccancel
  ipersist CUsername
  ipersist CPassword
  ipersist CToken
  ipersist CauthTokenBundle
  ipersist CcallOpts
  ihave #Hfix : clientFixed «$r0_ptr» { (zero_val go_etcd_io.etcd.client.v3.Client) with
      cfg' := cv, creds' := tc, resolver' := r, epMu' := «$v5_ptr», ctx' := GoInterface.ok ctx',
      cancel' := cancel, Username' := u0, Password' := p0, Token' := t0, authTokenBundle' := a1,
      callOpts' := co } $$ []
  · unfold clientFixed
    simp only
    iframe #
    ipureintro
    exact ⟨Hcl, Hta⟩
  ihave #Hdial : clientDialAt «$r0_ptr» $$ []
  · unfold clientDialAt
    iexists _
    iexact Hfix
  wp_apply wp_dialWithBalancer «$r0_ptr» $$ [] as %conn %derr Hderr
  · iframe #
  icases Hderr with (%Hdn | ⟨%de, %Hde, #Hdes⟩)
  rotate_left
  · -- the dial failed: its error, wrapped with the endpoints (the PR's first change)
    subst Hde
    wp_auto
    iunfold context.cancelSpec at Hcan
    wp_apply Hcan as -
    · imodintro; itrivial
    wp_apply wp_resolverClose
    wp_apply _root_.Perennial.strings.wp_Join $$ [Hxs] as -
    · iframe #
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    rw [show sint.nat (W64 (0 + 1)) = 1 by rfl]
    simp only [List.set_cons_succ, List.set_cons_zero]
    have hfmt : fmt.fmtSW go!"etcdclient: dialing [%s] failed: %w" :=
      ⟨go!"etcdclient: dialing [", go!"] failed: ", go!"", by rfl, by decide, by decide, by decide⟩
    wp_apply (wp_ErrorfWrap _ _ de _ _ hfmt) $$ [$Hsl] as %e ⟨-, #HeS, #Hw⟩
    · rw [show EtcdGrove.fmt.stringMethodSpec de go!"Error" = errorStringSpec de from rfl]
      iexact Hdes
    iapply HΦ
    iright
    isplitr
    · ipureintro; rfl
    iexists e
    isplitr
    · ipureintro; rfl
    isplitr
    · rw [show errorStringSpec e = EtcdGrove.fmt.stringMethodSpec e go!"Error" from rfl]
      iexact HeS
    unfold newClientErr
    iright; iright; iright; iright; ileft
    iexists de
    iframe #
  subst Hdn
  wp_auto
  ipersist Cconn
  ihave #Hconn : clientConnAt «$r0_ptr» $$ []
  · unfold clientConnAt
    iexists { (zero_val go_etcd_io.etcd.client.v3.Client) with
      cfg' := cv, creds' := tc, resolver' := r, epMu' := «$v5_ptr», ctx' := GoInterface.ok ctx',
      cancel' := cancel, Username' := u0, Password' := p0, Token' := t0, authTokenBundle' := a1,
      callOpts' := co, conn' := conn }
    unfold clientFixed
    simp only
    iframe #
  wp_apply wp_NewCluster «$r0_ptr» $$ [] as %vCl -
  · iframe #
  wp_apply wp_NewKV «$r0_ptr» $$ [] as %vKV -
  · iframe #
  wp_apply wp_NewLease «$r0_ptr» $$ [] as %vLe -
  · iframe #
  wp_apply wp_NewWatcher «$r0_ptr» $$ [] as %vWa -
  · iframe #
  wp_apply wp_NewAuth «$r0_ptr» $$ [] as %vAu -
  · iframe #
  wp_apply wp_NewMaintenance «$r0_ptr» $$ [] as %vMa -
  · iframe #
  ipersist CCluster
  ipersist CKV
  ipersist CLease
  ipersist CWatcher
  ipersist CAuth
  ipersist CMaintenance
  ihave #Hbuilt : clientBuiltAt «$r0_ptr» $$ []
  · unfold clientBuiltAt
    iexists { (zero_val go_etcd_io.etcd.client.v3.Client) with
      cfg' := cv, creds' := tc, resolver' := r, epMu' := «$v5_ptr», ctx' := GoInterface.ok ctx',
      cancel' := cancel, Username' := u0, Password' := p0, Token' := t0, authTokenBundle' := a1,
      callOpts' := co, conn' := conn, Cluster' := vCl, KV' := vKV, Lease' := vLe, Watcher' := vWa,
      Auth' := vAu, Maintenance' := vMa }
    unfold clientFixed
    simp only
    iframe #
  ihave #Gc := Ccfg
  iStructNamedPrefix Gc "G"
  -- the token request's context: the client's, with the dial timeout if set
  wp_join iprop(∃ (c2 : GoInterfaceOk) (cn2 : GoFunc) (vs2 : GMap GoInterface GoInterface)
      (dl2 : Option time.Time) (γ2 : context.ContextNames),
      ctx_ptr ↦ GoInterface.ok c2 ∗ cancel_ptr ↦ cn2 ∗
      context.isContext c2 { Values := vs2, Deadline := dl2, Done_gn := γ2, PDone := iprop(True) } ∗
      □ (∀ Φ : val → IProp GF, ▷ Φ #() -∗ WP (App (Val #cn2) (Val #())) {{ Φ }}))
    at (if: _ then _ else _) with [ctx cancel] as ⟨%c2, %cn2, %vs2, %dl2, %γ2, ctx, cancel, #Hc2, #Hcn2⟩
  · wp_auto
    wp_if_destruct
    · wp_apply context.wp_WithTimeout ctx' _ cv.DialTimeout' $$ [] as %c3 %γ3 %cn3 %d3 ⟨#Hcn3, #Hc3⟩
      · iframe #
      try wp_auto
      try wp_join_done
      iexists c3, cn3, cvs, (some d3), γ3
      iframe
      iframe #
      iintro !> %Φ' HΦ'
      iapply Hcn3
      · itrivial
      inext
      iintro -
      iexact HΦ'
    · isplitr
      · itrivial
      iexists ctx', _, cvs, cdl, γ'
      iframe
      iframe #
      iintro !> %Φ' HΦ'
      wp_auto
      iexact HΦ'
  -- the token request
  ihave #Hrc := retryClientOk_of_clientFixed _ _ $$ Hfix
  ihave #Hco := ctxOk_of_isContext _ _ $$ Hc2
  wp_apply wp_getToken «$r0_ptr» c2 _ $$ [] as %terr #Hterr
  · iframe #
  rcases terr with te | _
  · -- the token request failed: its error, wrapped with the endpoints (the PR's second change)
    ihave #Hterr0 := Hterr
    iunfold clientErrOk at Hterr
    icases Hterr with ⟨%Hce, #Hst⟩
    iunfold go_etcd_io.etcd.cache.v3.statusErrOk at Hst
    ihave ⟨#Htes, -⟩ := Hst $$ %te %rfl
    wp_auto
    wp_apply wp_Close «$r0_ptr» $$ [] as %cerr -
    · iframe #
    wp_apply Hcn2
    wp_apply _root_.Perennial.strings.wp_Join $$ [Hxs] as -
    · iframe #
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    rw [show sint.nat (W64 (0 + 1)) = 1 by rfl]
    simp only [List.set_cons_succ, List.set_cons_zero]
    have hfmt : fmt.fmtSW go!"etcdclient: communicating with [%s] failed: %w" :=
      ⟨go!"etcdclient: communicating with [", go!"] failed: ", go!"", by rfl, by decide, by decide,
        by decide⟩
    wp_apply (wp_ErrorfWrap _ _ te _ _ hfmt) $$ [$Hsl] as %e ⟨-, #HeS, #Hw⟩
    · rw [show EtcdGrove.fmt.stringMethodSpec te go!"Error" = errorStringSpec te from rfl]
      iexact Htes
    iapply HΦ
    iright
    isplitr
    · ipureintro; rfl
    iexists e
    isplitr
    · ipureintro; rfl
    isplitr
    · rw [show errorStringSpec e = EtcdGrove.fmt.stringMethodSpec e go!"Error" from rfl]
      iexact HeS
    unfold newClientErr
    iright; iright; iright; iright; iright; ileft
    iexists te
    iframe #
  wp_auto
  wp_apply Hcn2
  -- the version check, then the endpoint syncer
  generalize hrej : cv.RejectOldCluster' = rej
  cases rej
  rotate_left
  · wp_auto
    wp_apply wp_checkVersion «$r0_ptr» $$ [] as %cverr Hcv
    · iframe #
    icases Hcv with (%Hcvn | ⟨%ce, %Hce, #Hces⟩)
    · subst Hcvn
      wp_auto
      wp_apply wp_fork
      · wp_apply wp_autoSync «$r0_ptr» $$ []
        · iframe #
        ipureintro; exact isPanic_intoVal _
      iapply HΦ
      ileft
      iframe #
      ipureintro; rfl
    · subst Hce
      wp_auto
      wp_apply wp_Close «$r0_ptr» $$ [] as %cerr -
      · iframe #
      iapply HΦ
      iright
      isplitr
      · ipureintro; rfl
      iexists ce
      iframe #
      isplitr
      · ipureintro; rfl
      unfold newClientErr
      iright; iright; iright; iright; iright; iright
      ipureintro; exact hrej
  · wp_auto
    wp_apply wp_fork
    · wp_apply wp_autoSync «$r0_ptr» $$ []
      · iframe #
      ipureintro; exact isPanic_intoVal _
    iapply HΦ
    ileft
    iframe #
    ipureintro; rfl

end proof

end EtcdGrove
end Perennial
