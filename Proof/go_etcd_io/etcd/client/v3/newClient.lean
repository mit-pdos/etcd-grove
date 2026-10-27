/-
Proof of `Spec/go_etcd_io/etcd/client/v3/newClient.lean` (item 5, client construction).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.newClient
public import Spec.context.TODO
public import Spec.context.WithCancelTodo
public import Spec.go_etcd_io.etcd.client.v3.internal.resolver.New
public import Spec.go_etcd_io.etcd.client.v3.Client__SetEndpoints
public import Spec.go_etcd_io.etcd.client.v3.internal.resolver.EtcdManualResolver__Close
public import Spec.go_etcd_io.etcd.client.v3.Client__dialWithBalancer
public import Spec.go_etcd_io.etcd.client.v3.NewCluster
public import Spec.go_etcd_io.etcd.client.v3.NewKV
public import Spec.go_etcd_io.etcd.client.v3.NewLease
public import Spec.go_etcd_io.etcd.client.v3.NewWatcher
public import Spec.go_etcd_io.etcd.client.v3.NewAuth
public import Spec.go_etcd_io.etcd.client.v3.NewMaintenance
public import Spec.go_etcd_io.etcd.client.v3.Client__getToken
public import Spec.go_etcd_io.etcd.client.v3.Client__Close
public import Spec.go_etcd_io.etcd.client.v3.credentials.NewPerRPCCredentialBundle
public import Spec.go_etcd_io.etcd.client.v3.Client__autoSync
public import Perennial.Proof.sync
public import Perennial.Proof.context
public import Perennial.Proof.sync.RWMutexGuard

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 client

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem newClient.wp_proof
    (wp_TODO : context.TODO.spec (GF := GF) (hG := hG))
    (wp_WithCancelTodo : context.WithCancelTodo.spec (GF := GF) (hG := hG))
    (wp_resolverNew : resolver.New.spec (GF := GF) (hG := hG))
    (wp_SetEndpoints : Client.SetEndpoints.spec (GF := GF) (hG := hG))
    (wp_rClose : resolver.EtcdManualResolver.Close.spec (GF := GF) (hG := hG))
    (wp_dialWithBalancer : Client.dialWithBalancer.spec (GF := GF) (hG := hG))
    (wp_NewCluster : NewCluster.spec (GF := GF) (hG := hG))
    (wp_NewKV : NewKV.spec (GF := GF) (hG := hG))
    (wp_NewLease : NewLease.spec (GF := GF) (hG := hG))
    (wp_NewWatcher : NewWatcher.spec (GF := GF) (hG := hG))
    (wp_NewAuth : NewAuth.spec (GF := GF) (hG := hG))
    (wp_NewMaintenance : NewMaintenance.spec (GF := GF) (hG := hG))
    (wp_getToken : Client.getToken.spec (GF := GF) (hG := hG))
    (wp_autoSync : Client.autoSync.spec (GF := GF) (hG := hG))
    (wp_Close : Client.Close.spec (GF := GF) (hG := hG))
    (wp_NewBundle : credentials.NewPerRPCCredentialBundle.spec (GF := GF) (hG := hG)) :
    newClient.spec (GF := GF) (hG := hG) := by
  intro p cfg eps V
  wp_start as ⟨#Hp, #Hcfg, %HV⟩
  ihave #Hvars : (clientNewVars : IProp GF) $$ []
  · iapply clientNewVars_of_init; iPkgInit
  iunfold clientCfgOk at Hcfg
  icases Hcfg with ⟨#Heps, #Hdo, %Hc⟩
  obtain ⟨Hplain, Htls, Htok, Hctx, Hlg, Hms, Hmr, Hrej, Has⟩ := Hc
  ihave %Hpnn := typedPointsto_not_null _ _ _ $$ Hp
  ihave #Hpf := Hp
  iStructNamed Hpf
  wp_auto
  rw [decide_eq_false Hpnn]
  wp_auto
  rw [Htls]
  wp_auto
  rw [Htok, Hctx]
  wp_auto
  wp_apply wp_TODO
  wp_apply wp_WithCancelTodo as %ctx' %γ' %cancel ⟨#Hcancel, #Hctx'⟩
  ihave #Hvars0 := Hvars
  iunfold clientNewVars at Hvars
  icases Hvars with ⟨⟨%dsl, #Hdsl, #Hdslok⟩, -, -, -⟩
  wp_auto
  rw [decide_eq_false Hlg]
  wp_auto
  icases typedPointsto_not_null_dup _ _ _ $$ «$r0» with ⟨«$r0», %Hcnn⟩
  iStructNamed «$r0»
  ihave Hlgown : sync.atomic.ownPointer (hG := hG) (T' := go_uber_org.zap.Logger)
      (clientLgAddr «$r0_ptr») (DFrac.own 1) null $$ [lg]
  · rw [sync.atomic.ownPointer_unseal]; unfold sync.atomic.ownPointerDef; iexact lg
  wp_bind (App (Val #(methods _ _ _)) (Val #cfg.Logger'))
  iapply (sync.atomic.Pointer.wp_Store (T' := go_uber_org.zap.Logger) go_uber_org.zap.Logger.ty
    (clientLgAddr «$r0_ptr») cfg.Logger')
  · iPkgInit
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists null
  iframe Hlgown
  iintro Hlgown
  imod Hmask with -
  imod (inv_alloc clientLgN ⊤ iprop(∃ lg : Loc,
      sync.atomic.ownPointer (hG := hG) (T' := go_uber_org.zap.Logger) (clientLgAddr «$r0_ptr»)
        (DFrac.own 1) lg ∗ ⌜lg ≠ null⌝)) $$ [Hlgown] with #HcLg
  · inext; iexists _; iframe; ipureintro; exact Hlg
  ihave #HcLg' : isClientLogger (GF := GF) «$r0_ptr» $$ []
  · iunfold isClientLogger; iexact HcLg
  imodintro
  -- (2026-10-25, the auth plan's E2d) a user name and password: the client's token bundle
  irename : (cfg_ptr ↦ p : IProp GF) => Hcfgp
  wp_auto
  wp_join iprop(∃ (un pw : GoString) (atb : GoInterface),
      cfg_ptr ↦ p ∗ client_ptr ↦ «$r0_ptr» ∗
      clientF «$r0_ptr» go!"Username" ↦ un ∗ clientF «$r0_ptr» go!"Password" ↦ pw ∗
      clientF «$r0_ptr» go!"authTokenBundle" ↦ atb ∗ tokenBundleOk atb)
    at next with [Hcfgp client Username Password authTokenBundle]
    as ⟨%un, %pw, %atb, Hcfgp, client, Username, Password, authTokenBundle, #Htb⟩
  · by_cases hu : cfg.Username' = []
    · rw [decide_eq_true hu]
      wp_auto
      wp_join_done
      iexists _, _, GoInterface.nil
      iframe
      iunfold tokenBundleOk
      ileft; ipureintro; rfl
    rw [decide_eq_false hu]
    wp_auto
    by_cases hp : cfg.Password' = []
    · rw [decide_eq_true hp]
      wp_auto
      wp_join_done
      iexists _, _, GoInterface.nil
      iframe
      iunfold tokenBundleOk
      ileft; ipureintro; rfl
    rw [decide_eq_false hp]
    wp_auto
    wp_apply wp_NewBundle $$ [] as %atb #Hb
    (try wp_auto)
    wp_join_done
    iexists _, _, atb
    iframe
    iunfold tokenBundleOk
    iright; iexact Hb
  rw [decide_eq_false (show ¬ (sint.Z (W64 0) < sint.Z cfg.MaxCallSendMsgSize') by
    have : sint.Z (W64 0) = 0 := by decide
    word)]
  wp_auto
  rw [decide_eq_false (show ¬ (sint.Z (W64 0) < sint.Z cfg.MaxCallRecvMsgSize') by
    have : sint.Z (W64 0) = 0 := by decide
    word)]
  wp_auto
  ihave %Hel := ownSlice_len _ _ _ $$ Heps
  wp_apply wp_resolverNew _ eps $$ [$Heps] as %r ⟨%Hrnn, Hro⟩
  rw [decide_eq_false (show ¬ (sint.Z cfg.Endpoints'.len < sint.Z (W64 1)) by
    have : sint.Z (W64 1) = 1 := by decide
    have hne : eps.length ≠ 0 := fun h => Hplain.1 (List.eq_nil_of_length_eq_zero h)
    obtain ⟨h1, h2⟩ := Hel
    rw [h1] at hne
    unfold sint.nat at hne
    word)]
  wp_auto
  ipersist resolver
  ipersist epMu
  ipersist cfg
  ipersist creds
  ipersist Username
  ipersist Token
  ipersist authTokenBundle
  ipersist callOpts
  imod (sync.init_RWMutex (fun _ => iprop(True)) «$v5_ptr» (E := ⊤)) $$ [] «$v5» with Hslots
  · inext; itrivial
  icases sync.ownRWMutex_slots_guard _ _ $$ Hslots with ⟨-, #Hguard⟩
  wp_apply wp_SetEndpoints «$r0_ptr» «$v5_ptr» r slice.nil eps cfg.Endpoints' eps
    $$ [$epMu $Hguard $endpoints $resolver $Hro $Heps] as ⟨endpoints, Hro⟩
  ipersist endpoints
  ihave #Hrc : retryClientOk (GF := GF) «$r0_ptr» $$ []
  · iunfold retryClientOk
    isplitr
    · ipureintro; exact Hcnn
    iframe HcLg'
    iexists [], atb
    iframe Token authTokenBundle
    ipureintro; intro h; exact absurd rfl h
  ihave #HDOpt : p.[go_etcd_io.etcd.client.v3.Config, go!"DialOptions"] ↦□ cfg.DialOptions' $$ []
  · iexact DialOptions
  wp_apply wp_dialWithBalancer «$r0_ptr» cfg GoInterface.nil r cfg.Endpoints' eps atb
    $$ [$Hrc $cfg $Hdo $authTokenBundle $Htb $creds $endpoints $Heps $resolver $Hro]
    as %conn %derr Hres
  · ipureintro; exact Hplain
  icases Hres with (⟨%Hderr, #Hconn⟩ | %Hderr)
  · subst Hderr
    wp_auto
    ipersist conn
    iunfold isEtcdConn at Hconn
    icases Hconn with ⟨%ic, #Hgc, #Hic, #HicW⟩
    ihave #Hcore : clientCoreAt (GF := GF) «$r0_ptr» $$ []
    · iunfold clientCoreAt
      iframe HcLg'
      isplitr
      · ipureintro; exact Hcnn
      isplitr
      · iexists _; iexact conn
      isplitr
      · iexists _; iexact callOpts
      iexists _; iexact cfg
    ihave #Hkv : clientKVAt (GF := GF) «$r0_ptr» eps $$ []
    · iunfold clientKVAt
      isplitr
      · ipureintro; exact Hcnn
      iexists conn, dsl
      iframe conn callOpts Hdslok
      iunfold isEtcdConn
      iexists ic
      iframe Hgc Hic HicW
    wp_apply wp_NewCluster «$r0_ptr» $$ [$Hcore] as %vc -
    wp_apply wp_NewKV «$r0_ptr» eps $$ [$Hkv] as %vkv ⟨%api, %Hvkv, #Hapi⟩
    wp_apply wp_NewLease «$r0_ptr» eps $$ [$Hcore $Hkv] as %vl ⟨%lp, %Hvl, #Hlp⟩
    iunfold callOptsAt at Hdslok
    icases Hdslok with ⟨%cvs, #Hcvs, -, #Hcvok, -⟩
    have Htb := HV
    wp_apply wp_NewWatcher { V with conn := conn, ics := [ic] } «$r0_ptr» dsl cvs
      $$ [$Hpkg2 $conn $callOpts $Hcvs $Hcvok $HcLg'] as %wi ⟨%w, %wc, %wlg, %Hwi, #Hcw⟩
    · isplitr
      · ipureintro; exact Hcnn
      ipureintro; exact Htb
    wp_apply wp_NewAuth «$r0_ptr» eps $$ [$Hkv] as %va ⟨%ap, %Hva, #Hap⟩
    wp_apply wp_NewMaintenance «$r0_ptr» $$ [$Hcore] as %vm -
    ipersist KV
    ipersist Watcher
    ipersist Lease
    ipersist Auth
    ihave #Hcfgf := cfg
    iStructNamed Hcfgf
    wp_auto
    wp_join iprop(∃ (cx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (cf : GoFunc),
        client_ptr ↦ «$r0_ptr» ∗ ctx_ptr ↦ GoInterface.ok cx ∗ cancel_ptr ↦ cf ∗
        context.isContext cx cd ∗
        □ (∀ Φ : val → IProp GF, ▷ Φ #() -∗ WP (App (Val #cf) (Val #())) {{ Φ }}))
      with [client ctx cancel] as ⟨%cx, %cd, %cf, client, ctx, cancel, #Hcx, #Hcf⟩
    · wp_apply context.wp_WithTimeout ctx' _ cfg.DialTimeout' $$ [$Hctx']
        as %cx2 %γ2 %cf2 %dl ⟨#Hcf2, #Hcx2⟩
      wp_join_done
      iexists cx2, _, cf2
      iframe client ctx cancel Hcx2
      iintro !> %Φ' HΦ'
      iapply Hcf2 $$ [] [HΦ']
      · itrivial
      inext; iintro -; iexact HΦ'
    · iexists ctx', _, _
      iframe client ctx cancel Hctx'
      iintro !> %Φ' HΦ'
      wp_auto
      iexact HΦ'
    wp_apply wp_getToken «$r0_ptr» cx cd $$ [$Hrc] as %terr ⟨-, -⟩
    · iapply ctxOk_of_isContext; iexact Hcx
    -- (E2d) the token's fetch failed (a client with a user name): the client closed, an error
    cases terr with
    | ok e =>
      wp_auto
      wp_apply wp_Close «$r0_ptr» $$ [$Hcore] as %cerr -
      wp_bind (App (Val #cf) (Val #()))
      iapply Hcf
      inext
      wp_auto
      iapply HΦ
      iright
      ipureintro; exact ⟨by simp, rfl⟩
    | nil =>
    wp_auto
    wp_bind (App (Val #cf) (Val #()))
    iapply Hcf
    inext
    wp_auto
    rw [Hrej]
    wp_auto
    wp_apply wp_fork $$ []
    · wp_apply wp_autoSync «$r0_ptr» cfg $$ [$cfg]
      · ipureintro; exact Has
      itrivial
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iunfold isNewClient
    iframe Hkv Hrc
    isplitl []
    · iexists api
      subst Hvkv
      iframe KV Hapi
    isplitl []
    · iexists w, conn, wc, wlg, [ic]
      subst Hwi
      iframe Watcher Hgc Hcw
    isplitl []
    · iexists lp
      subst Hvl
      iframe Lease Hlp
    iexists ap
    subst Hva
    iframe Auth Hap
  · cases derr with
    | nil => exact absurd rfl Hderr
    | ok e =>
      wp_auto
      ihave #Hcs := Hcancel
      iunfold context.cancelSpec at Hcs
      wp_bind (App (Val #cancel) (Val #()))
      iapply Hcs
      · itrivial
      inext
      iintro -
      wp_auto
      wp_apply wp_rClose r
      iapply HΦ
      iright
      try (ipureintro; exact ⟨Hderr, rfl⟩)

end proof

end EtcdGrove
end Perennial
