/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/NewKV.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.NewKV
public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__Close
public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__monitorSession
public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__waitSession
public import Spec.go_etcd_io.etcd.client.v3.leasing.leaseCache__clearOldRevokes
public import Spec.go_etcd_io.etcd.client.v3.Client__Ctx
public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeasingNewLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasing

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

theorem NewKV.wp_proof
    (hCtx : EtcdGrove.Client.Ctx.spec (GF := GF) (hG := hG))
    (hMS : leasingKV.monitorSession.spec (GF := GF) (hG := hG))
    (hCOR : leaseCache.clearOldRevokes.spec (GF := GF) (hG := hG))
    (hClose : leasingKV.Close.spec (GF := GF) (hG := hG))
    (hWS : leasingKV.waitSession.spec (GF := GF) (hG := hG)) :
    NewKV.spec (GF := GF) (hG := hG) := by
  intro cl pfx osl
  wp_start as ⟨#Hcci, #Hcl, %Hpre⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hctxp : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Hv3 : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Hcl' := Hcl
  iunfold isLeasingEtcdClient at Hcl'
  icases Hcl' with ⟨%kv, %cctx, %ccs, #HKV, #HDo, #HTxn, #HLC, #Hcctxf, #Hcctx, #Hccc⟩
  ihave #HLC' := HLC
  iunfold isLeasingClient at HLC'
  icases HLC' with ⟨#HKVf, -⟩
  (try wp_auto)
  wp_apply hCtx cl (GoInterface.ok cctx) $$ [$Hv3 $Hcctxf]
  wp_apply context.wp_WithCancel iprop(True) cctx ccs $$ [$Hctxp $Hcctx $Hccc]
    as %ictx %γi %cancel ⟨#Hcancel, #Hictx, #Hicc⟩
  ihave #Hcancel' := context.cancel_spec_forget _ _ _ $$ Hcancel
  (try wp_auto)
  wp_apply (wp_map_make1 (K := GoString) (V := time.Time) go.string time.Time.ty) as %rm Hrm
  (try wp_auto)
  wp_apply chan.wp_make1 (V := Unit) as %sc %γsc ⟨#Hsc, %_, Hsoc⟩
  (try wp_auto)
  iStructNamedPrefix «$r0» "C"
  iStructNamedPrefix Cleases "L"
  -- the ghost state
  imod ghostVar_alloc (GF := GF) (leaseCacheSt0 rm) with ⟨%γst, Hst⟩
  imod mono_nat_own_alloc (GF := GF) 0 with ⟨%γready, Hready, -⟩
  imod mono_list_own_alloc (GF := GF) ([] : List (GoString × Loc)) with ⟨%γinst, Hinst, -⟩
  imod mono_list_own_alloc (GF := GF) [leaseCacheSt0 rm] with ⟨%γlog, Hlog, -⟩
  imod mono_nat_own_alloc (GF := GF) 0 with ⟨%γsess, Hsess, -⟩
  imod sync.init_WaitGroup leasingWgWGN (lkvWg «$r0_ptr») $$ Cwg
    with ⟨%γwg, #HisWg, Hwgo, Hwaiters⟩
  imod ownTokAuth_alloc (GF := GF) with ⟨%γwr, Hwra⟩
  imod ownTokAuth_alloc (GF := GF) with ⟨%γwo, Hwoa⟩
  imod ownTokAuth_alloc (GF := GF) with ⟨%γwc, Hwca⟩
  imod ownTokAuth_add leasingWgOwedMax γwc 0 $$ Hwca with ⟨Hwca, Hcaps⟩
  imod ownToks_0 (GF := GF) γwc with Hcap0
  ihave Htk0 : threadToks (GF := GF) 0 $$ []
  · iapply threadToks_zero
  imod ghostVar_alloc (GF := GF) () with ⟨%γop, Hop⟩
  obtain ⟨γ, hγ⟩ : ∃ γ : LeasingNames, γ = ⟨⟨γst, γready, γinst⟩, γsess, γlog, γwg, γwr, γwo, γwc,
      γop⟩ := ⟨_, rfl⟩
  -- `sessionc`, a broadcast channel announcing `sessionReadyQ γ`
  imod alloc_broadcast_chan (sessionReadyQ γ) γsc sc $$ Hsc Hsoc with Hpend
  icases ownBroadcastChan_open _ _ _ _ $$ Hpend with ⟨%γch, #Hint, Hown⟩
  ihave #Hscunk : ownBroadcastChan sc γsc (sessionReadyQ γ) .Unknown $$ []
  · iapply ownBroadcastChan_close _ _ _ _ γch
    iframe #
  ihave Hpend : ownBroadcastChan sc γsc (sessionReadyQ γ) .Pending $$ [Hown]
  · iapply ownBroadcastChan_close _ _ _ _ γch
    iframe #
    iexact Hown
  -- `session` and `sessionc`, halves
  icases ((fractional_of_dfractional (fun dq => typedPointsto (GF := GF)
      (structFieldRef leasingKV go!"session" «$r0_ptr») (null : Loc) dq)).fractional
      (1 : Qp).half (1 : Qp).half).1 $$ [Csession] with ⟨Hs1, Hs2⟩
  · rw [Qp.half_add_half]; iexact Csession
  icases ((fractional_of_dfractional (fun dq => typedPointsto (GF := GF)
      (structFieldRef leasingKV go!"sessionc" «$r0_ptr») sc dq)).fractional
      (1 : Qp).half (1 : Qp).half).1 $$ [Csessionc] with ⟨Hsc1, Hsc2⟩
  · rw [Qp.half_add_half]; iexact Csessionc
  -- the lease cache
  imod leasingCache_init «$r0_ptr» γ pfx rm sc $$ [Hcci Lmu Lentries Lrevokes Hrm Lheader Hst Hready Hinst
    Hs1 Hsc1 Hlog Hsess] with ⟨#Hcache, Hrds⟩
  · subst hγ
    iframe
    iframe #
    unfold sessioncOk
    iexists γsc
    iexact Hscunk
  -- the wait group's counter invariant
  have hwg : γ.wg = γwg := by subst hγ; rfl
  rw [← hwg]
  imod inv_alloc leasingWgN ⊤ (leasingWgInv (GF := GF) γ)
    $$ [Hwgo Hwaiters Hwra Htk0 Hwoa Hcap0 Hwca] with #HwgInv
  · inext
    subst hγ
    unfold leasingWgInv
    iexists W32 0, 0, 0, 0
    rw [show sint.nat (W32 0) = 0 from rfl]
    iframe
    isplitr
    · ipureintro; decide
    isplitr
    · ipureintro; rfl
    ileft; ipureintro; rfl
  ihave Hcaps : ownToks γ.wc 2 $$ [Hcaps]
  · subst hγ; unfold leasingWgOwedMax; iexact Hcaps
  ihave Hop : leasingOpen γ 1 $$ [Hop]
  · subst hγ; unfold leasingOpen; iexact Hop
  ipersist Ccl
  ipersist Ckv
  ipersist Cpfx
  ipersist Cctx
  ipersist Ccancel
  ipersist CsessionOpts
  ipersist lkv
  ipersist cctx
  ihave #Hlkv : isLeasingKV «$r0_ptr» γ pfx $$ []
  · unfold isLeasingKV
    iexists cl, kv, ictx, _, cancel, osl
    isplitr
    · ipureintro; exact Hpre.1
    iframe #
    ipureintro; exact Hpre.2
  ihave #Hcanc : isLeasingCancel «$r0_ptr» $$ []
  · unfold isLeasingCancel concurrency.cancelSpec
    iexists cancel
    iframe #
  -- `lkv.wg.Add(2)`
  wp_apply wp_leasingWg_Add2 «$r0_ptr» γ 1 Hpre.2 $$ [$Hsync $HisWg $HwgInv $Hcaps $Hop]
    as ⟨H2, Hop⟩
  icases ownToks_add_1 1 1 γ.wo $$ H2 with ⟨Hr1, Hr2⟩
  -- the session monitor
  wp_apply wp_fork_tok_body $$ [Hr1 Hs2 Hsc2 Hpend]
  · iintro Htok
    wp_apply wp_with_defer as %defer defer
    (try wp_auto)
    wp_apply hMS «$r0_ptr» γ pfx $$ [$Hpkg $Hlkv Hs2 Hsc2 Hpend]
    · unfold sessionMonitor
      iexists null, sc, γsc, false
      simp only [Bool.false_eq_true, ↓reduceIte]
      iframe
      imodintro
      unfold sessionOk
      simp only [↓reduceIte]
      itrivial
    (try wp_auto)
    wp_apply wp_leasingWg_DoneOwed «$r0_ptr» γ $$ [$Hsync $HisWg $HwgInv Hr1] as -
    · unfold leasingWgRunningOwed; iexact Hr1
    (try wp_auto)
    iexact Htok
  -- `clearOldRevokes`
  wp_apply wp_fork_tok_body $$ [Hr2]
  · iintro Htok
    wp_apply wp_with_defer as %defer defer
    (try wp_auto)
    wp_apply hCOR (lkvLeases «$r0_ptr») γ.lc pfx (leasingX «$r0_ptr» γ) ictx _
      $$ [$Hpkg $Hcache $Hictx]
    · imodintro
      iintro %st %rv %_ HX
      imod leasingX_step «$r0_ptr» γ st { st with revokes := rv } $$ HX with ⟨HX, -⟩
      imodintro
      iexact HX
    (try wp_auto)
    wp_apply wp_leasingWg_DoneOwed «$r0_ptr» γ $$ [$Hsync $HisWg $HwgInv Hr2] as -
    · unfold leasingWgRunningOwed; iexact Hr2
    (try wp_auto)
    iexact Htok
  (try wp_auto)
  -- `lkv.waitSession(cctx)`, with a reader slot lent
  obtain ⟨n, hn⟩ : ∃ n, leasingMaxReaders = n + 1 :=
    ⟨leasingMaxReaders - 1, by
      unfold leasingMaxReaders; rw [sync.rwmutex.actualMaxReaders_unseal]; decide⟩
  rw [hn, List.replicate_succ]
  icases BigSepL.bigSepL_cons.1 $$ Hrds with ⟨Hr, Hrds⟩
  wp_apply hWS «$r0_ptr» γ pfx ictx _ $$ [$Hpkg $Hlkv $Hr $Hictx] as %err ⟨Hr, Herr⟩
  (try wp_auto)
  iapply HΦ
  unfold newKVResult
  iexists «$r0_ptr», γ
  isplitr
  · ipureintro; rfl
  iframe Hlkv
  isplitl [Hr Hrds]
  · rw [hn, List.replicate_succ]
    iapply BigSepL.bigSepL_cons.2
    iframe
  iframe Hop
  isplitr
  · unfold leasingCloseFn
    imodintro
    iintro %Φ' Hop' HΦ'
    iapply hClose «$r0_ptr» γ pfx $$ [$Hpkg $Hlkv $Hcanc $Hop']
    inext
    iintro -
    iexact HΦ'
  iexact Herr

end proof

end leasing
end EtcdGrove
end Perennial
