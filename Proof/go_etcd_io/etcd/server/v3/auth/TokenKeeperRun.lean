/-
**The simple token provider's TTL keeper goroutine** (`simpleTokenTTLKeeper.run`, the auth plan's
S5e, 2026-10-25; `notes/decisions.md`, "S5e of the auth plan"). Lean-first (no Rocq counterpart).

`run` (`simple_token.go`): a `time.Ticker` at the package's tick (`simpleTokenTTLResolution`, the
auth package's fact: read-only, positive), then a loop whose `select` either receives a tick (some
`time.Time`: Perennial's ticker channel is a bag of arbitrary times) and, under the provider's
mutex, deletes every expired token from the provider's map (the delete callback, `delfOk`) and
from the keeper's own, or receives on `stopc` and returns; its deferred function stops the ticker
and closes `donec`. Whether a token has expired is `Time.After`'s answer, some boolean (Perennial
has no order model on times): any tick may delete any token, which the token binding tolerates (a
token deleted is one `info` no longer answers). After each `Lock` the keeper finds its own map in
the lock invariant through its element of the keepers' ghost set (`simpleLk`, S5d).

`keeper_run` discharges S5d's hypothesis `RunSpec`; `tokenSimple_okA_run` is S5d's
`tokenSimple_okA` without it. `tokenSimple_new` is `newTokenProviderSimple`: it allocates the
provider, its mutex with the lock invariant (no token, no keeper, the issued tokens' authority and
the keepers' ghost set fresh) and returns, under fresh names, the provider's read-only facts
(`simpleOk`), its index waiter (`simpleWaitOk`), the admin side's share (`simpleAdmin`, no keeper)
and the authority over the rights to issue tokens (`γf`, empty: whoever chooses tokens, the
server's apply thread, mints them, one per raft index).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.TokenSimpleAdmin
public import Perennial.Proof.time.Link
public import Perennial.Proof.time.PtrMethods
public import Spec.go_uber_org.zap.NewNop

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth auth

namespace auth

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- `(*Time).After`: the value method on `*l` (the method set of `*Time`), some boolean. A local
copy of the shape of Perennial's `Time.wp_ptr_Before_of` (`notes/perennial-changes.md`). -/
theorem time_wp_ptr_After (l : Loc) (t u : time.Time) :
    {{ (l ↦ t : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType time.Time.ty @!! go!"After")) (Val #u))
    {{ (b : Bool), RET #b; l ↦ t }} := by
  wp_start as Hl
  wp_auto
  wp_apply time.Time.wp_After as %b -
  iapply HΦ $$ Hl

/-- **The keeper's goroutine `run`** (see the file header): S5d's `RunSpec`. -/
theorem keeper_run : RunSpec (GF := GF) (hG := hG) := by
  intro k p γt γf γk
  wp_start as Hr
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave Hai : (authInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hai with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨%d, #Hd, %Hdpos⟩⟩
  iunfold keeperRun at Hr
  icases Hr with ⟨%sc, %dc, %γs, %γd, %df, #Hsc, #Hdc, #Hdf, #Hmuf, #Hbag, Hpend, #Hmu, #Hel, Hdelf⟩
  iunfold delfOk at Hdelf
  icases Hdelf with #Hdelf
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply (lc := 2) time.wp_NewTicker $$ [] as %tk %tch %γtk #Htk
  · ipureintro; exact Hdpos
  iunfold time.isTicker at Htk
  icases Htk with ⟨#HtC, #HtI, #Htbag⟩
  ipersist tm
  ipersist tokenTicker
  wp_for
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- a tick: the expired tokens deleted, under the provider's mutex
    simp only [chan.blockingClausePre]
    iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, tch, γtk
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Htbag
    iapply bag_recv_au $$ [$Hlc1 $Hlc2] Htbag
    inext
    iintro %tm0 -
    (try wp_auto)
    wp_apply (lc := 2) time.wp_Now as %now -
    (try wp_auto)
    wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlk, HI⟩
    iunfold simpleLk at HI
    icases HI with ⟨%mp, %m, %kc, %ks, %ttl, %S, Hmp, Hm, Hbig, Hauth, Hk, %Hkks, HKa, Hks, Httl, %Httlpos⟩
    icombine HKa Hel gives %Hkin
    icases keepers_acc γk ks k Hkin $$ Hks with ⟨Hkp, Hback⟩
    iunfold keeperMap at Hkp
    icases Hkp with ⟨%km, %tmap, %kttl, #Hkm, Htm, #Hkttl⟩
    (try wp_auto)
    wp_func_lits
    wp_bind (App (App (Val (map.forRange _ _)) _) _)
    iapply wp_map_for_range_mut (K := GoString) (V := time.Time) (fun (_ : Nat) (_ : GMap GoString time.Time) =>
        iprop(∃ (tv : GoString) (ev : time.Time) (pm : GMap GoString GoString),
          "Hmp" ∷ tsF go!"simpleTokens" p ↦ mp ∗ "Hm" ∷ mp ↦$ pm ∗
          "Hbig" ∷ ([∗map] t ↦ u ∈ pm, iprop(ghostMapElem (GF := GF) γt (t, u) DFrac.discard () ∗
            ghostMapElem γf t (DFrac.own 1) ())) ∗
          "t" ∷ t_ptr ↦ tv ∗ "tokenendtime" ∷ tokenendtime_ptr ↦ ev ∗ "nowtime" ∷ nowtime_ptr ↦ now))
      _ go.string time.Time.ty km tmap $$ Htm
    iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
    isplitl [Hmp Hm Hbig t tokenendtime nowtime]
    · iexists _, _, m
      simp only [named]
      iframe
    isplitr
    · imodintro
      iintro %i %key %v %m' ⟨%Hki, %Hmv, %Hagree⟩ HP Htm
      iNamed HP
      (try wp_auto)
      wp_apply (time_wp_ptr_After nowtime_ptr now v) $$ [$nowtime] as %b nowtime
      wp_if_destruct
      · (try wp_auto)
        unfold forMapPostcondition
        iright; ileft
        isplitr
        · ipureintro; rfl
        iexists m'
        iframe Htm
        isplitl
        · iexists _, _, _
          simp only [named]
          iframe
        ipureintro; intro k' _; rfl
      · (try wp_auto)
        wp_apply Hdelf $$ [$Hmp $Hm $Hbig] as ⟨%pm'', Hmp, Hm, Hbig⟩
        (try wp_auto)
        wp_apply (wp_mapDelete km m' key go.string time.Time.ty) $$ [$Htm] as Htm
        (try wp_auto)
        unfold forMapPostcondition
        iright; ileft
        isplitr
        · ipureintro; rfl
        iexists _
        iframe Htm
        isplitl
        · iexists _, _, pm''
          simp only [named]
          iframe
        ipureintro
        intro k' hk
        rw [GMap.lookup_delete_ne _ (Ne.symm hk)]
    iintro %tmap' HP Htm
    iNamed HP
    (try wp_auto)
    ihave Hks := Hback $$ [Htm]
    · iunfold keeperMap; iexists km, tmap', kttl; iframe Htm; iframe #
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlk Hmp Hm Hbig Hauth Hk HKa Hks Httl]
    · iunfold simpleLk
      iexists mp, _, kc, ks, ttl, S
      iframe Hmp Hm Hbig Hauth Hk HKa Hks Httl
      ipureintro; exact ⟨Hkks, Httlpos⟩
    wp_for_post
    iframe
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- a signal on `stopc`: the ticker stopped, `donec` closed
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, sc, γs
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hbag
    iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hbag
    inext
    iintro %u -
    (try wp_auto)
    wp_for_post
    (try wp_auto)
    wp_apply time.Ticker.wp_Stop tk $$ []
    · iexists tch, γtk; iunfold time.isTicker; iframe #
    (try wp_auto)
    ihave #Htt : □ (True : IProp GF) $$ []
    · imodintro; itrivial
    wp_apply wp_broadcast_chan_close dc γd iprop(True) $$ [$Hpend $Htt] as -
    (try wp_auto)
    iapply HΦ
    itrivial
  iapply BigAndL.bigAndL_nil.2
  itrivial

/-- **The simple provider meets the token provider's contract** in the mode `on γa` with the admin
side's resource (S5d's `tokenSimple_okA`, its keeper hypothesis `RunSpec` discharged by
`keeper_run`). -/
theorem tokenSimple_okA_run (hValid : ValidSpec (GF := GF) (hG := hG))
    (h_Debug : zap.Logger.Debug.spec (GF := GF) (hG := hG))
    (h_String : zap.String.spec (GF := GF) (hG := hG)) (p : Loc) (γa : AuthNames) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ simpleOk p γa.tok γa.fresh ⊢
      tokenProviderOkA (interface.mkOk (go.GoType.PointerType tokenSimple.ty) #p) (.on γa) (simpleAdmin p) :=
  tokenSimple_okA hValid keeper_run h_Debug h_String p γa

/-- **`newTokenProviderSimple(lg, indexWaiter, TokenTTL)`** (see the file header): for a positive
TTL (`NewTokenProvider` passes the configured one, or `simpleTokenTTLDefault`) and an index waiter
whose channels are `anyRecv`. -/
theorem tokenSimple_new (h_NewNop : zap.NewNop.spec (GF := GF) (hG := hG))
    (lg : Loc) (iw : GoFunc) (ttl : time.Duration) (hpos : 0 < sint.Z ttl) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗
        □ (∀ idx : w64, {{ True }} (App (Val #iw) (Val #idx)) {{ (ch : Loc), RET #ch; anyRecv ch }}) }}
      (App (App (App (Val (@! newTokenProviderSimple)) (Val #lg)) (Val #iw)) (Val #ttl))
    {{ (p : Loc), RET #p; ∃ γt γf : GName, simpleOk p γt γf ∗ simpleWaitOk p ∗ simpleAdmin p ∗
        ghostMapAuth γf 1 (∅ : GMap GoString Unit) }} := by
  wp_start as #Hiw
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  (try wp_auto)
  wp_if_destruct
  · wp_apply h_NewNop as %lg' %Hlg'
    (try wp_auto)
    wp_apply (wp_map_make1 (K := GoString) (V := GoString) go.string go.string) as %mp Hm
    (try wp_auto)
    wp_alloc p as Hp
    iStructNamed Hp
    imod (tokAlloc (GF := GF)) with ⟨%γt, Htok⟩
    imod (ghost_map_alloc_empty (GF := GF) (K := GoString) (V := Unit)) with ⟨%γf, Hf⟩
    imod (ghost_map_alloc_empty (GF := GF) (K := Loc) (V := Unit)) with ⟨%γk, Hka⟩
    ihave ⟨Hk1, Hk2⟩ := (typedPointsto_half_split _ _ (1 : Qp)).1 $$ simpleTokenKeeper
    imod sync.init_Mutex (simpleLk p γt γf γk) ⊤ (tsF go!"simpleTokensMu" p)
      $$ [simpleTokensMu] [simpleTokens Hm Htok Hk1 Hka simpleTokenTTL] with #Hmu
    · iexact simpleTokensMu
    · inext
      iunfold simpleLk
      iexists mp, ∅, null, ∅, ttl, ∅
      iframe
      isplitl []
      · iapply BigSepM.bigSepM_empty.2; itrivial
      isplitr
      · ipureintro; left; rfl
      isplitl []
      · iapply BigSepM.bigSepM_empty.2; itrivial
      ipureintro; exact hpos
    ipersist lg
    ipersist indexWaiter
    (try wp_auto)
    iapply HΦ
    iexists γt, γf
    iframe Hf
    isplitr
    · iunfold simpleOk
      iexists lg', γk
      iframe #
      ipureintro; exact Hlg'
    isplitr
    · iunfold simpleWaitOk
      iexists iw
      iframe #
    iunfold simpleAdmin
    iexists null
    iframe Hk2
    ileft; ipureintro; rfl
  · wp_apply (wp_map_make1 (K := GoString) (V := GoString) go.string go.string) as %mp Hm
    (try wp_auto)
    wp_alloc p as Hp
    iStructNamed Hp
    imod (tokAlloc (GF := GF)) with ⟨%γt, Htok⟩
    imod (ghost_map_alloc_empty (GF := GF) (K := GoString) (V := Unit)) with ⟨%γf, Hf⟩
    imod (ghost_map_alloc_empty (GF := GF) (K := Loc) (V := Unit)) with ⟨%γk, Hka⟩
    ihave ⟨Hk1, Hk2⟩ := (typedPointsto_half_split _ _ (1 : Qp)).1 $$ simpleTokenKeeper
    imod sync.init_Mutex (simpleLk p γt γf γk) ⊤ (tsF go!"simpleTokensMu" p)
      $$ [simpleTokensMu] [simpleTokens Hm Htok Hk1 Hka simpleTokenTTL] with #Hmu
    · iexact simpleTokensMu
    · inext
      iunfold simpleLk
      iexists mp, ∅, null, ∅, ttl, ∅
      iframe
      isplitl []
      · iapply BigSepM.bigSepM_empty.2; itrivial
      isplitr
      · ipureintro; left; rfl
      isplitl []
      · iapply BigSepM.bigSepM_empty.2; itrivial
      ipureintro; exact hpos
    ipersist lg
    ipersist indexWaiter
    (try wp_auto)
    iapply HΦ
    iexists γt, γf
    iframe Hf
    isplitr
    · iunfold simpleOk
      iexists lg, γk
      iframe #
      ipureintro; exact Hif
    isplitr
    · iunfold simpleWaitOk
      iexists iw
      iframe #
    iunfold simpleAdmin
    iexists null
    iframe Hk2
    ileft; ipureintro; rfl

end proof

end auth
end EtcdGrove
end Perennial
