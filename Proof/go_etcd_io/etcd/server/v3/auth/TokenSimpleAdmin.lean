/-
**The simple token provider's admin side** (`tokenSimple`'s `enable`, `disable`,
`invalidateUser`; the TTL keeper's `stop` and `deleteSimpleToken`; the auth plan's S5d,
2026-10-25; `notes/decisions.md`, "S5d of the auth plan"). Lean-first (no Rocq counterpart).

**The admin side's share** (`simpleAdmin p`, the contract's admin resource `A`,
`tokenProviderOkA`): half the provider's keeper field (the other half is the lock invariant's,
`simpleLk`) and, for a keeper that is set, its stop channels (`keeperStop`). `invalidateUser` reads
the field before taking `simpleTokensMu`; `enable`/`disable` write it under the mutex with both
halves. Not a Go race: etcd's callers serialize the three (`enable`/`disable` under the store's
`enabledMu`, `invalidateUser` on the apply thread).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.TokenSimple
public import Perennial.Golang.Theory.Chan.Idioms.Bag
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast
public import Spec.go_uber_org.zap.Logger__Debug
public import Spec.go_uber_org.zap.String

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth auth

namespace auth

section pred
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **A keeper's stop channels** (persistent): `stopc`, a bag of signals (`stop()` sends one, `run`
returns on it), and `donec`, a broadcast channel `run` closes on its way out (`stop()` waits on it). -/
def keeperStop (k : Loc) : IProp GF :=
  iprop(∃ (sc dc : Loc) (γs γd : ChanNames), kpF go!"stopc" k ↦□ sc ∗ kpF go!"donec" k ↦□ dc ∗
    isChanBag γs sc (fun _ : Unit => iprop(True)) ∗ ownBroadcastChan dc γd iprop(True) .Unknown)

instance keeperStop_persistent (k : Loc) : Persistent (keeperStop (GF := GF) k) := by
  unfold keeperStop; infer_instance

/-- **The admin side's share of the simple provider** `p` (see the file header). -/
def simpleAdmin (p : Loc) : IProp GF :=
  iprop(∃ k : Loc, tsF go!"simpleTokenKeeper" p ↦{DFrac.own (1 : Qp).half} k ∗
    (⌜k = null⌝ ∨ keeperStop k))

/-- **The delete callback's contract** (`enable`'s `delf`, the keeper's `deleteTokenFunc`): called
under the provider's mutex with the map and its tokens' elements, it deletes the token (the map's
other entries kept). -/
def delfOk (p : Loc) (γt γf : GName) (df : GoFunc) : IProp GF :=
  iprop(□ (∀ (tk : GoString) (mp : Loc) (m : GMap GoString GoString),
    {{ tsF go!"simpleTokens" p ↦ mp ∗ mp ↦$ m ∗
        ([∗map] t ↦ u ∈ m, ghostMapElem γt t DFrac.discard u ∗ ghostMapElem γf t DFrac.discard ()) }}
      (App (Val #df) (Val #tk))
    {{ RET #(); ∃ m' : GMap GoString GoString, tsF go!"simpleTokens" p ↦ mp ∗ mp ↦$ m' ∗
        ([∗map] t ↦ u ∈ m', ghostMapElem γt t DFrac.discard u ∗ ghostMapElem γf t DFrac.discard ()) }}))

/-- **What a keeper's goroutine `run` is given** (`enable`): the keeper's read-only fields, its
stop channels with the right to close `donec`, the provider's mutex with its invariant, the
keeper's element of the ghost set (so that, after each `Lock`, it finds its map among the
keepers' maps: the auth plan's S5d), the delete callback's contract. -/
def keeperRun (k p : Loc) (γt γf γk : GName) : IProp GF :=
  iprop(∃ (sc dc : Loc) (γs γd : ChanNames) (df : GoFunc),
    kpF go!"stopc" k ↦□ sc ∗ kpF go!"donec" k ↦□ dc ∗ kpF go!"deleteTokenFunc" k ↦□ df ∗
    kpF go!"mu" k ↦□ tsF go!"simpleTokensMu" p ∗
    isChanBag γs sc (fun _ : Unit => iprop(True)) ∗ ownBroadcastChan dc γd iprop(True) .Pending ∗
    sync.isMutex (tsF go!"simpleTokensMu" p) (simpleLk p γt γf γk) ∗
    ghostMapElem γk k DFrac.discard () ∗ delfOk p γt γf df)

/-- **The hypothesis on the keeper's goroutine** (`simpleTokenTTLKeeper.run`; not an axiom): from
`keeperRun`, it returns (a `time.Ticker` loop: on each tick, under the mutex, every expired token
deleted from the provider's map, through the callback, and from the keeper's; on a signal on
`stopc`, the ticker stopped and `donec` closed). True of the Go code; not proved here: the
loop's `select` over the ticker's channel bag and `stopc`, the range with deletion over the
keeper's map (`wp_map_for_range_mut`), are the remaining work (`notes/decisions.md`, "S5d"). -/
def RunSpec : Prop :=
  ∀ (k p : Loc) (γt γf γk : GName),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ keeperRun k p γt γf γk }}
      (App (Val #(methods (go.GoType.PointerType simpleTokenTTLKeeper.ty) go!"run" #k)) (Val #()))
    {{ RET #(); True }}

end pred

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- `tm.deleteSimpleToken(token)`: the keeper's map, kept. -/
theorem keeper_delete (k : Loc) (token : GoString) :
    {{ keeperMap (GF := GF) k }}
      (App (Val #(methods (go.GoType.PointerType simpleTokenTTLKeeper.ty) go!"deleteSimpleToken" #k))
        (Val #token))
    {{ RET #(); keeperMap k }} := by
  wp_start as Hk
  iunfold keeperMap at Hk
  icases Hk with ⟨%km, %tm, %ttl, #Hkm, Htm, #Httl⟩
  (try wp_auto)
  wp_apply (wp_mapDelete km tm token go.string time.Time.ty) $$ [$Htm] as Htm
  (try wp_auto)
  iapply HΦ
  iunfold keeperMap; iexists km, _, ttl; iframe #; iexact Htm

/-- **`tm.stop()`**: it returns (a signal sent on `stopc`, or `donec` closed; then `donec`
closed). -/
theorem keeper_stop (k : Loc) :
    {{ keeperStop (GF := GF) k }}
      (App (Val #(methods (go.GoType.PointerType simpleTokenTTLKeeper.ty) go!"stop" #k)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as Hs
  iunfold keeperStop at Hs
  icases Hs with ⟨%sc, %dc, %γs, %γd, #Hsc, #Hdc, #Hbag, #Hbc⟩
  ihave #Hdch := ownBroadcastChan_is_chan _ _ _ _ $$ Hbc
  wp_auto_lc 2
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, sc, γs, ()
    isplit
    · ipureintro; exact ⟨rfl, rfl⟩
    isplit
    · iapply is_bag_is_chan $$ Hbag
    iapply bag_send_au $$ [$Hlc1 $Hlc2] Hbag []
    · itrivial
    inext
    (try wp_auto)
    wp_bind (App (Val (chan.receive (go.GoType.StructType []))) (Val #dc))
    iapply (chan.wp_receive (V := Unit) dc γd) $$ Hdch
    iintro -
    iapply broadcast_chan_receive $$ Hbc
    iintro -
    (try wp_auto)
    iapply HΦ; itrivial
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, dc, γd
    isplit
    · ipureintro; rfl
    isplit
    · iexact Hdch
    iapply broadcast_chan_receive $$ Hbc
    iintro -
    (try wp_auto)
    wp_bind (App (Val (chan.receive (go.GoType.StructType []))) (Val #dc))
    iapply (chan.wp_receive (V := Unit) dc γd) $$ Hdch
    iintro -
    iapply broadcast_chan_receive $$ Hbc
    iintro -
    (try wp_auto)
    iapply HΦ; itrivial
  iapply BigAndL.bigAndL_nil.2
  itrivial

/-- **`t.disable()`**: the keeper stopped and the map emptied (the old map's tokens dropped: S5's
issued map is keyed by (token, user), so a token string may be issued again). -/
theorem tokenSimple_disable (p : Loc) (γt γf : GName) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ simpleOk (GF := GF) p γt γf ∗
        simpleAdmin p }}
      (App (Val #(methods (go.GoType.PointerType tokenSimple.ty) go!"disable" #p)) (Val #()))
    {{ RET #(); simpleAdmin p }} := by
  wp_start as ⟨#Hok, Had⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold simpleOk at Hok
  icases Hok with ⟨%lg, %γk, #Hlg, %Hlgnn, #Hmu⟩
  iunfold simpleAdmin at Had
  icases Had with ⟨%ka, Hka, #Hkst⟩
  (try wp_auto)
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlk, HI⟩
  iunfold simpleLk at HI
  icases HI with ⟨%mp, %m, %k, %ks, %ttl, %S, Hmp, Hm, Hbig, Hauth, Hk, %Hkks, HKa, Hks, Httl, %Httlpos⟩
  icombine Hka Hk gives %Heq
  subst Heq
  ihave Hkf := (typedPointsto_half_split _ _ (1 : Qp)).2 $$ [Hka Hk]
  · iframe
  (try wp_auto)
  wp_apply (wp_map_make1 (K := GoString) (V := GoString) go.string go.string) as %mp' Hm'
  (try wp_auto)
  ihave ⟨Hka, Hk⟩ := (typedPointsto_half_split _ _ (1 : Qp)).1 $$ Hkf
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlk Hmp Hm' Hauth Hk HKa Hks Httl]
  · iunfold simpleLk
    iexists mp', ∅, null, ks, ttl, S
    iframe Hmp Hm' Hauth Hk HKa Hks Httl
    isplitl []
    · iapply BigSepM.bigSepM_empty.2
      itrivial
    ipureintro; exact ⟨Or.inl rfl, Httlpos⟩
  (try wp_auto)
  wp_if_destruct
  · (try wp_auto)
    iapply HΦ
    iunfold simpleAdmin; iexists null; iframe Hka; ileft; ipureintro; rfl
  (try wp_auto)
  icases Hkst with (%Hn | #Hst)
  · simp_all
  wp_apply (keeper_stop ka) $$ [$Hst]
  (try wp_auto)
  iapply HΦ
  iunfold simpleAdmin; iexists null; iframe Hka; ileft; ipureintro; rfl

/-- **`t.invalidateUser(name)`**: the user's tokens removed from the map and from the keeper's (the
map's other entries, and their issued elements and rights, kept). -/
theorem tokenSimple_invalidateUser (p : Loc) (γt γf : GName) (user : GoString) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ simpleOk (GF := GF) p γt γf ∗
        simpleAdmin p }}
      (App (Val #(methods (go.GoType.PointerType tokenSimple.ty) go!"invalidateUser" #p)) (Val #user))
    {{ RET #(); simpleAdmin p }} := by
  wp_start as ⟨#Hok, Had⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold simpleOk at Hok
  icases Hok with ⟨%lg, %γk, #Hlg, %Hlgnn, #Hmu⟩
  iunfold simpleAdmin at Had
  icases Had with ⟨%ka, Hka, #Hkst⟩
  (try wp_auto)
  wp_if_destruct
  · (try wp_auto)
    iapply HΦ
    iunfold simpleAdmin; iexists _; iframe Hka; ileft; ipureintro; rfl
  (try wp_auto)
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlk, HI⟩
  iunfold simpleLk at HI
  icases HI with ⟨%mp, %m, %k, %ks, %ttl, %S, Hmp, Hm, Hbig, Hauth, Hk, %Hkks, HKa, Hks, Httl, %Httlpos⟩
  icombine Hka Hk gives %Heq
  subst Heq
  rcases Hkks with Hkn | Hkm
  · exact absurd Hkn Hif
  icases keepers_acc γk ks ka Hkm $$ Hks with ⟨Hkp, Hback⟩
  (try wp_auto)
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range_mut (K := GoString) (V := GoString) (fun (_ : Nat) (m' : GMap GoString GoString) =>
      iprop(∃ (nv tv : GoString),
        "Hmp" ∷ tsF go!"simpleTokens" p ↦ mp ∗ "Hk" ∷ tsF go!"simpleTokenKeeper" p ↦{DFrac.own (1 : Qp).half} ka ∗
        "Hkp" ∷ keeperMap ka ∗ "name" ∷ name_ptr ↦ nv ∗ "token" ∷ token_ptr ↦ tv ∗
        "t" ∷ t_ptr ↦ p ∗ "username" ∷ username_ptr ↦ user ∗
        "Hbig" ∷ ([∗map] t ↦ u ∈ m', iprop(ghostMapElem (GF := GF) γt t DFrac.discard u ∗
          ghostMapElem γf t DFrac.discard ()))))
    _ go.string go.string mp m $$ Hm
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [Hmp Hk Hkp name token t username Hbig]
  · iexists _, _
    simp only [named]
    iframe
  isplitr
  · imodintro
    iintro %i %key %v %m' ⟨%Hki, %Hmv, %Hagree⟩ HP Hm
    iNamed HP
    (try wp_auto)
    wp_if_destruct
    · (try wp_auto)
      wp_apply (wp_mapDelete mp m' key go.string go.string) $$ [$Hm] as Hm
      (try wp_auto)
      wp_apply (keeper_delete ka key) $$ [$Hkp] as Hkp
      (try wp_auto)
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists _
      iframe Hm
      isplitl
      · iexists _, _
        simp only [named]
        iframe Hmp Hk Hkp name token t username
        cases hl : m'.lookup key with
        | none => rw [GMap.delete_notin _ _ hl]; iexact Hbig
        | some u =>
          icases (BigSepM.bigSepM_delete hl).1 $$ Hbig with ⟨-, Hbig⟩
          iexact Hbig
      ipureintro
      intro k' hk
      rw [GMap.lookup_delete_ne _ (Ne.symm hk)]
    · (try wp_auto)
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists m'
      iframe Hm
      isplitl
      · iexists _, _
        simp only [named]
        iframe
      ipureintro; intro k' _; rfl
  iintro %m' HP Hm
  iNamed HP
  (try wp_auto)
  ihave Hks := Hback $$ Hkp
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlk Hmp Hm Hbig Hauth Hk HKa Hks Httl]
  · iunfold simpleLk
    iexists mp, m', ka, ks, ttl, S
    iframe Hmp Hm Hbig Hauth Hk HKa Hks Httl
    ipureintro; exact ⟨Or.inr Hkm, Httlpos⟩
  (try wp_auto)
  iapply HΦ
  iunfold simpleAdmin; iexists ka; iframe Hka Hkst

/-- A broadcast channel's closing right, and its persistent `Unknown` view. -/
theorem bc_pending_unknown (ch : Loc) (γ : ChanNames) (Q : IProp GF) :
    ownBroadcastChan ch γ Q .Pending ⊢ ownBroadcastChan ch γ Q .Pending ∗ ownBroadcastChan ch γ Q .Unknown := by
  iintro Hown
  icases ownBroadcastChan_open _ _ _ _ $$ Hown with ⟨%γch, #Hint, Hown⟩
  isplitl [Hown]
  · iapply ownBroadcastChan_close _ _ _ _ γch; iframe #; iexact Hown
  · iapply ownBroadcastChan_close _ _ _ _ γch; iframe #

/-- **`t.enable()`**: a keeper created and its goroutine started (`RunSpec`), when none is set. -/
theorem tokenSimple_enable (hRun : RunSpec (GF := GF) (hG := hG))
    (h_Debug : zap.Logger.Debug.spec (GF := GF) (hG := hG))
    (h_String : zap.String.spec (GF := GF) (hG := hG)) (p : Loc) (γt γf : GName) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ simpleOk (GF := GF) p γt γf ∗
        simpleAdmin p }}
      (App (Val #(methods (go.GoType.PointerType tokenSimple.ty) go!"enable" #p)) (Val #()))
    {{ RET #(); simpleAdmin p }} := by
  wp_start as ⟨#Hok, Had⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold simpleOk at Hok
  icases Hok with ⟨%lg, %γk, #Hlg, %Hlgnn, #Hmu⟩
  iunfold simpleAdmin at Had
  icases Had with ⟨%ka, Hka, #Hkst⟩
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlk, HI⟩
  iunfold simpleLk at HI
  icases HI with ⟨%mp, %m, %k, %ks, %ttl, %S, Hmp, Hm, Hbig, Hauth, Hk, %Hkks, HKa, Hks, Httl, %Httlpos⟩
  icombine Hka Hk gives %Heq
  subst Heq
  (try wp_auto)
  wp_if_destruct
  rotate_left
  · -- already enabled
    (try wp_auto)
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlk Hmp Hm Hbig Hauth Hk HKa Hks Httl]
    · iunfold simpleLk
      iexists mp, m, ka, ks, ttl, S
      iframe Hmp Hm Hbig Hauth Hk HKa Hks Httl
      ipureintro; exact ⟨Hkks, Httlpos⟩
    (try wp_auto)
    iapply HΦ
    iunfold simpleAdmin; iexists ka; iframe Hka Hkst
  wp_if_destruct
  · exfalso; simp_all; omega
  (try wp_auto)
  ipersist t
  wp_apply (wp_map_make1 (K := GoString) (V := time.Time) go.string time.Time.ty) as %km Hkm
  wp_apply (chan.wp_make1 (V := Unit)) as %dc %γd ⟨#Hdc, %Hcapd, Hdo⟩
  wp_apply (chan.wp_make1 (V := Unit)) as %sc %γs ⟨#Hsc, %Hcaps, Hso⟩
  (try wp_auto)
  ihave %Hkpnn := typedPointsto_not_null _ _ _ $$ «$r0»
  ihave Hkf := typedPointsto_split _ _ _ $$ «$r0»
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hkf
  -- the new keeper in the ghost set (whether or not its address is there already)
  ihave HinsK : iprop(|==> ∃ K' : GMap Loc Unit, ghostMapAuth γk 1 K' ∗
      ghostMapElem γk «$r0_ptr» DFrac.discard () ∗ ⌜K'.lookup «$r0_ptr» = some ()⌝ ∗
      (keeperMap «$r0_ptr» -∗
        [∗map] k' ↦ _u ∈ K', iprop(keeperMap (GF := GF) k' ∗ ghostMapElem γk k' DFrac.discard ()))) $$
      [HKa Hks]
  · cases hK : ks.lookup «$r0_ptr» with
    | some u =>
      cases u
      icases (BigSepM.bigSepM_lookup_acc
        (Φ := fun k' (_ : Unit) => iprop(keeperMap (GF := GF) k' ∗ ghostMapElem γk k' DFrac.discard ())) hK).1
        $$ Hks with ⟨⟨-, #He⟩, Hback⟩
      imodintro
      iexists ks
      iframe HKa He
      isplitr
      · ipureintro; exact hK
      iintro Hkm
      iapply Hback
      iframe Hkm He
    | none =>
      imod (ghost_map_insert_persist «$r0_ptr» () hK) $$ HKa with ⟨HKa, #He⟩
      imodintro
      iexists (ks.insert «$r0_ptr» ())
      iframe HKa He
      isplitr
      · ipureintro; simp
      iintro Hkm
      iapply (BigSepM.bigSepM_insert hK).2
      iframe Hks Hkm He
  imod HinsK with ⟨%K', HKa, #HelK, %HK', HKback⟩
  imod (start_bag (fun _ : Unit => iprop(True)) ChanState.Idle sc γs trivial) $$ Hsc Hso with #Hbag
  imod (alloc_broadcast_chan iprop(True) γd dc) $$ Hdc Hdo with Hpend
  icases bc_pending_unknown dc γd _ $$ Hpend with ⟨Hpend, #Hunk⟩
  ihave Hkf := (typedPointsto_half_split _ _ (1 : Qp)).2 $$ [Hka Hk]
  · iframe
  ipersist tokens
  ipersist donec
  ipersist stopc
  ipersist deleteTokenFunc
  ipersist mu
  ipersist simpleTokenTTL
  (try wp_auto)
  wp_apply wp_fork $$ [Hpend]
  · wp_apply (hRun «$r0_ptr» p γt γf γk) $$ [Hpend]
    · iframe #
      iunfold keeperRun
      iexists sc, dc, γs, γd, _
      iframe #
      iframe Hpend
      iunfold delfOk
      iintro !> %tk %mp0 %m0 %Ψ !> ⟨Hmp0, Hm0, Hbig0⟩ HΨ
      (try wp_auto)
      wp_apply (wp_map_lookup2 go.string go.string mp0 m0 tk) $$ [$Hm0] as Hm0
      (try wp_auto)
      ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
      · iPkgInit
      wp_if_destruct
      · (try wp_auto)
        wp_apply h_String $$ [] as %f1 -
        wp_apply h_String $$ [] as %f2 -
        (try wp_auto)
        wp_apply wp_slice_literal
        (try wp_auto)
        isplitr
        · ipureintro; rfl
        iintro %fsl
        iintro Hfsl
        (try wp_auto)
        wp_apply h_Debug $$ []
        · iframe #; ipureintro; exact Hlgnn
        (try wp_auto)
        wp_apply (wp_mapDelete mp0 m0 tk go.string go.string) $$ [$Hm0] as Hm0
        (try wp_auto)
        iapply HΨ
        iexists _
        iframe Hmp0 Hm0
        cases hl : m0.lookup tk with
        | none => rw [GMap.delete_notin _ _ hl]; iexact Hbig0
        | some u =>
          icases (BigSepM.bigSepM_delete hl).1 $$ Hbig0 with ⟨-, Hbig0⟩
          iexact Hbig0
      (try wp_auto)
      iapply HΨ
      iexists _
      iframe Hmp0 Hm0 Hbig0
    ipureintro; exact isPanic_intoVal _
  (try wp_auto)
  ihave ⟨Hka, Hk⟩ := (typedPointsto_half_split _ _ (1 : Qp)).1 $$ Hkf
  ihave Hks := HKback $$ [Hkm]
  · iunfold keeperMap; iexists km, ∅, ttl; iframe Hkm; iframe #
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlk Hmp Hm Hbig Hauth Hk HKa Hks Httl]
  · iunfold simpleLk
    iexists mp, m, «$r0_ptr», K', ttl, S
    iframe Hmp Hm Hbig Hauth Hk HKa Hks Httl
    ipureintro; exact ⟨Or.inr HK', Httlpos⟩
  (try wp_auto)
  iapply HΦ
  iunfold simpleAdmin; iexists «$r0_ptr»; iframe Hka
  iright
  iunfold keeperStop; iexists sc, dc, γs, γd; iframe #

/-- **The simple provider meets the token provider's contract** in the mode `on γa`, with the admin
side's resource `simpleAdmin p` (the auth plan's S5d): `info` over `ValidSpec` (the contract's
`info` clause has no context premise: `tokenSimple_info_ctx` is `info` on a context with no
hypothesis), `enable` over `RunSpec`, `disable`, `invalidateUser`, `assign`. -/
theorem tokenSimple_okA (hValid : ValidSpec (GF := GF) (hG := hG)) (hRun : RunSpec (GF := GF) (hG := hG))
    (h_Debug : zap.Logger.Debug.spec (GF := GF) (hG := hG))
    (h_String : zap.String.spec (GF := GF) (hG := hG)) (p : Loc) (γa : AuthNames) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ simpleOk p γa.tok γa.fresh ⊢
      tokenProviderOkA (interface.mkOk (go.GoType.PointerType tokenSimple.ty) #p) (.on γa) (simpleAdmin p) := by
  iintro ⟨#Hpkg, #Hok⟩
  iunfold tokenProviderOkA
  iexists _
  isplitr
  · ipureintro; rfl
  isplitr
  · iintro !> %ctx %token %rev %Φ !> - HΦ
    iapply (tokenSimple_info hValid p γa.tok γa.fresh γa rfl ctx token rev Φ)
    iframe #; iexact HΦ
  isplitr
  · iintro !> %Φ !> HA HΦ
    iapply (tokenSimple_enable hRun h_Debug h_String p γa.tok γa.fresh) $$ [HA] HΦ
    iframe #; iexact HA
  isplitr
  · iintro !> %Φ !> HA HΦ
    iapply (tokenSimple_disable p γa.tok γa.fresh) $$ [HA] HΦ
    iframe #; iexact HA
  isplitr
  · iintro !> %name %Φ !> HA HΦ
    iapply (tokenSimple_invalidateUser p γa.tok γa.fresh name) $$ [HA] HΦ
    iframe #; iexact HA
  · iintro !> %ctx %user %rev %Φ !> Hctx HΦ
    iapply (tokenSimple_assign p γa.tok γa.fresh γa rfl rfl ctx user rev) $$ [Hctx] HΦ
    iframe #; iexact Hctx

end proof

end auth
end EtcdGrove
end Perennial
