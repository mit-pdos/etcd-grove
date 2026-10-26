/-
**The admin check at the latest state on the apply path** (the auth plan's E3c, 2026-10-27;
`notes/decisions.md`, "E3c of the auth plan"). Lean-first (no Rocq counterpart).

`authApplierV3.Apply` (`auth.go`) checks an admin request (`needAdminPermission`) with the store's
`IsAdminPermitted` before it calls its inner applier's `Apply`; its spec (and the chain's `Apply`
clause, `applierTriples`) gives, for a dispatched request, S3's verdict at some recorded state
(`adminPass`) and nothing for a rejected one. The apply thread holds the admin side's authority
(E2s's `auth.latestRes`), so the check's verdict is the latest state's (`isAuthStoreL`'s
`IsAdminPermitted`, E2s's `auth.adminVerdictL`) both ways: here, as E2y did for the KV path, that
verdict lifted through `Apply`, beside the existing triples (none of which changes):

- `adminPassL`/`adminRejL`: the admin check passed / refused at the latest state of `hs`, for the
  request's own principal (`principalOf rq`, the header's, which `Apply` hands the store).
- `applyNR c a`: an applier whose `Apply` always runs its `applyFunc` (no rejection): the backend's
  (`applyNR_backend`) and a quota applier's over one (`applyNR_quota`), so the base chain's inner
  applier (`applyNR_base`, from `baseShape`).
- `authApplierV3.Apply.specL`/`wp_latest`: the auth applier's `Apply` with `authIsL`, the latest-state
  resource `L hs` (handed to the `applyFunc` with `A`, or back with a rejection) and an inner
  applier that does not reject; dispatched means `adminPassL`, rejected `adminRejL`.
- `applierAdmL E c a L`: that triple as a persistent fact of an applier value; of the auth applier
  (`applierAdmL_auth`), of the current applier with no alarm set (`applierAdmL_cur`).
- `uberApplier.Apply.adminSpecL`/`wp_adminL`: E2o's admin triple of the uber-applier with the
  current chain the base one (no alarm set), the authority family `Own` lending `L hs` to the
  check (`Own γa h ⊢ L h ∗ (L h -∗ Own γa h)`, the tie-carrying instance's `auth.latestRes_of_T`),
  and the latest-state verdict in the postcondition.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.needAdminPermission
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__Apply
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.ApplyAdmin
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.ApplyKVL
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.AuthApplyLatest
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Packaging

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

/-! ## The verdicts (pure) -/

section pure
variable [GooseExts]

/-- **The admin check passed at the latest state** of `hs` (when the request needs it): the latest
state admits the request's principal (`auth.adminOk`). -/
def apply.adminPassL (M : auth.AuthMode) (hs : List auth.AuthState) (rq : apply.IRRModel) : Prop :=
  apply.needAdminPermission rq = true →
    apply.latestOk M hs (fun stl => auth.adminOk stl (some (auth.authInfoM (apply.principalOf rq))))

/-- **The admin check refused at the latest state** of `hs`: the latest state does not admit the
request's principal. -/
def apply.adminRejL (M : auth.AuthMode) (hs : List auth.AuthState) (rq : apply.IRRModel) : Prop :=
  apply.latestOk M hs (fun stl => ¬ auth.adminOk stl (some (auth.authInfoM (apply.principalOf rq))))

theorem apply.adminPassL_of_not_need (M : auth.AuthMode) (hs : List auth.AuthState)
    (rq : apply.IRRModel) (h : apply.needAdminPermission rq = false) : apply.adminPassL M hs rq := by
  intro h'; rw [h] at h'; cases h'

/-- A check that passed (`err = nil`) at the latest state. -/
theorem apply.adminPassL_of_verdict (M : auth.AuthMode) (hs : List auth.AuthState)
    (rq : apply.IRRModel)
    (hv : auth.adminVerdictL M hs (some (auth.authInfoM (apply.principalOf rq))) GoInterface.nil) :
    apply.adminPassL M hs rq := by
  intro _
  cases M with
  | on γa => intro stl hl; exact (hv stl hl).1 rfl
  | off => trivial
  | any => trivial

/-- A check that refused (`err ≠ nil`) at the latest state. -/
theorem apply.adminRejL_of_verdict (M : auth.AuthMode) (hs : List auth.AuthState)
    (rq : apply.IRRModel) (err : GoInterface) (herr : err ≠ GoInterface.nil)
    (hv : auth.adminVerdictL M hs (some (auth.authInfoM (apply.principalOf rq))) err) :
    apply.adminRejL M hs rq := by
  cases M with
  | on γa => intro stl hl hok; exact herr ((hv stl hl).2 hok)
  | off => trivial
  | any => trivial

end pure

/-! ## The contracts -/

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The auth layer's admin rejection's result** (`apply.rejectResultIs`'s), its error one of the
auth package's error variables (`authApplyErrIs`; the auth plan's E3j: what `IsAdminPermitted`
returns, `isAuthStoreL`), so that it is told apart from `ErrNoSpace`. -/
def apply.rejectResultIsA (ar : Loc) : IProp GF :=
  iprop(⌜ar ≠ null⌝ ∗ ∃ v : go_etcd_io.etcd.server.v3.etcdserver.apply.Result, ar ↦ v ∗
    ⌜v.Err' ≠ GoInterface.nil ∧ v.Resp' = GoInterface.nil⌝ ∗ authApplyErrIs v.Err')

/-- **An admin entry's rejection's error** (read-only; the auth plan's E3j): for a rejected
request, its result's error is one of the auth package's (`authApplyErrIs`). -/
def apply.adminRejErr (ar : Loc) : apply.ApplyOut → IProp GF
  | .rejected => iprop(∃ v : go_etcd_io.etcd.server.v3.etcdserver.apply.Result, ar ↦□ v ∗
      authApplyErrIs v.Err')
  | _ => iprop(True)

instance apply.adminRejErr_persistent (ar : Loc) (out : apply.ApplyOut) :
    Persistent (apply.adminRejErr (GF := GF) ar out) := by
  cases out <;> unfold apply.adminRejErr <;> infer_instance

/-- **An applier of the chain `c` whose `Apply` always runs its `applyFunc`** (persistent): the
`applyFunc` under the chain's resources at the request's principal, its result returned. -/
def apply.applyNR (c : apply.Chain) (a : GoInterface) : IProp GF :=
  iprop(∃ ai : GoInterfaceOk, ⌜a = GoInterface.ok ai⌝ ∗
    □ (∀ (r : Loc) (rq : apply.IRRModel) (skip v3 : Bool) (af : GoFunc) (A : IProp GF)
        (B : Loc → IProp GF),
      {{ apply.irrWrapperIs r rq skip ∗ A ∗
          ({{ apply.chainRes c (.ok ai) (apply.principalOf rq) ∗ A }} (App (App (Val #af) (Val #r)) (Val #v3))
            {{ (ar : Loc), RET #ar; apply.chainResAny c (.ok ai) ∗ B ar }}) }}
        (App (App (App (Val #(methods ai.ty go!"Apply" ai.v)) (Val #r)) (Val #v3)) (Val #af))
      {{ (ar : Loc), RET #ar; B ar }}))

instance apply.applyNR_persistent (c : apply.Chain) (a : GoInterface) :
    Persistent (apply.applyNR (GF := GF) c a) := by
  unfold apply.applyNR; infer_instance

/-- **An applier's `Apply` with the admin check's verdict at the latest state** (persistent): with
the latest-state resource `L hs` (handed to the `applyFunc` with `A`), either the `applyFunc` ran and
the check (if any) passed at the latest state, or the request needed the check, it refused at the
latest state, and `A`, `L hs` come back with the rejection. -/
def apply.applierAdmL (E : apply.AEnv GF) (c : apply.Chain) (a : GoInterface)
    (L : List auth.AuthState → IProp GF) : IProp GF :=
  iprop(∃ ai : GoInterfaceOk, ⌜a = GoInterface.ok ai⌝ ∗
    □ (∀ (r : Loc) (rq : apply.IRRModel) (skip v3 : Bool) (af : GoFunc) (A : IProp GF)
        (B : Loc → IProp GF) (hs : List auth.AuthState),
      {{ apply.irrWrapperIs r rq skip ∗ A ∗ L hs ∗
          ({{ apply.chainRes c (.ok ai) (apply.principalOf rq) ∗ A ∗ L hs }}
              (App (App (Val #af) (Val #r)) (Val #v3))
            {{ (ar : Loc), RET #ar; apply.chainResAny c (.ok ai) ∗ B ar }}) }}
        (App (App (App (Val #(methods ai.ty go!"Apply" ai.v)) (Val #r)) (Val #v3)) (Val #af))
      {{ (ar : Loc), RET #ar;
          (B ar ∗ ⌜apply.adminPassL E.authMode hs rq⌝) ∨
            (⌜apply.needAdminPermission rq = true ∧ apply.adminRejL E.authMode hs rq⌝ ∗ A ∗ L hs ∗
              apply.rejectResultIsA ar) }}))

instance apply.applierAdmL_persistent (E : apply.AEnv GF) (c : apply.Chain) (a : GoInterface)
    (L : List auth.AuthState → IProp GF) : Persistent (apply.applierAdmL E c a L) := by
  unfold apply.applierAdmL; infer_instance

variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **`aa.Apply(r, shouldApplyV3, applyFunc)` with the admin check at the latest state** (see the
file header): `Apply.spec`'s triple with the store's checks at the latest state (`authIsL`), the
inner applier one that does not reject (`applyNR`) and the latest-state resource `L hs`, handed to
the `applyFunc` with `A`; a dispatched request's check (if any) passed at the latest state, a
rejected one refused there. -/
abbrev apply.authApplierV3.Apply.specL : Prop :=
  ∀ (E : apply.AEnv GF) (c : apply.Chain) (inner : GoInterface) (p r : Loc) (rq : apply.IRRModel)
    (skip v3 : Bool) (af : GoFunc) (A : IProp GF) (B : Loc → IProp GF)
    (L : List auth.AuthState → IProp GF) (hs : List auth.AuthState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      apply.authIs E p inner ∗ apply.authIsL E p L ∗ apply.applyNR c inner ∗
      apply.irrWrapperIs r rq skip ∗ A ∗ L hs ∗
      ({{ apply.chainRes (.auth E.authOn c) (interface.mkOk (go.GoType.PointerType authApplierV3.ty) #p)
            (apply.principalOf rq) ∗ A ∗ L hs }}
          (App (App (Val #af) (Val #r)) (Val #v3))
        {{ (ar : Loc), RET #ar; apply.chainResAny (.auth E.authOn c)
            (interface.mkOk (go.GoType.PointerType authApplierV3.ty) #p) ∗ B ar }}) }}
    (App (App (App (Val (p @!! go.GoType.PointerType authApplierV3.ty @!! go!"Apply")) (Val #r)) (Val #v3)) (Val #af))
  {{ (ar : Loc), RET #ar;
      (B ar ∗ ⌜apply.adminPassL E.authMode hs rq⌝) ∨
        (⌜apply.needAdminPermission rq = true ∧ apply.adminRejL E.authMode hs rq⌝ ∗ A ∗ L hs ∗
          apply.rejectResultIsA ar) }}

/-- **`a.Apply(r, shouldApplyV3)` on an admitted admin request with no alarm set, the admin check
at the latest state** (see the file header): E2o's `adminSpec` with the current chain the base one,
the base applier's latest-state `Apply` (`applierAdmL`), the latest-state resource `L` lent by the
authority family `Own` (`hsplit`); besides `adminSpec`'s postcondition (but for `applyAuthRes`, whose
recorded-state verdict the latest one replaces), a dispatched request's check passed at the latest
state and a rejected one's refused there. -/
abbrev apply.uberApplier.Apply.adminSpecL : Prop :=
  ∀ (E : apply.AEnv GF) (p : Loc) (opts : go_etcd_io.etcd.server.v3.etcdserver.apply.ApplierOptions)
    (x : apply.ApplyKV) (r : Loc) (rq : apply.IRRModel) (skip v3 : Bool)
    (Pre Q Post : IProp GF) (W : IProp GF) (γa : auth.AuthNames) (hs : List auth.AuthState)
    (Own : auth.AuthNames → List auth.AuthState → IProp GF) (L : List auth.AuthState → IProp GF),
  (∀ h, Own γa h ⊢ L h ∗ (L h -∗ Own γa h)) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ apply.uberIs E p opts ∗
      apply.irrWrapperIs r rq skip ∗ apply.uberOwn E p x.chain ∗ apply.kvOwn E x.log ∗
      apply.cPre v3 E.P E.f Pre Q Post ∗
      (∃ base : GoInterface, structFieldRef uberApplier go!"applyV3base" p ↦□ base ∗
        apply.applierAdmin E (apply.baseChain E.authOn) base W Own ∗
        apply.applierAdmL E (apply.baseChain E.authOn) base L) ∗
      ⌜E.authMode = .on γa ∧ apply.adminKindOk rq ∧ apply.dispatchOk E.authOn rq ∧
        receiptBound GF ≤ 2 ^ 48⌝ ∗ ⌜skip = true → rq.txn.isSome = true⌝ ∗
      ⌜x.chain = apply.baseChain E.authOn⌝ ∗
      Own γa hs ∗ ⧗ 1 ∗ W }}
    (App (App (Val (p @!! go.GoType.PointerType uberApplier.ty @!! go!"Apply")) (Val #r)) (Val #v3))
  {{ (ar : Loc), RET #ar; ∃ (x' : apply.ApplyKV) (out : apply.ApplyOut),
      apply.uberOwn E p x'.chain ∗ apply.kvOwn E x'.log ∗ apply.cPost v3 Pre Post ∗
      ⌜apply.applyStep rq v3 x x' out ∧ (out = .rejected ∨ ∃ o, out = .dispatched o skip)⌝ ∗
      ⌜(out = .rejected → apply.needAdminPermission rq = true ∧ apply.adminRejL E.authMode hs rq) ∧
        (∀ o, out = .dispatched o skip → apply.adminPassL E.authMode hs rq)⌝ ∗
      apply.resTrace ar ∗ apply.applyResultIs rq v3 x.log ar out ∗ W ∗
      apply.adminOut Own γa E.authMode hs rq v3 ar out ∗ apply.adminRejErr ar out }}

end defs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **The backend applier's `Apply` does not reject** (`applierV3backend.Apply.spec`). -/
theorem apply.applyNR_backend (hApply : apply.applierV3backend.Apply.spec (GF := GF) (hG := hG))
    (p : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ⊢
      apply.applyNR .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) := by
  iintro #Hpkg
  iunfold apply.applyNR
  iexists ⟨go.GoType.PointerType applierV3backend.ty, #p⟩
  isplitr
  · ipureintro; rfl
  iintro !> %r %rq %skip %v3 %af %A %B %Φ' !> ⟨#Hw, HA, #Haf⟩ HΦ'
  iapply (hApply p r v3 af (iprop(apply.chainRes .backend
      (.ok ⟨go.GoType.PointerType applierV3backend.ty, #p⟩) (apply.principalOf rq) ∗ A))
    (fun ar => iprop(apply.chainResAny .backend
      (.ok ⟨go.GoType.PointerType applierV3backend.ty, #p⟩) ∗ B ar))) $$ [HA]
  · iframe #
    iframe HA
    simp only [apply.chainRes]
    ipureintro; trivial
  inext
  iintro %ar ⟨-, HB⟩
  iapply HΦ'
  iexact HB

/-- **A quota applier's `Apply` (its inner applier's, promoted) does not reject** when its inner
applier's does not. -/
theorem apply.applyNR_quota (c : apply.Chain) (p : Loc) (inner : GoInterface) :
    structFieldRef quotaApplierV3 go!"applierV3" p ↦□ inner ∗ apply.applyNR (GF := GF) c inner ⊢
      apply.applyNR (.quota c) (interface.mkOk (go.GoType.PointerType quotaApplierV3.ty) #p) := by
  iintro ⟨#Hf, #Hin⟩
  iunfold apply.applyNR at Hin
  icases Hin with ⟨%bi, %Hbi, #HApply⟩
  subst Hbi
  iunfold apply.applyNR
  iexists ⟨go.GoType.PointerType quotaApplierV3.ty, #p⟩
  isplitr
  · ipureintro; rfl
  iintro !> %r %rq %skip %v3 %af %A %B %Φ' !> ⟨#Hw, HA, #Haf⟩ HΦ'
  rw [method_unfold (t := go.GoType.PointerType quotaApplierV3.ty) (m := go!"Apply")]
  wp_call
  wp_auto
  iapply HApply $$ %r %rq %skip %v3 %af %A %B [HA]
  · iframe HA
    iframe #
    imodintro
    iintro %Φ'' ⟨Hres, HA⟩ HΦ''
    ihave Hres := apply.chainRes_quota_in c p (.ok bi) (apply.principalOf rq) $$ Hf Hres
    iapply Haf $$ [Hres HA]
    · iframe
    inext
    iintro %ar ⟨Hres, HB⟩
    iapply HΦ''
    iframe HB
    iapply apply.chainResAny_quota_out c p (.ok bi) $$ Hf Hres
  inext
  iintro %ar HB
  iapply HΦ'
  iexact HB

/-- **The base chain's inner applier does not reject** (the quota applier over the backend, from
`baseShape`'s fields). -/
theorem apply.applyNR_base (hApply : apply.applierV3backend.Apply.spec (GF := GF) (hG := hG))
    (pq pb : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      structFieldRef quotaApplierV3 go!"applierV3" pq ↦□
        (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #pb : GoInterface) ⊢
      apply.applyNR (.quota .backend) (interface.mkOk (go.GoType.PointerType quotaApplierV3.ty) #pq) := by
  iintro ⟨#Hpkg, #Hf⟩
  ihave #Hb := apply.applyNR_backend hApply pb $$ Hpkg
  iapply apply.applyNR_quota .backend pq _ $$ [Hf Hb]
  iframe #

theorem apply.authApplierV3.Apply.wp_latest
    (hNA : apply.needAdminPermission.spec (GF := GF) (hG := hG)) :
    apply.authApplierV3.Apply.specL (GF := GF) (hG := hG) := by
  intro E c inner p r rq skip v3 af A B L hs
  wp_start as ⟨#Hauth, #HauthL, #Hinner, #Hw, HA, HL, #Haf⟩
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold apply.authIs at Hauth
  icases Hauth with ⟨#Happ, -, -, #Hmu⟩
  iunfold apply.authIsL at HauthL
  icases HauthL with ⟨%st, #Hasf, #Hst⟩
  ihave #Hst' := Hst
  iunfold apply.isAuthStoreL at Hst'
  icases Hst' with ⟨%sti, %Hsti, -, -, -, #HAdmin⟩
  subst Hsti
  ihave #Hin := Hinner
  iunfold apply.applyNR at Hin
  icases Hin with ⟨%bi, %Hbi, #HApplyI⟩
  subst Hbi
  ihave #Hw' := Hw
  iunfold apply.irrWrapperIs at Hw'
  icases Hw' with ⟨%Hrn, %ip, #Hip, #Hirr, #Hskip⟩
  ihave #Hirr' := Hirr
  iunfold apply.internalRaftRequestIs at Hirr'
  icases Hirr' with ⟨%Hipn, -, ⟨%hl, #HH, #Hhdr⟩, -⟩
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinfo, Hard⟩
  iunfold apply.authInfoIdle at Hinfo
  wp_join iprop(structFieldRef authApplierV3 go!"authInfo" p ↦ apply.principalOf rq ∗ aa_ptr ↦ p ∗
      r_ptr ↦ r)
    at (if: _ then _ else _) with [Hinfo aa r] as ⟨Hinfo, aa, r⟩
  · -- the header's principal: with a header its fields, else the zero `AuthInfo`
    cases hh : rq.header with
    | none =>
      have hp : apply.principalOf rq = zeroValDef := by simp [apply.principalOf, hh]
      simp only [apply.optReqIs]
      icases Hhdr with %Hnull
      wp_if_destruct
      · (try wp_auto)
        rw [hp]
        wp_join_done
        (try iframe)
      · exact absurd Hnull Hif
    | some hm =>
      have hp : apply.principalOf rq = ⟨hm.username, hm.authRevision⟩ := by
        simp [apply.principalOf, hh]
      simp only [apply.optReqIs]
      iunfold apply.headerIs at Hhdr
      icases Hhdr with ⟨%Hhn, -, #HU, #HR⟩
      wp_if_destruct
      · exact absurd rfl Hhn
      · (try wp_auto)
        rw [hp]
        isplitr
        · ipureintro; first | rfl | trivial
        iframe aa r
        iExactEq Hinfo
        rfl
  wp_apply (hNA ip rq) $$ [$Hirr] as %b %Hb
  subst Hb
  cases hna : apply.needAdminPermission rq
  · -- no admin check
    wp_auto
    wp_apply HApplyI $$ %r %rq %skip %v3 %af
        %(iprop(A ∗ L hs ∗ structFieldRef authApplierV3 go!"authInfo" p ↦ apply.principalOf rq))
        %(fun ar => iprop(B ar ∗ ∃ i : go_etcd_io.etcd.server.v3.auth.AuthInfo,
          structFieldRef authApplierV3 go!"authInfo" p ↦ i)) [HA HL Hinfo] as %ar ⟨HB, %info2, Hinfo⟩
    · iframe Hw
      isplitl [HA HL Hinfo]
      · iframe HA HL Hinfo
      imodintro
      iintro %Φ'' ⟨Hres, HA, HL, Hi⟩ HΦ''
      ihave Hres := apply.chainResAny_of _ _ _ $$ Hres
      ihave Hres := apply.chainRes_auth_in c p (.ok bi) (apply.principalOf rq) $$ Happ Hi Hres
      iapply Haf $$ [Hres HA HL]
      · iframe
      inext
      iintro %ar ⟨Hres, HB⟩
      iapply HΦ''
      ihave ⟨%i, Hi, Hres⟩ := apply.chainResAny_auth_out c p (.ok bi) $$ Happ Hres
      dsimp only
      iframe Hres HB
      iexists i; iexact Hi
    (try wp_auto)
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hinfo Hard]
    · inext
      iframe Hard
      iunfold apply.authInfoIdle
      iExactEq Hinfo
      first | rfl | (congr 1; cases info2; rfl) | (congr 1; cases info2; simp [zeroValDef])
    iapply HΦ
    ileft
    iframe HB
    ipureintro
    exact apply.adminPassL_of_not_need _ _ _ hna
  wp_auto
  wp_apply HAdmin $$ [$Hinfo $Hard $HL] as %err ⟨Hinfo, Hard, HL, #HeI, %Hv⟩
  cases err with
  | nil =>
    wp_auto
    wp_apply HApplyI $$ %r %rq %skip %v3 %af
        %(iprop(A ∗ L hs ∗ structFieldRef authApplierV3 go!"authInfo" p ↦ apply.principalOf rq))
        %(fun ar => iprop(B ar ∗ ∃ i : go_etcd_io.etcd.server.v3.auth.AuthInfo,
          structFieldRef authApplierV3 go!"authInfo" p ↦ i)) [HA HL Hinfo] as %ar ⟨HB, %info2, Hinfo⟩
    · iframe Hw
      isplitl [HA HL Hinfo]
      · iframe HA HL Hinfo
      imodintro
      iintro %Φ'' ⟨Hres, HA, HL, Hi⟩ HΦ''
      ihave Hres := apply.chainResAny_of _ _ _ $$ Hres
      ihave Hres := apply.chainRes_auth_in c p (.ok bi) (apply.principalOf rq) $$ Happ Hi Hres
      iapply Haf $$ [Hres HA HL]
      · iframe
      inext
      iintro %ar ⟨Hres, HB⟩
      iapply HΦ''
      ihave ⟨%i, Hi, Hres⟩ := apply.chainResAny_auth_out c p (.ok bi) $$ Happ Hres
      dsimp only
      iframe Hres HB
      iexists i; iexact Hi
    (try wp_auto)
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hinfo Hard]
    · inext
      iframe Hard
      iunfold apply.authInfoIdle
      iExactEq Hinfo
      first | rfl | (congr 1; cases info2; rfl) | (congr 1; cases info2; simp [zeroValDef])
    iapply HΦ
    ileft
    iframe HB
    ipureintro
    exact apply.adminPassL_of_verdict _ _ _ Hv
  | ok e =>
    wp_auto
    wp_alloc ar as Har
    ihave ⟨Har, %Harn⟩ := typedPointsto_not_null_dup _ _ _ $$ Har
    wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hinfo Hard]
    · inext
      iframe Hard
      iunfold apply.authInfoIdle
      iExactEq Hinfo
      first | rfl | (congr 1; simp [zeroValDef])
    iapply HΦ
    iright
    iframe HA HL
    isplitr
    · ipureintro
      exact ⟨rfl, apply.adminRejL_of_verdict _ _ _ _ (by simp) Hv⟩
    iunfold apply.rejectResultIsA
    isplitr
    · ipureintro; exact Harn
    iexists _
    iframe Har
    isplitr
    · ipureintro; simp
    iexact HeI

/-- **The auth applier's `Apply` at the latest state** as an applier fact (`applierAdmL`). -/
theorem apply.applierAdmL_auth
    (hApplyL : apply.authApplierV3.Apply.specL (GF := GF) (hG := hG))
    (E : apply.AEnv GF) (c : apply.Chain) (inner : GoInterface) (p : Loc)
    (L : List auth.AuthState → IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      apply.authIs E p inner ∗ apply.authIsL E p L ∗ apply.applyNR c inner ⊢
      apply.applierAdmL E (.auth E.authOn c)
        (interface.mkOk (go.GoType.PointerType authApplierV3.ty) #p) L := by
  iintro ⟨#Hpkg, #Ha, #HaL, #Hnr⟩
  iunfold apply.applierAdmL
  iexists ⟨go.GoType.PointerType authApplierV3.ty, #p⟩
  isplitr
  · ipureintro; rfl
  iintro !> %r %rq %skip %v3 %af %A %B %hs %Φ' !> ⟨#Hw, HA, HL, Haf⟩ HΦ'
  iapply (hApplyL E c inner p r rq skip v3 af A B L hs) $$ [HA HL Haf] HΦ'
  iframe HA HL Haf
  (try iframe #)

/-- **With no alarm set the current applier's latest-state `Apply` is the base applier's**: its
shape (`uberShape`) at the base chain makes it the base applier (`applierKVL_cur`'s). -/
theorem apply.applierAdmL_cur (E : apply.AEnv GF) (p : Loc) (a : GoInterface)
    (L : List auth.AuthState → IProp GF) :
    apply.uberShape E p (apply.baseChain E.authOn) a ∗
      (∃ base : GoInterface, structFieldRef uberApplier go!"applyV3base" p ↦□ base ∗
        apply.applierAdmL E (apply.baseChain E.authOn) base L) ⊢
      apply.applierAdmL E (apply.baseChain E.authOn) a L := by
  iintro ⟨#Hsh, %base, #Hb, #Hkv⟩
  iunfold apply.uberShape at Hsh
  icases Hsh with ⟨%base', %ns, %cr, %Hc, #Hb', #Has⟩
  obtain ⟨rfl, rfl⟩ := apply.alarmChain_eq_base _ _ _ Hc.symm
  icombine Hb Hb' gives %Hbb
  subst Hbb
  iunfold apply.alarmShape at Has
  icases Has with ⟨%a1, #H1, #H2⟩
  iunfold apply.cappedShape at H1
  icases H1 with %Ha1
  iunfold apply.corruptShape at H2
  icases H2 with %Ha
  subst Ha1 Ha
  iexact Hkv

theorem apply.uberApplier.Apply.wp_adminL
    (hD : apply.uberApplier.dispatch.adminSpec (GF := GF) (hG := hG)) :
    apply.uberApplier.Apply.adminSpecL (GF := GF) (hG := hG) := by
  intro E p opts x r rq skip v3 Pre Q Post W γa hs Own L hsplit
  wp_start as ⟨#Hu, #Hw, Hown, Hkv, Hcs, #Hbase, %Hok, %Hskip, %Hch, Ho, Hrc, HW⟩
  ihave #Hpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply $$ []
  · iPkgInit
  icases Hbase with ⟨%base, #Hbf, #Hst, #HstL⟩
  iunfold apply.uberOwn at Hown
  icases Hown with ⟨%a, Ha, #Hs, %HcE, #Hsh⟩
  ihave #Had := apply.applierAdmin_curG E W Own p x.chain a $$ [Hsh]
  · iframe #
    try (iexists base; iframe #)
  ihave #Hsh' : apply.uberShape E p (apply.baseChain E.authOn) a $$ []
  · rw [← Hch]; iexact Hsh
  ihave #HAL : apply.applierAdmL E x.chain a L $$ []
  · rw [Hch]
    iapply apply.applierAdmL_cur
    iframe Hsh'
    try (iexists base; iframe #)
  ihave #Hs' := Hs
  iunfold apply.applierSpec at Hs'
  icases Hs' with ⟨%ai, %Hai, -⟩
  subst Hai
  iunfold apply.applierAdmL at HAL
  icases HAL with ⟨%ai', %Hai', #HApply⟩
  cases Hai'
  ihave ⟨HL, Hback⟩ := hsplit hs $$ Ho
  wp_auto
  iapply wp_fupd
  wp_apply HApply $$ %r %rq %skip %v3
      %(methods (go.GoType.PointerType uberApplier.ty) go!"dispatch" #p)
      %(iprop(structFieldRef uberApplier go!"applyV3" p ↦ (GoInterface.ok ai) ∗ apply.kvOwn E x.log ∗
        apply.cPre v3 E.P E.f Pre Q Post ∗ (L hs -∗ Own γa hs) ∗ ⧗ 1 ∗ W))
      %(fun ar => iprop(structFieldRef uberApplier go!"applyV3" p ↦ (GoInterface.ok ai) ∗
        ∃ o : apply.Outcome, apply.kvOwn E (o.logAfter x.log) ∗ apply.cPost v3 Pre Post ∗
          ⌜apply.dispatchStep x.chain rq v3 x.log o⌝ ∗ apply.resTrace ar ∗
          apply.dispatchResult rq v3 x.log skip ar o ∗ W ∗ apply.adminDone Own γa E.authMode hs rq v3 ar))
      %hs [Ha Hkv Hcs Hback Hrc HW HL] as %ar Hpost
  · iframe Hw Ha Hkv Hcs Hback Hrc HW HL
    imodintro
    iintro %Φ' ⟨Hres, ⟨Ha, Hkv, Hcs, Hback, Hrc, HW⟩, HL⟩ HΦ'
    ihave Ho := Hback $$ HL
    iapply (hD E p opts x.chain (.ok ai) r rq skip v3 x.log Pre Q Post (apply.principalOf rq) W γa hs Own)
      $$ [Hres Ha Hkv Hcs Ho Hrc HW]
    · iframe #
      iframe Hres Ha Hkv Hcs Ho Hrc HW
      ipureintro; exact ⟨Hok, HcE⟩
    inext
    iintro %ar ⟨Hres, Ha, Hrest⟩
    iapply HΦ'
    simp only []
    iframe Hres Ha Hrest
  icases Hpost with (⟨⟨Ha', %o, Hkv, HPP, %Hst', Htr, Hres, HW, Hdone⟩, %Hpass⟩ |
    ⟨%Hrj, ⟨Ha, Hkv, Hcs, Hback, Hrc, HW⟩, HL, Hrej⟩)
  · imodintro
    iapply HΦ
    iexists ⟨o.logAfter x.log, x.chain⟩, (.dispatched o skip)
    simp only [apply.applyResultIs, apply.adminOut, apply.adminRejErr]
    iframe Hkv HPP Htr Hres HW Hdone
    isplitl [Ha']
    · iunfold apply.uberOwn; iexists _; iframe Ha' Hs Hsh; ipureintro; exact HcE
    isplitr
    · ipureintro; exact ⟨⟨Hskip, Hst', rfl, Or.inl rfl⟩, Or.inr ⟨o, rfl⟩⟩
    ipureintro
    refine ⟨fun h => (by cases h), fun _ _ => Hpass⟩
  · ihave Ho := Hback $$ HL
    iunfold apply.rejectResultIsA at Hrej
    icases Hrej with ⟨%Harn, %v, Hv, %Hvf, #HeA⟩
    ihave #HeI := authApplyErrIs_apply _ $$ HeA
    ipersist Hv
    imodintro
    iapply HΦ
    iexists x, .rejected
    simp only [apply.applyResultIs, apply.adminOut]
    iframe Hkv Ho Hrc HW
    isplitl [Ha]
    · iunfold apply.uberOwn; iexists _; iframe Ha Hs Hsh; ipureintro; exact HcE
    isplitl [Hcs]
    · iapply apply.cPost_of_pre
      iapply apply.cPre_pre
      iexact Hcs
    isplitr
    · ipureintro; exact ⟨⟨Hrj.1, rfl⟩, by simp⟩
    isplitr
    · ipureintro
      exact ⟨fun _ => Hrj, fun _ h => by cases h⟩
    isplitl []
    · iapply apply.resTrace_err ar v Hvf.1 $$ Hv
    isplitr
    · iunfold apply.rejectedResultIs
      isplitr
      · ipureintro; exact Harn
      iexists v
      iframe Hv HeI
      ipureintro; exact Hvf
    simp only [apply.adminRejErr]
    iexists v
    iframe Hv HeA

end proof

end EtcdGrove
end Perennial
