/-
**The disabled auth store** (the authstore-noax stage, 2026-11-18; `notes/decisions.md`,
"authstore-noax"). Lean-first (no Rocq counterpart).

`NewAuthStore` with auth off: a store whose `enabled` field is `false` and stays so. Its invariant
(`offInv`) is the store's locks with what they guard and the revision's atomic, nothing of the
history (`authInv`'s mode `off` holds the backend's read contract and the token provider's, which
a disabled store never uses and the server cannot give: `notes/decisions.md`, "authstore-noax").
Go (at the etcd pin, `server/auth/store.go`): every method the server calls with auth off returns
before reading the backend or the token provider once `IsAuthEnabled()` is `false`
(`isOpPermitted`, `IsAdminPermitted`, `AuthInfoFromCtx`, `Close`), and the store's writers of
`enabled` (`AuthEnable`, `AuthDisable`, `Recover`) are not called with auth on, or write `false`
(`Recover` on an image whose auth bucket has no `authEnabled` key).

* `offInv st`: `enabledMu` guarding `enabled` at `false` (all of it: the lock's writers write it
  whole), `rangePermCacheMu` guarding the cache's field, `beMu` guarding half of `be` (the other
  half the caller's, `authBeOn`, which `Recover` takes to replace it), the revision's atomic in an
  invariant, the logger read-only.
* the methods' triples on it: `IsAuthEnabled`, `Revision`, `setRevision`, `isOpPermitted` and the
  three permission checks, `IsAdminPermitted`, `AuthInfoFromCtx`, `Close`, `refreshRangePermCache`
  (on a reader with no user); and, before the invariant is made, `Revision` and `commitRevision` on
  the owned field (`NewAuthStore`'s).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.InvAuth
public import Spec.go_uber_org.zap.Logger__Debug

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace auth

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- What `enabledMu` guards at `q` with auth off: the field `enabled` at `false`. -/
def offEnP (st : Loc) (q : Qp) : IProp GF := iprop(aF go!"enabled" st ↦{DFrac.own q} false)

/-- What `rangePermCacheMu` guards at `q` with auth off: the field `rangePermCache`. -/
def offCaP (st : Loc) (q : Qp) : IProp GF :=
  iprop(∃ mp : GoMap, aF go!"rangePermCache" st ↦{DFrac.own q} mp)

/-- What `beMu` guards at `q` with auth off: half of the field `be` (the other half the caller's,
`authBeOn`). -/
def offBeP (st : Loc) (q : Qp) : IProp GF :=
  iprop(∃ be : AuthBackend, aF go!"be" st ↦{DFrac.own q.half} be)

/-- **The disabled auth store** at `st` (persistent): its three locks' guards, the revision's
atomic, the read-only logger. -/
def offInv (st : Loc) : IProp GF :=
  iprop(⌜st ≠ null⌝ ∗ inv (nroot.@"authRev") (∃ r : w64, aF go!"revision" st ↦ r) ∗
    (∃ lg : Loc, aF go!"lg" st ↦□ lg ∗ zapLoggerOk lg) ∗
    sync.isRWMutexGuard (aF go!"beMu" st) (offBeP st) ∗
    sync.isRWMutexGuard (aF go!"enabledMu" st) (offEnP st) ∗
    sync.isRWMutexGuard (aF go!"rangePermCacheMu" st) (offCaP st))

instance offInv_persistent (st : Loc) : Persistent (offInv (GF := GF) st) := by
  unfold offInv; infer_instance

/-- **A transaction's `UnsafeSaveAuthRevision(rev)` from `Pre` to `Post`.** -/
def saveRevOk (ti : GoInterfaceOk) (rev : w64) (Pre Post : IProp GF) : IProp GF :=
  iprop({{ Pre }} (App (Val #(methods ti.ty go!"UnsafeSaveAuthRevision" ti.v)) (Val #rev))
    {{ RET #(); Post }})

/-- **A reader with no user** (persistent): its `UnsafeGetAllUsers()` returns none under `H`. -/
def getAllUsersNone (ti : GoInterfaceOk) (H : IProp GF) : IProp GF :=
  iprop(□ ({{ H }} (App (Val #(methods ti.ty go!"UnsafeGetAllUsers" ti.v)) (Val #()))
    {{ (s : GoSlice), RET #s; H ∗ s ↦* ([] : List Loc) }}))

instance getAllUsersNone_persistent (ti : GoInterfaceOk) (H : IProp GF) :
    Persistent (getAllUsersNone (GF := GF) ti H) := by
  unfold getAllUsersNone; infer_instance

/-- **A reader's resource of the disabled store**: a slot of `enabledMu` (the request path's
methods read the flag and return). -/
def offRd (st : Loc) : IProp GF := sync.ownRWMutex (aF go!"enabledMu" st) (offEnP st)

end defs

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance offEnP_fractional (st : Loc) : Fractional (offEnP (GF := GF) st) := by
  unfold offEnP
  constructor
  intro q1 q2
  exact typedPointsto_frac_add _ _ q1 q2

instance offCaP_fractional (st : Loc) : Fractional (offCaP (GF := GF) st) := by
  unfold offCaP
  exact fractional_exists_agree
    (fun (mp : GoMap) q => iprop(aF go!"rangePermCache" st ↦{DFrac.own q} mp))
    (fun mp => ⟨fun q1 q2 => typedPointsto_frac_add _ _ q1 q2⟩)
    (fun x y q1 q2 => by
      iintro ⟨H1, H2⟩
      icombine H1 H2 gives %Heq
      ipureintro; exact Heq)

theorem Qp.half_add' (p q : Qp) : (p + q).half = p.half + q.half := Subtype.ext (by grind)

instance offBeP_fractional (st : Loc) : Fractional (offBeP (GF := GF) st) := by
  unfold offBeP
  exact fractional_exists_agree
    (fun (be : AuthBackend) q => iprop(aF go!"be" st ↦{DFrac.own q.half} be))
    (fun be => ⟨fun q1 q2 => by
      rw [Qp.half_add']
      exact typedPointsto_frac_add _ _ q1.half q2.half⟩)
    (fun x y q1 q2 => by
      iintro ⟨H1, H2⟩
      icombine H1 H2 gives %Heq
      ipureintro; exact Heq)

end lemmas

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- `as.IsAuthEnabled()` of the disabled store: `false`. -/
theorem isAuthEnabled_off (st : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ offInv st ∗ offRd st }}
      (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"IsAuthEnabled")) (Val #()))
    {{ (b : Bool), RET #b; offRd st ∗ ⌜b = false⌝ }} := by
  wp_start as ⟨#Hinv, Hrd⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold offRd at Hrd
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.RWMutex.wp_RLock $$ [$Hrd] as ⟨Hlk, HP⟩
  iunfold offEnP at HP
  (try wp_auto)
  wp_apply sync.RWMutex.wp_RUnlock $$ [$Hlk HP] as Hrd
  · inext; iunfold offEnP; iexact HP
  iapply HΦ
  iunfold offRd
  iframe Hrd
  ipureintro; rfl

/-- `as.Revision()` of the disabled store: some value. -/
theorem revision_off (st : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ offInv st }}
      (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"Revision")) (Val #()))
    {{ (x : w64), RET #x; True }} := by
  wp_start as #Hinv
  ihave #Hatomic : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  iunfold offInv at Hinv
  icases Hinv with ⟨%Hst, #Hrev, -⟩
  wp_auto
  wp_apply_core sync.atomic.wp_LoadUint64 $$ [] [HΦ «$res0»]
  · iexact Hatomic
  iinv Hrev with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  icases Hi with ⟨%r, Hr⟩
  iexists r
  iframe Hr
  iintro Hr
  imod Hmask with -
  imod Hclose $$ [Hr] with -
  · inext; iexists r; iexact Hr
  imodintro
  wp_auto
  iapply HΦ
  itrivial

/-- `as.Revision()` on the owned field (before the invariant is made). -/
theorem revision_own (st : Loc) (r : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ aF go!"revision" st ↦ r }}
      (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"Revision")) (Val #()))
    {{ RET #r; aF go!"revision" st ↦ r }} := by
  wp_start as Hr
  ihave #Hatomic : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  wp_auto
  wp_apply_core sync.atomic.wp_LoadUint64 $$ [] [HΦ «$res0» Hr]
  · iexact Hatomic
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists r
  iframe Hr
  iintro Hr
  imod Hmask with -
  imodintro
  wp_auto
  iapply HΦ $$ Hr

/-- `as.setRevision(rev)` of the disabled store. -/
theorem setRevision_off (st : Loc) (rev : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ offInv st }}
      (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"setRevision")) (Val #rev))
    {{ RET #(); True }} := by
  wp_start as #Hinv
  ihave #Hatomic : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  iunfold offInv at Hinv
  icases Hinv with ⟨%Hst, #Hrev, -⟩
  wp_auto
  wp_apply_core sync.atomic.wp_StoreUint64 $$ [] [HΦ]
  · iexact Hatomic
  iinv Hrev with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  icases Hi with ⟨%r, Hr⟩
  iexists r
  iframe Hr
  iintro Hr
  imod Hmask with -
  imod Hclose $$ [Hr] with -
  · inext; iexists rev; iexact Hr
  imodintro
  wp_auto
  iapply HΦ
  itrivial

/-- `as.commitRevision(tx)` on the owned field (`NewAuthStore`'s, before the invariant is made):
the field at `r + 1`, and the transaction's `UnsafeSaveAuthRevision(r + 1)` contract from `Pre` to
`Post`. -/
theorem commitRevision_own (st : Loc) (r : w64) (ti : GoInterfaceOk) (Pre Post : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ aF go!"revision" st ↦ r ∗
        Pre ∗ saveRevOk ti (r + W64 1) Pre Post }}
      (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"commitRevision"))
        (Val #(GoInterface.ok ti)))
    {{ RET #(); aF go!"revision" st ↦ (r + W64 1) ∗ Post }} := by
  wp_start as ⟨Hr, HPre, HS⟩
  ihave #Hatomic : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  wp_auto
  wp_apply_core sync.atomic.wp_AddUint64 $$ [] [-Hatomic]
  · iexact Hatomic
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists r
  iframe Hr
  iintro Hr
  imod Hmask with -
  imodintro
  wp_auto
  wp_apply (revision_own st (r + W64 1)) $$ [$Hpkg $Hr] as Hr
  (try wp_auto)
  iunfold saveRevOk at HS
  wp_bind (App (Val #(methods ti.ty go!"UnsafeSaveAuthRevision" ti.v)) (Val #(r + W64 1)))
  iapply HS $$ HPre
  inext
  iintro HPost
  (try wp_auto)
  iapply HΦ
  iframe

/-- `as.isOpPermitted(...)` of the disabled store: `nil` (it returns at `!as.IsAuthEnabled()`). -/
theorem isOpPermitted_off (st : Loc) (u : GoString) (rev : w64) (key re : GoSlice)
    (pt : go_etcd_io.etcd.api.v3.authpb.Permission_Type) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ offInv st ∗ offRd st }}
      (App (App (App (App (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"isOpPermitted"))
        (Val #u)) (Val #rev)) (Val #key)) (Val #re)) (Val #pt))
    {{ (err : GoInterface), RET #err; offRd st ∗ ⌜err = GoInterface.nil⌝ }} := by
  wp_start as ⟨#Hinv, Hrd⟩
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply (isAuthEnabled_off st) $$ [$Hpkg $Hinv $Hrd] as %en ⟨Hrd, %Hen⟩
  subst Hen
  wp_auto
  iapply HΦ
  iframe Hrd
  ipureintro; rfl

/-- `as.IsPutPermitted(authInfo, key)` of the disabled store: `nil`. -/
theorem isPutPermitted_off (st a : Loc) (info : AuthInfo) (dq : DFrac) (key : GoSlice) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ offInv st ∗ offRd st ∗
        a ↦{dq} info }}
      (App (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"IsPutPermitted")) (Val #a))
        (Val #key))
    {{ (err : GoInterface), RET #err; offRd st ∗ a ↦{dq} info ∗ ⌜err = GoInterface.nil⌝ }} := by
  wp_start as ⟨#Hinv, Hrd, Ha⟩
  ihave %Hann := typedPointsto_not_null $$ Ha
  iStructNamed Ha
  wp_auto
  wp_apply (isOpPermitted_off st info.Username' info.Revision' key slice.nil (W32 1))
    $$ [$Hpkg $Hinv $Hrd] as %err ⟨Hrd, %Herr⟩
  ihave Ha : a ↦{dq} info $$ [Username Revision]
  · iapply typedPointsto_combine a info dq Hann
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  iapply HΦ
  iframe
  ipureintro; exact Herr

/-- `as.IsRangePermitted(authInfo, key, rangeEnd)` of the disabled store: `nil`. -/
theorem isRangePermitted_off (st a : Loc) (info : AuthInfo) (dq : DFrac) (key re : GoSlice) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ offInv st ∗ offRd st ∗
        a ↦{dq} info }}
      (App (App (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"IsRangePermitted"))
        (Val #a)) (Val #key)) (Val #re))
    {{ (err : GoInterface), RET #err; offRd st ∗ a ↦{dq} info ∗ ⌜err = GoInterface.nil⌝ }} := by
  wp_start as ⟨#Hinv, Hrd, Ha⟩
  ihave %Hann := typedPointsto_not_null $$ Ha
  iStructNamed Ha
  wp_auto
  wp_apply (isOpPermitted_off st info.Username' info.Revision' key re (W32 0))
    $$ [$Hpkg $Hinv $Hrd] as %err ⟨Hrd, %Herr⟩
  ihave Ha : a ↦{dq} info $$ [Username Revision]
  · iapply typedPointsto_combine a info dq Hann
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  iapply HΦ
  iframe
  ipureintro; exact Herr

/-- `as.IsDeleteRangePermitted(authInfo, key, rangeEnd)` of the disabled store: `nil`. -/
theorem isDeleteRangePermitted_off (st a : Loc) (info : AuthInfo) (dq : DFrac) (key re : GoSlice) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ offInv st ∗ offRd st ∗
        a ↦{dq} info }}
      (App (App (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"IsDeleteRangePermitted"))
        (Val #a)) (Val #key)) (Val #re))
    {{ (err : GoInterface), RET #err; offRd st ∗ a ↦{dq} info ∗ ⌜err = GoInterface.nil⌝ }} := by
  wp_start as ⟨#Hinv, Hrd, Ha⟩
  ihave %Hann := typedPointsto_not_null $$ Ha
  iStructNamed Ha
  wp_auto
  wp_apply (isOpPermitted_off st info.Username' info.Revision' key re (W32 1))
    $$ [$Hpkg $Hinv $Hrd] as %err ⟨Hrd, %Herr⟩
  ihave Ha : a ↦{dq} info $$ [Username Revision]
  · iapply typedPointsto_combine a info dq Hann
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  iapply HΦ
  iframe
  ipureintro; exact Herr

/-- `as.IsAdminPermitted(authInfo)` of the disabled store, `authInfo` any (`nil` too): `nil`. -/
theorem isAdminPermitted_off (st a : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ offInv st ∗ offRd st }}
      (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"IsAdminPermitted")) (Val #a))
    {{ (err : GoInterface), RET #err; offRd st ∗ ⌜err = GoInterface.nil⌝ }} := by
  wp_start as ⟨#Hinv, Hrd⟩
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply (isAuthEnabled_off st) $$ [$Hpkg $Hinv $Hrd] as %en ⟨Hrd, %Hen⟩
  subst Hen
  wp_auto
  iapply HΦ
  iframe Hrd
  ipureintro; rfl

/-- `as.AuthInfoFromCtx(ctx)` of the disabled store: `nil, nil`. -/
theorem authInfoFromCtx_off (st : Loc) (ctx : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ offInv st ∗ offRd st }}
      (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"AuthInfoFromCtx")) (Val #ctx))
    {{ (a : Loc) (err : GoInterface), RET (PairV #a #err); offRd st ∗
        ⌜a = null ∧ err = GoInterface.nil⌝ }} := by
  wp_start as ⟨#Hinv, Hrd⟩
  wp_auto
  wp_apply (isAuthEnabled_off st) $$ [$Hpkg $Hinv $Hrd] as %en ⟨Hrd, %Hen⟩
  subst Hen
  wp_auto
  iapply HΦ
  iframe Hrd
  ipureintro; exact ⟨rfl, rfl⟩

/-- `as.Close()` of the disabled store: `nil` (it reads `enabled`, `false`, under `enabledMu`'s
write lock and returns). -/
theorem close_off (st : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ offInv st }}
      (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"Close")) (Val #()))
    {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil⌝ }} := by
  wp_start as #Hinv
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hinv' := Hinv
  iunfold offInv at Hinv'
  icases Hinv' with ⟨%Hst, -, -, -, #Hguard, -⟩
  (try wp_auto)
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hguard] as ⟨Hlk, HP⟩
  iunfold offEnP at HP
  (try wp_auto)
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk HP]
  · inext; iunfold offEnP; iexact HP
  (try wp_auto)
  iapply HΦ
  ipureintro; rfl

/-- `as.refreshRangePermCache(tx)` of the disabled store on a reader `ti` whose
`UnsafeGetAllUsers()` returns no user under `H` (the cache map replaced by an empty one). -/
theorem refreshRangePermCache_off (h_Debug : zap.Logger.Debug.spec (GF := GF) (hG := hG))
    (st : Loc) (ti : GoInterfaceOk) (H : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ offInv st ∗ H ∗
        getAllUsersNone ti H }}
      (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"refreshRangePermCache"))
        (Val #(GoInterface.ok ti)))
    {{ RET #(); H }} := by
  wp_start as ⟨#Hinv, HH, #HGA⟩
  iunfold getAllUsersNone at HGA
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Hinv' := Hinv
  iunfold offInv at Hinv'
  icases Hinv' with ⟨%Hst, -, ⟨%lg, #Hlg, #Hlgnn⟩, -, -, #Hguard⟩
  (try wp_auto)
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hguard] as ⟨Hlk, HP⟩
  iunfold offCaP at HP
  icases HP with ⟨%mp0, HP⟩
  (try wp_auto)
  wp_apply h_Debug
  · iexact Hlgnn
  (try wp_auto)
  wp_apply (wp_map_make1 (K := GoString) (V := Loc) go.string
    (go.GoType.PointerType unifiedRangePermissions.ty)) as %mp HM
  (try wp_auto)
  wp_bind (App (Val #(methods ti.ty go!"UnsafeGetAllUsers" ti.v)) (Val #()))
  iapply HGA $$ HH
  inext
  iintro %s ⟨HH, Hs⟩
  (try wp_auto)
  ihave %Hslen := ownSlice_len s _ _ $$ Hs
  -- no user: the loop exits at once
  ihave IH : iprop(∃ (k : w64) (ux : Loc),
      "i" ∷ i_ptr ↦ k ∗ "user" ∷ user_ptr ↦ ux ∗ "%Hk" ∷ ⌜k = W64 0⌝) $$ [i user]
  · iexists W64 0, _
    iframe
    ipureintro; rfl
  irename : (as_ptr ↦ st : IProp GF) => Has
  wp_for IH
  wp_if_destruct
  · exfalso
    have hlt : sint.Z k < sint.Z s.len := by
      first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
    have h0 : sint.Z s.len = 0 := by have := Hslen.1; simp at this; word
    subst Hk
    rw [h0] at hlt
    exact absurd hlt (by decide)
  (try wp_auto)
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk HP]
  · inext; iunfold offCaP; iexists mp; iexact HP
  (try wp_auto)
  iapply HΦ $$ HH

end proof

end auth
end EtcdGrove
end Perennial
