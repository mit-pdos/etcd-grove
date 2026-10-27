/-
**The checks at the latest state** (the auth plan's E2r, 2026-10-26; `notes/decisions.md`, "E2r of
the auth plan"). The checks' specs (`isOpPermitted`, `IsAdminPermitted`, ...) give their verdict
at *some* recorded state per read (S3: `permVerdict`, `adminVerdict`), all a concurrent reader can
be promised. The apply thread is the store's only writer and holds the admin side's authority
(`authOwn`, S4f) between its batch transactions, so its own checks can be promised the latest state
of that authority (`histLast`): this file states and proves those variants beside the generic
specs, over the backend's read contract at the latest state (`authReadTxOk`'s second clause).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__lockedReadTx
public import Proof.go_etcd_io.etcd.server.v3.auth.VerdictLemmas
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__IsAuthEnabled
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__Revision
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__isOpPermitted
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__isRangeOpPermitted
public import Spec.go_etcd_io.etcd.server.v3.auth.checkKeyInterval
public import Spec.go_etcd_io.etcd.server.v3.auth.checkKeyPoint
public import Spec.go_etcd_io.etcd.server.v3.auth.hasRootRole
public import Spec.go_uber_org.zap.ByteString
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Logger__Error
public import Spec.go_uber_org.zap.Logger__Warn
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Uint64

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth auth

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- `as.lockedReadTx()` for a caller holding the admin side's authority `hs` (the apply thread):
the locked read transaction is at the latest state (`authReadTxLockedL`); the authority back. -/
abbrev auth.authStore.lockedReadTx.specL : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : auth.AuthMode) (hs : List auth.AuthState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗
      beRd st R M ∗ R ∗ authOwn M hs }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"lockedReadTx")) (Val #()))
  {{ (tx : GoInterface), RET #tx; beRd st R M ∗ authReadTxLockedL tx R M hs ∗ authOwn M hs }}

end spec

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem auth.authStore.lockedReadTx.wp_latest :
    auth.authStore.lockedReadTx.specL (GF := GF) (hG := hG) := by
  intro st R M hs
  wp_start as ⟨#Hinv, Hrd, HR, Hown⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold authInv at Hinv
  icases Hinv with ⟨%Hst, -, -, -, -, -, -⟩
  iunfold beRd at Hrd
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.RWMutex.wp_RLock $$ [$Hrd] as ⟨Hlk, HP⟩
  iunfold beP at HP
  icases HP with ⟨%be, Hbe, #Hbeok⟩
  ihave #Hbeok' := Hbeok
  iunfold authBackendOk at Hbeok'
  icases Hbeok' with ⟨%bi, %Hbi, #HRT⟩
  subst Hbi
  wp_auto
  wp_apply HRT as %tx Htx
  iunfold authReadTxOk at Htx
  icases Htx with ⟨%ti, %Hti, Htx⟩
  subst Hti
  icases Htx with ⟨%Hs, -, #HRL, -, #Hreads⟩
  wp_auto
  wp_bind (App (Val #(methods ti.ty go!"RLock" ti.v)) (Val #()))
  iapply HRL $$ %hs [HR Hown]
  · iframe HR Hown
  inext
  iintro ⟨%sta, Htok, #Hsnap, Hown, %Hlast⟩
  (try wp_auto)
  wp_apply sync.RWMutex.wp_RUnlock $$ [$Hlk Hbe] as Hrd
  · inext; iunfold beP; iexists _; iframe Hbe; iexact Hbeok
  iapply HΦ
  iunfold beRd
  iframe Hrd Hown
  iunfold authReadTxLockedL
  iexists ti
  isplitr
  · ipureintro; rfl
  iexists sta, Hs
  iframe Htok
  iframe #
  ipureintro; exact Hlast

end proof

namespace auth

/-! ## The verdicts at the latest state (pure) -/

section pure
variable [ext : FfiSyntax]

/-- **The tie of the admin side's halves to the latest state** of `hs` (the auth plan's E2r): in
`on γa`, the flag's half holds the latest state's flag, while auth is enabled the cache's half
is the latest state's cache, and always the cache's state has the latest state's permissions
(`permView`, the auth plan's E3j: every admin operation but `RoleAdd`, which adds a role without
permissions, and `AuthDisable`, which changes no user or role, refreshes the cache from the state it
commits, whatever the flag). (What the apply thread's resource is to keep across its steps: they
set the flag at `AuthEnable`/`AuthDisable` and refresh the cache from the state they commit.) -/
def latestTie (M : AuthMode) (hs : List AuthState) (b : Bool) (sc : AuthState) : Prop :=
  match M with
  | .on _ => ∀ stl, hs.getLast? = some stl →
      b = stl.enabled ∧ (b = true → sc = stl) ∧ permView sc = permView stl
  | _ => True

/-- **`isRangeOpPermitted`'s verdict at the cache's state `sc`** (pure): for a request of the shape
the cache decides, at a state with valid permission keys, the check passes exactly when the user
exists at `sc` with permissions covering the request. -/
def cacheVerdictP (sc : AuthState) (user k e : GoString)
    (pt : go_etcd_io.etcd.api.v3.authpb.Permission_Type) (b : Bool) : Prop :=
  k ≠ [] → (e = [] ∨ isOpenEnded e ∨ go.GoStringLt k e) → permKeysOk sc →
    (b = true ↔ ∃ roles, sc.users !! user = some roles ∧
      (if e = [] then coversPoint sc roles (permOp pt) k else coversRange sc roles (permOp pt) k e))

/-- **A permission check's verdict at the latest state** of the admin side's authority `hs` (pure;
the auth plan's E2r): in `on γa`, at the latest state `stl` a passing check is the principal
permitted there with a revision not below `stl`'s (or auth disabled), a refusing one the refusal
at `stl` in each of the four reads (`refusedV`); in `off` the check passes; in `any` nothing. -/
def permVerdictL (M : AuthMode) (hs : List AuthState) (ai : AuthInfoM) (key rangeEnd : GoString)
    (op : PermType) (err : GoInterface) : Prop :=
  match M with
  | .on _ => ∀ stl, hs.getLast? = some stl →
      (err = GoInterface.nil → permitted stl ai key rangeEnd op ∧
        (stl.enabled = false ∨ stl.revision ≤ ai.rev)) ∧
      (err ≠ GoInterface.nil → refusedV ⟨stl, stl, stl, stl⟩ ai key rangeEnd op)
  | .off => err = GoInterface.nil
  | .any => True

/-- For a request of the shape the cache decides, the latest verdict is exact: the check passes
iff the principal is permitted at the latest state and its revision is not stale. -/
theorem permVerdictL_iff (γa : AuthNames) (hs : List AuthState) (ai : AuthInfoM)
    (key rangeEnd : GoString) (op : PermType) (err : GoInterface) (stl : AuthState)
    (hl : hs.getLast? = some stl) (hsh : reqShape key rangeEnd)
    (h : permVerdictL (.on γa) hs ai key rangeEnd op err) :
    err = GoInterface.nil ↔
      permitted stl ai key rangeEnd op ∧ (stl.enabled = false ∨ stl.revision ≤ ai.rev) := by
  obtain ⟨hp, hr⟩ := h stl hl
  constructor
  · exact hp
  · intro ⟨hpm, hrev⟩
    refine Classical.byContradiction fun hne => ?_
    have hrf := (refusedV_diag stl ai key rangeEnd op hsh).1 (hr hne)
    rcases hrf with hn | ⟨he, hlt⟩
    · exact hn hpm
    · rcases hrev with h1 | h1
      · rw [he] at h1; cases h1
      · omega

theorem cacheVerdictP_entry (sc : AuthState) (user k e : GoString)
    (pt : go_etcd_io.etcd.api.v3.authpb.Permission_Type) (b : Bool) (Lr Lw : List adt.Entry)
    (hpt : pt = W32 0 ∨ pt = W32 1) (Hent : cacheEntryIs sc user Lr Lw)
    (hb : k ≠ [] → (e = [] ∨ isOpenEnded e ∨ go.GoStringLt k e) →
      (b = true ↔ if e = [] then ∃ z ∈ (if pt = W32 0 then Lr else Lw), adt.inIvl z.1 k
        else ∀ x, adt.inIvl (queryIvl k e) x →
          ∃ z ∈ (if pt = W32 0 then Lr else Lw), adt.inIvl z.1 x)) :
    cacheVerdictP sc user k e pt b := by
  intro hk hr hkeys
  obtain ⟨roles, hroles, hLr, hLw⟩ := Hent
  rw [hb hk hr]
  have hL : ((if pt = W32 0 then Lr else Lw).map Prod.fst).Perm
      (ivlsOf (permOp pt) (userPerms sc roles)) := by
    unfold permOp
    rcases hpt with rfl | rfl
    · simp only [↓reduceIte]; exact hLr
    · rw [if_neg (by word), if_neg (by word)]; exact hLw
  have hiff : ∀ roles', sc.users !! user = some roles' ↔ roles' = roles := by
    intro roles'; rw [hroles]; constructor
    · intro h; cases h; rfl
    · rintro rfl; rfl
  simp only [hiff, exists_eq_left]
  by_cases he : e = []
  · simp only [he, ↓reduceIte]
    rw [coversPoint_iff sc roles (permOp pt) k hkeys]
    exact exists_inIvl_perm hL k
  · simp only [he, ↓reduceIte]
    rw [coversRange_iff sc roles (permOp pt) k e hk he hkeys]
    constructor
    · intro H x hx; exact (exists_inIvl_perm hL x).1 (H x hx)
    · intro H x hx; exact (exists_inIvl_perm hL x).2 (H x hx)

theorem cacheVerdictP_absent (sc : AuthState) (Mp : GMap GoString Loc) (user k e : GoString)
    (pt : go_etcd_io.etcd.api.v3.authpb.Permission_Type)
    (hdom : ∀ u, (Mp !! u).isSome ↔ (sc.users !! u).isSome) (h : Mp !! user = none) :
    cacheVerdictP sc user k e pt false := by
  intro _ _ _
  have hu : sc.users !! user = none := by
    have hd := hdom user
    rw [h] at hd
    cases hs : sc.users !! user with
    | none => rfl
    | some r => rw [hs] at hd; simp at hd
  simp only [hu, Bool.false_eq_true, false_iff, not_exists, not_and]
  intro _ hr; cases hr

/-- `!as.IsAuthEnabled()` at the latest flag (`on`): the check passes, auth disabled at the latest
state. -/
theorem permVerdictL_on_disabled (γa : AuthNames) (hs : List AuthState) (sc : AuthState)
    (ai : AuthInfoM) (key rangeEnd : GoString) (op : PermType)
    (ht : latestTie (.on γa) hs false sc) :
    permVerdictL (.on γa) hs ai key rangeEnd op GoInterface.nil := by
  intro stl hl
  have he := (ht stl hl).1
  exact ⟨fun _ => ⟨Or.inl he.symm, Or.inl he.symm⟩, fun h => absurd rfl h⟩

/-- A refusal at the latest state (`on`), auth enabled there, for one of `refusedV`'s reasons. -/
theorem permVerdictL_on_refused (γa : AuthNames) (hs : List AuthState) (sc : AuthState)
    (ai : AuthInfoM) (key rangeEnd : GoString) (op : PermType) (err : GoInterface)
    (herr : err ≠ GoInterface.nil) (ht : latestTie (.on γa) hs true sc)
    (hwhy : ∀ stl, hs.getLast? = some stl → sc = stl →
      ai.rev = 0 ∨ ai.rev < stl.revision ∨
        ∀ u, stl.users !! ai.user = some u → ¬ isRoot u ∧
          (reqShape key rangeEnd →
            ∀ u', stl.users !! ai.user = some u' → ¬ covers stl u' op key rangeEnd)) :
    permVerdictL (.on γa) hs ai key rangeEnd op err := by
  intro stl hl
  obtain ⟨he, hc, -⟩ := ht stl hl
  refine ⟨fun h => absurd h herr, fun _ => ?_⟩
  exact ⟨he.symm, hwhy stl hl (hc rfl)⟩

/-- A pass at the latest state (`on`): auth enabled, the token's revision not below the latest's,
the user present there, root or (for a request of the cache's shape) covered there. -/
theorem permVerdictL_on_pass (γa : AuthNames) (hs : List AuthState) (sc : AuthState)
    (ai : AuthInfoM) (key rangeEnd : GoString) (op : PermType)
    (ht : latestTie (.on γa) hs true sc)
    (hok : ∀ stl, hs.getLast? = some stl → sc = stl →
      ai.rev ≠ 0 ∧ stl.revision ≤ ai.rev ∧ ∃ u, stl.users !! ai.user = some u ∧
        (isRoot u ∨ (reqShape key rangeEnd → covers stl u op key rangeEnd))) :
    permVerdictL (.on γa) hs ai key rangeEnd op GoInterface.nil := by
  intro stl hl
  obtain ⟨-, hc, -⟩ := ht stl hl
  obtain ⟨h0, hrev, u, hu, hcov⟩ := hok stl hl (hc rfl)
  exact ⟨fun _ => ⟨Or.inr ⟨h0, u, hu, hcov⟩, Or.inr hrev⟩, fun h => absurd rfl h⟩

/-- The cache's refusal at `stl`, for a request of the cache's shape: no user of the name with
covering permissions. -/
theorem cacheVerdictP_false_not_covers (stl : AuthState) (user k e : GoString)
    (pt : go_etcd_io.etcd.api.v3.authpb.Permission_Type)
    (hc : cacheVerdictP stl user k e pt false) (hkeys : permKeysOk stl)
    (hsh : reqShape k e) (u' : User) (hu : stl.users !! user = some u') :
    ¬ covers stl u' (permOp pt) k e := by
  intro hcov
  have := (hc hsh.1 hsh.2 hkeys).2 ⟨u', hu, by unfold covers at hcov; exact hcov⟩
  cases this

/-- The cache's pass at `stl`, for a request of the cache's shape: the user's permissions cover
it. -/
theorem cacheVerdictP_true_covers (stl : AuthState) (user k e : GoString)
    (pt : go_etcd_io.etcd.api.v3.authpb.Permission_Type)
    (hc : cacheVerdictP stl user k e pt true) (hkeys : permKeysOk stl)
    (hsh : reqShape k e) (u : User) (hu : stl.users !! user = some u) :
    covers stl u (permOp pt) k e := by
  obtain ⟨u', hu', hcov⟩ := (hc hsh.1 hsh.2 hkeys).1 rfl
  rw [hu] at hu'; cases hu'
  unfold covers; exact hcov

end pure

end auth

/-! ## The checks' specs at the latest state -/

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- `as.IsAuthEnabled()` for a caller holding the admin side's half of the flag at `b` (`flagAt`):
it returns `b` (the guard's half agrees), with the mode's verdict. -/
abbrev auth.authStore.IsAuthEnabled.specL : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : auth.AuthMode) (b : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗
      enabledRd st M ∗ flagAt st M b }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"IsAuthEnabled")) (Val #()))
  {{ (en : Bool), RET #en; enabledRd st M ∗ flagAt st M b ∗ enabledVerdict M en ∗ ⌜en = b⌝ }}

/-- `as.isRangeOpPermitted(user, key, rangeEnd, pt)` for a caller holding the admin side's half of
the cache at the state `sc` (`cacheAt`): the verdict at `sc` (`cacheVerdictP`; the guard's map is
the admin side's). -/
abbrev auth.authStore.isRangeOpPermitted.specL : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : auth.AuthMode) (sc : auth.AuthState) (user : GoString)
    (key re : GoSlice) (k e : GoString) (dk de : DFrac)
    (pt : go_etcd_io.etcd.api.v3.authpb.Permission_Type),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗
      cacheRd st M ∗ cacheAt st M sc ∗ key ↦*{dk} k ∗ re ↦*{de} e ∗ ⌜permTypOk pt⌝ ∗
      ⌜sint.Z key.len < 2 ^ 63 - 1⌝ }}
    (App (App (App (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"isRangeOpPermitted"))
      (Val #user)) (Val #key)) (Val #re)) (Val #pt))
  {{ (b : Bool), RET #b; cacheRd st M ∗ cacheAt st M sc ∗ key ↦*{dk} k ∗ re ↦*{de} e ∗
      ⌜cacheVerdictP sc user k e pt b⌝ }}

/-- `as.isOpPermitted(...)` on the apply thread: with the admin side's authority `hs`, its halves of
the flag (at `b`) and of the cache (at `sc`) tied to the latest state (`latestTie`), the verdict is
the latest state's (`permVerdictL`); the resources back. -/
abbrev auth.authStore.isOpPermitted.specL : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : auth.AuthMode) (hs : List auth.AuthState) (b : Bool)
    (sc : auth.AuthState) (info : AuthInfo) (key re : GoSlice) (k e : List w8) (dk de : DFrac)
    (pt : go_etcd_io.etcd.api.v3.authpb.Permission_Type),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗
      authRd st R M ∗ key ↦*{dk} k ∗ re ↦*{de} e ∗ ⌜permTypOk pt⌝ ∗
      ⌜sint.Z key.len < 2 ^ 63 - 1⌝ ∗ authOwn M hs ∗ flagAt st M b ∗ cacheAt st M sc ∗
      ⌜latestTie M hs b sc⌝ }}
    (App (App (App (App (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"isOpPermitted"))
      (Val #info.Username')) (Val #info.Revision')) (Val #key)) (Val #re)) (Val #pt))
  {{ (err : GoInterface), RET #err; authRd st R M ∗ key ↦*{dk} k ∗ re ↦*{de} e ∗ authErrIs err ∗
      authOwn M hs ∗ flagAt st M b ∗ cacheAt st M sc ∗
      ⌜permVerdictL M hs (authInfoM info) k e (permOp pt) err⌝ }}

end spec

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem enabledVerdict_true_ne_off (M : AuthMode) :
    enabledVerdict (GF := GF) M true ⊢ ⌜M ≠ .off⌝ := by
  cases M with
  | off => unfold enabledVerdict; iintro %H; cases H
  | any => iintro -; ipureintro; nofun
  | on γa => iintro -; ipureintro; nofun

theorem auth.authStore.IsAuthEnabled.wp_latest :
    auth.authStore.IsAuthEnabled.specL (GF := GF) (hG := hG) := by
  intro st R M b
  wp_start as ⟨#Hinv, Hrd, Hfl⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold authInv at Hinv
  icases Hinv with ⟨%Hst, -, -, -, -, -, -⟩
  iunfold enabledRd at Hrd
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.RWMutex.wp_RLock $$ [$Hrd] as ⟨Hlk, HP⟩
  iunfold enabledP at HP
  icases HP with ⟨%b', Hb, #Hv, Hg⟩
  iunfold flagAt at Hfl
  icases Hfl with ⟨Hfl, HflQ⟩
  icombine Hb Hfl gives %Heq
  (try wp_auto)
  wp_apply sync.RWMutex.wp_RUnlock $$ [$Hlk Hb Hg] as Hrd
  · inext; iunfold enabledP; iexists b'; iframe Hb Hg; iexact Hv
  iapply HΦ
  iunfold enabledRd
  subst Heq
  iframe Hrd
  isplitl [Hfl HflQ]
  · iunfold flagAt; iframe Hfl HflQ
  iframe Hv
  ipureintro; rfl

theorem auth.authStore.isRangeOpPermitted.wp_latest
    (h_String : zap.String.spec (GF := GF) (hG := hG))
    (h_Error : zap.Logger.Error.spec (GF := GF) (hG := hG))
    (h_checkKeyInterval : auth.checkKeyInterval.spec (GF := GF) (hG := hG))
    (h_checkKeyPoint : auth.checkKeyPoint.spec (GF := GF) (hG := hG)) :
    auth.authStore.isRangeOpPermitted.specL (GF := GF) (hG := hG) := by
  intro st R M sc user key re k e dk de pt
  wp_start as ⟨#Hinv, Hrd, Hca, Hk, He, %Hpt, %Hlen⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  iunfold authInv at Hinv
  icases Hinv with ⟨%Hst, -, ⟨%lg, #Hlg, %Hlgnn⟩, -, -, -, -⟩
  ihave %Hle := ownSlice_len _ _ _ $$ He
  have he0 := adt.slice_len_eq_zero Hle
  iunfold cacheRd at Hrd
  iunfold cacheAt at Hca
  icases Hca with ⟨%mp', %Mp', Hmp', #HM', #Hof, Hq⟩
  iunfold cacheOf at Hof
  icases Hof with ⟨%Hdom, #Hall⟩
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.RWMutex.wp_RLock $$ [$Hrd] as ⟨Hlk, HP⟩
  iunfold cacheP at HP
  icases HP with ⟨%mp, %Mp, Hmp, #HM, #Hok, HgM⟩
  icombine Hmp Hmp' gives %Heq
  subst Heq
  ihave %HMeq := ownMap_agree mp _ _ Mp Mp' $$ [$HM $HM']
  subst HMeq
  (try wp_auto)
  wp_apply wp_map_lookup2 go.string _ mp Mp user $$ HM as -
  cases HMu : Mp !! user with
  | none =>
    simp only [Option.isSome_none, Bool.false_eq_true, decide_false, Bool.not_false]
    wp_auto
    wp_apply h_String _ _ as %f -
    (try wp_auto)
    wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f]
    isplitr
    · ipureintro; rfl
    iintro %fsl ⟨-, -⟩
    (try wp_auto)
    wp_apply h_Error
    · ipureintro; exact Hlgnn
    (try wp_auto)
    wp_apply sync.RWMutex.wp_RUnlock $$ [$Hlk Hmp HgM] as Hrd
    · inext; iunfold cacheP; iexists mp, Mp; iframe Hmp HM Hok HgM
    iapply HΦ
    iunfold cacheRd
    iframe Hrd Hk He
    isplitl [Hmp' Hq]
    · iunfold cacheAt; iexists mp, Mp; iframe Hmp' HM Hq; iunfold cacheOf; iframe Hall
      ipureintro; exact Hdom
    ipureintro; exact cacheVerdictP_absent sc Mp user k e pt Hdom HMu
  | some p =>
    ihave #Hent := BigSepM.bigSepM_lookup (Φ := fun (u : GoString) (p : Loc) =>
        iprop(∃ Lr Lw, permsAt p Lr Lw ∗ ⌜cacheEntryIs sc u Lr Lw⌝)) HMu $$ Hall
    icases Hent with ⟨%Lr, %Lw, #Hp, %Hent⟩
    simp only [Option.isSome_some, _root_.decide_true, Bool.not_true, Option.getD_some]
    wp_auto
    wp_if_destruct
    · -- a point: `rangeEnd` empty
      rw [he0] at Hif
      wp_apply (h_checkKeyPoint lg p Lr Lw key k dk pt) $$ [$Hp $Hk] as %b ⟨Hk, %Hb⟩
      · ipureintro; exact ⟨Hpt, Hlen⟩
      (try wp_auto)
      wp_apply sync.RWMutex.wp_RUnlock $$ [$Hlk Hmp HgM] as Hrd
      · inext; iunfold cacheP; iexists mp, Mp; iframe Hmp HM Hok HgM
      iapply HΦ
      iunfold cacheRd
      iframe Hrd Hk He
      isplitl [Hmp' Hq]
      · iunfold cacheAt; iexists mp, Mp; iframe Hmp' HM Hq; iunfold cacheOf; iframe Hall
        ipureintro; exact Hdom
      ipureintro
      apply cacheVerdictP_entry sc user k e pt b Lr Lw Hpt Hent
      intro _ _
      rw [if_pos Hif]
      exact Hb
    · rw [he0] at Hif
      wp_apply (h_checkKeyInterval lg p Lr Lw key re k e dk de pt) $$ [$Hp $Hk $He]
        as %b ⟨Hk, He, %Hb⟩
      · ipureintro; exact Hpt
      (try wp_auto)
      wp_apply sync.RWMutex.wp_RUnlock $$ [$Hlk Hmp HgM] as Hrd
      · inext; iunfold cacheP; iexists mp, Mp; iframe Hmp HM Hok HgM
      iapply HΦ
      iunfold cacheRd
      iframe Hrd Hk He
      isplitl [Hmp' Hq]
      · iunfold cacheAt; iexists mp, Mp; iframe Hmp' HM Hq; iunfold cacheOf; iframe Hall
        ipureintro; exact Hdom
      ipureintro
      apply cacheVerdictP_entry sc user k e pt b Lr Lw Hpt Hent
      intro hk hr
      rw [if_neg Hif]
      rcases hr with h | h
      · exact absurd h Hif
      · exact Hb hk h

end proof

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- The latest state of `hs` in the mode `on`, unique. -/
theorem histLast_on_unique (γa : AuthNames) (hs : List AuthState) (a b : AuthState)
    (ha : histLast (.on γa) hs a) (hb : hs.getLast? = some b) : a = b := by
  have h : hs.getLast? = some a := ha
  rw [h] at hb; cases hb; rfl

theorem auth.authStore.isOpPermitted.wp_latest
    (h_IsAuthEnabled : auth.authStore.IsAuthEnabled.specL (GF := GF) (hG := hG))
    (h_Revision : auth.authStore.Revision.spec (GF := GF) (hG := hG))
    (h_Uint64 : zap.Uint64.spec (GF := GF) (hG := hG))
    (h_ByteString : zap.ByteString.spec (GF := GF) (hG := hG))
    (h_ZError : zap.Error.spec (GF := GF) (hG := hG))
    (h_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (h_String : zap.String.spec (GF := GF) (hG := hG))
    (h_Error : zap.Logger.Error.spec (GF := GF) (hG := hG))
    (h_hasRootRole : auth.hasRootRole.spec (GF := GF) (hG := hG))
    (h_lockedReadTx : auth.authStore.lockedReadTx.specL (GF := GF) (hG := hG))
    (h_isRangeOpPermitted : auth.authStore.isRangeOpPermitted.specL (GF := GF) (hG := hG)) :
    auth.authStore.isOpPermitted.specL (GF := GF) (hG := hG) := by
  intro st R M hs b sc info key re k e dk de pt
  wp_start as ⟨#Hinv, Hrd, Hk, He, %Hpt, %Hlen, Hown, Hfl, Hca, %Htie⟩
  iunfold authRd at Hrd
  icases Hrd with ⟨Hen, Hcr, Hbr, HR⟩
  ihave %Hkeys := authOwn_last_permKeysOk M hs $$ Hown
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave Hai : (authInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hai with ⟨#HeUE, #HeUNF, #HePD, #HeOR, #HeIT, -, -⟩
  ihave #HeUE' := HeUE
  iunfold authErrVar at HeUE'
  icases HeUE' with ⟨%eUE, #HeUEa, -⟩
  ihave #HePD' := HePD
  iunfold authErrVar at HePD'
  icases HePD' with ⟨%ePD, #HePDa, -⟩
  ihave #HeOR' := HeOR
  iunfold authErrVar at HeOR'
  icases HeOR' with ⟨%eOR, #HeORa, -⟩
  ihave #Hinv' := Hinv
  iunfold authInv at Hinv'
  icases Hinv' with ⟨%Hst, -, ⟨%lg, #Hlg, %Hlgnn⟩, -, -, -, -⟩
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply (h_IsAuthEnabled st R M b) $$ [$Hinv $Hen $Hfl] as %en ⟨Hen, Hfl, #Hev, %Hen_b⟩
  subst Hen_b
  cases en
  · wp_auto
    iapply HΦ
    iunfold authRd
    iframe
    isplitl []
    · iunfold authErrIs; ileft; ipureintro; rfl
    ipureintro
    cases M with
    | on γa => exact permVerdictL_on_disabled γa hs sc _ _ _ _ Htie
    | off => rfl
    | any => trivial
  ihave %Hnoff := enabledVerdict_true_ne_off M $$ Hev
  wp_auto
  wp_if_destruct
  · iapply HΦ
    iunfold authRd
    iframe
    isplitl []
    · iunfold authErrIs
      iright
      iexists ErrUserEmpty, eUE
      iframe HeUEa
      ipureintro; simp
    ipureintro
    cases M with
    | on γa =>
      refine permVerdictL_on_refused γa hs sc _ _ _ _ _ (fun h => by cases h) Htie ?_
      intro stl _ _
      left; unfold authInfoM; simp only; rw [Hif]; rfl
    | off => exact absurd rfl Hnoff
    | any => trivial
  have h0 : uint.nat info.Revision' ≠ 0 := fun h => Hif (by word)
  wp_apply (h_Revision st R M (some hs)) $$ [$Hinv Hown] as %cur ⟨Hown, -, %Hcur⟩
  · iunfold authOwnOpt; iexact Hown
  iunfold authOwnOpt at Hown
  (try wp_auto)
  wp_if_destruct
  · wp_apply h_Uint64 _ _ as %f1 -
    wp_apply h_Uint64 _ _ as %f2 -
    wp_apply h_ByteString _ _ as %f3 -
    (try wp_auto)
    wp_apply h_ZError _ as %f4 -
    (try wp_auto)
    wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1, f2, f3, f4]
    isplitr
    · ipureintro; rfl
    iintro %fsl ⟨-, -⟩
    (try wp_auto)
    wp_apply h_Warn
    · ipureintro; exact Hlgnn
    iapply HΦ
    iunfold authRd
    iframe
    isplitl []
    · iunfold authErrIs
      iright
      iexists ErrAuthOldRevision, eOR
      iframe HeORa
      ipureintro; simp
    ipureintro
    cases M with
    | on γa =>
      refine permVerdictL_on_refused γa hs sc _ _ _ _ _ (fun h => by cases h) Htie ?_
      intro stl hl _
      right; left
      have hc := Hcur hs stl rfl hl rfl (by nofun)
      unfold authInfoM; simp only
      rw [← hc]; word
    | off => exact absurd rfl Hnoff
    | any => trivial
  have hcur : uint.nat cur ≤ uint.nat info.Revision' := by word
  wp_apply (h_lockedReadTx st R M hs) $$ [$Hinv $Hbr $HR $Hown] as %tx ⟨Hbr, Htx, Hown⟩
  iunfold authReadTxLockedL at Htx
  icases Htx with ⟨%ti, %Hti, Htx⟩
  subst Hti
  icases Htx with ⟨%sta, %Hs, Htok, -, %Hsta, #Hreads⟩
  iunfold authTxReads at Hreads
  icases Hreads with ⟨#Hrds, #HRU⟩
  iunfold authReaderOk at Hrds
  icases Hrds with ⟨#HUG, -, -, -, -⟩
  wp_auto
  wp_bind (App (Val #(methods ti.ty go!"UnsafeGetUser" ti.v)) (Val #info.Username'))
  iapply HUG $$ Htok
  inext
  iintro %u ⟨Htok, Hu⟩
  wp_auto
  wp_if_destruct
  · ihave %Hnone := userOut_null sta info.Username' $$ Hu
    wp_apply h_String _ _ as %f -
    (try wp_auto)
    wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f]
    isplitr
    · ipureintro; rfl
    iintro %fsl ⟨-, -⟩
    (try wp_auto)
    wp_apply h_Error
    · ipureintro; exact Hlgnn
    (try wp_auto)
    wp_bind (App (Val #(methods ti.ty go!"RUnlock" ti.v)) (Val #()))
    iapply HRU $$ Htok
    inext
    iintro HR
    (try wp_auto)
    iapply HΦ
    iunfold authRd
    iframe
    isplitl []
    · iunfold authErrIs
      iright
      iexists ErrPermissionDenied, ePD
      iframe HePDa
      ipureintro; simp
    ipureintro
    cases M with
    | on γa =>
      refine permVerdictL_on_refused γa hs sc _ _ _ _ _ (fun h => by cases h) Htie ?_
      intro stl hl _
      right; right
      have hsl := histLast_on_unique γa hs sta stl Hsta hl
      subst hsl
      intro u hu
      have hu' : sta.users !! info.Username' = some u := hu
      rw [Hnone] at hu'; cases hu'
    | off => exact absurd rfl Hnoff
    | any => trivial
  ihave Hu' := userOut_some u sta info.Username' Hif $$ Hu
  icases Hu' with ⟨%roles, %ur, %Hur, Hu⟩
  wp_apply h_hasRootRole $$ [$Hu] as %root ⟨Hu, %Hroot⟩
  · ipureintro; rw [Hur.2.1]; exact Hur.2.2
  cases root
  · have hn : ¬ isRoot roles := by rw [← Hur.2.1]; exact of_decide_eq_false Hroot.symm
    (try wp_auto)
    wp_apply (h_isRangeOpPermitted st R M sc info.Username' key re k e dk de pt)
      $$ [$Hinv $Hcr $Hca $Hk $He] as %okr ⟨Hcr, Hca, Hk, He, %Hcv⟩
    · ipureintro; exact ⟨Hpt, Hlen⟩
    cases okr
    · (try wp_auto)
      wp_bind (App (Val #(methods ti.ty go!"RUnlock" ti.v)) (Val #()))
      iapply HRU $$ Htok
      inext
      iintro HR
      (try wp_auto)
      iapply HΦ
      iunfold authRd
      iframe
      isplitl []
      · iunfold authErrIs
        iright
        iexists ErrPermissionDenied, ePD
        iframe HePDa
        ipureintro; simp
      ipureintro
      cases M with
      | on γa =>
        refine permVerdictL_on_refused γa hs sc _ _ _ _ _ (fun h => by cases h) Htie ?_
        intro stl hl hsc
        subst hsc
        have hsl := histLast_on_unique γa hs sta sc Hsta hl
        subst hsl
        right; right
        intro u' hu'
        have hu'' : sta.users !! info.Username' = some u' := hu'
        rw [Hur.1] at hu''; cases hu''
        refine ⟨hn, fun hsh u2 hu2 => ?_⟩
        exact cacheVerdictP_false_not_covers sta info.Username' k e pt Hcv
          (Hkeys sta Hsta rfl (by nofun)) hsh u2 hu2
      | off => exact absurd rfl Hnoff
      | any => trivial
    · (try wp_auto)
      wp_bind (App (Val #(methods ti.ty go!"RUnlock" ti.v)) (Val #()))
      iapply HRU $$ Htok
      inext
      iintro HR
      (try wp_auto)
      iapply HΦ
      iunfold authRd
      iframe
      isplitl []
      · iunfold authErrIs; ileft; ipureintro; rfl
      ipureintro
      cases M with
      | on γa =>
        refine permVerdictL_on_pass γa hs sc _ _ _ _ Htie ?_
        intro stl hl hsc
        subst hsc
        have hsl := histLast_on_unique γa hs sta sc Hsta hl
        subst hsl
        have hc := Hcur hs sta rfl Hsta rfl (by nofun)
        refine ⟨h0, ?_, roles, Hur.1, Or.inr fun hsh => ?_⟩
        · show sta.revision ≤ uint.nat info.Revision'; rw [← hc]; exact hcur
        · exact cacheVerdictP_true_covers sta info.Username' k e pt Hcv
            (Hkeys sta Hsta rfl (by nofun)) hsh roles Hur.1
      | off => exact absurd rfl Hnoff
      | any => trivial
  · have hroot : isRoot roles := by rw [← Hur.2.1]; exact of_decide_eq_true Hroot.symm
    (try wp_auto)
    wp_bind (App (Val #(methods ti.ty go!"RUnlock" ti.v)) (Val #()))
    iapply HRU $$ Htok
    inext
    iintro HR
    (try wp_auto)
    iapply HΦ
    iunfold authRd
    iframe
    isplitl []
    · iunfold authErrIs; ileft; ipureintro; rfl
    ipureintro
    cases M with
    | on γa =>
      refine permVerdictL_on_pass γa hs sc _ _ _ _ Htie ?_
      intro stl hl hsc
      have hsl := histLast_on_unique γa hs sta stl Hsta hl
      subst hsl
      have hc := Hcur hs sta rfl Hsta rfl (by nofun)
      refine ⟨h0, ?_, roles, Hur.1, Or.inl hroot⟩
      show sta.revision ≤ uint.nat info.Revision'; rw [← hc]; exact hcur
    | off => exact absurd rfl Hnoff
    | any => trivial

end proof


namespace auth

section pure
variable [ext : FfiSyntax]

/-- **The latest verdict of one permission, in `kvGranted`'s shape** (the auth plan's E2r, for
E2q's model step, `etcdserver/KVAuthModel.lean`): for a request of the cache's shape, a check of
`op` on `[key, rangeEnd)` passes exactly when, at the latest state, auth is disabled, or the token's
revision is not `0` nor stale and its user exists with the root role or permissions covering the
request. -/
theorem permVerdictL_granted (γa : AuthNames) (hs : List AuthState) (ai : AuthInfoM)
    (key rangeEnd : GoString) (op : PermType) (err : GoInterface) (stl : AuthState)
    (hl : hs.getLast? = some stl) (hsh : reqShape key rangeEnd)
    (h : permVerdictL (.on γa) hs ai key rangeEnd op err) :
    err = GoInterface.nil ↔
      (stl.enabled = false ∨ (ai.rev ≠ 0 ∧ stl.revision ≤ ai.rev ∧
        ∃ u, stl.users !! ai.user = some u ∧ (isRoot u ∨ covers stl u op key rangeEnd))) := by
  rw [permVerdictL_iff γa hs ai key rangeEnd op err stl hl hsh h]
  unfold permitted granted
  constructor
  · rintro ⟨hp | ⟨h0, u, hu, hc⟩, hr⟩
    · exact Or.inl hp
    · rcases hr with hr | hr
      · exact Or.inl hr
      · refine Or.inr ⟨h0, hr, u, hu, ?_⟩
        rcases hc with hc | hc
        · exact Or.inl hc
        · exact Or.inr (hc hsh)
  · rintro (hd | ⟨h0, hr, u, hu, hc⟩)
    · exact ⟨Or.inl hd, Or.inl hd⟩
    · refine ⟨Or.inr ⟨h0, u, hu, ?_⟩, Or.inr hr⟩
      rcases hc with hc | hc
      · exact Or.inl hc
      · exact Or.inr fun _ => hc

theorem permVerdictL_permOp (M : AuthMode) (hs : List AuthState) (ai : AuthInfoM)
    (key rangeEnd : GoString) (pt : go_etcd_io.etcd.api.v3.authpb.Permission_Type) (op : PermType)
    (err : GoInterface) (hop : permOp pt = op)
    (h : permVerdictL M hs ai key rangeEnd (permOp pt) err) :
    permVerdictL M hs ai key rangeEnd op err := by
  rw [hop] at h; exact h

end pure

end auth

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- `as.IsPutPermitted(authInfo, key)` on the apply thread: the latest state's verdict on the
write (`isOpPermitted.specL`). -/
abbrev auth.authStore.IsPutPermitted.specL : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : auth.AuthMode) (hs : List auth.AuthState) (b : Bool)
    (sc : auth.AuthState) (a : Loc) (info : AuthInfo) (dq : DFrac) (key : GoSlice) (k : List w8)
    (dk : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗
      authRd st R M ∗ a ↦{dq} info ∗ key ↦*{dk} k ∗ ⌜sint.Z key.len < 2 ^ 63 - 1⌝ ∗
      authOwn M hs ∗ flagAt st M b ∗ cacheAt st M sc ∗ ⌜latestTie M hs b sc⌝ }}
    (App (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"IsPutPermitted")) (Val #a)) (Val #key))
  {{ (err : GoInterface), RET #err; authRd st R M ∗ a ↦{dq} info ∗ key ↦*{dk} k ∗ authErrIs err ∗
      authOwn M hs ∗ flagAt st M b ∗ cacheAt st M sc ∗
      ⌜permVerdictL M hs (authInfoM info) k [] .write err⌝ }}

/-- `as.IsRangePermitted(authInfo, key, rangeEnd)` on the apply thread: the latest state's verdict
on the read. -/
abbrev auth.authStore.IsRangePermitted.specL : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : auth.AuthMode) (hs : List auth.AuthState) (b : Bool)
    (sc : auth.AuthState) (a : Loc) (info : AuthInfo) (dq : DFrac) (key re : GoSlice)
    (k e : List w8) (dk de : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗
      authRd st R M ∗ a ↦{dq} info ∗ key ↦*{dk} k ∗ re ↦*{de} e ∗ ⌜sint.Z key.len < 2 ^ 63 - 1⌝ ∗
      authOwn M hs ∗ flagAt st M b ∗ cacheAt st M sc ∗ ⌜latestTie M hs b sc⌝ }}
    (App (App (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"IsRangePermitted")) (Val #a)) (Val #key)) (Val #re))
  {{ (err : GoInterface), RET #err; authRd st R M ∗ a ↦{dq} info ∗ key ↦*{dk} k ∗
      re ↦*{de} e ∗ authErrIs err ∗ authOwn M hs ∗ flagAt st M b ∗ cacheAt st M sc ∗
      ⌜permVerdictL M hs (authInfoM info) k e .read err⌝ }}

/-- `as.IsDeleteRangePermitted(authInfo, key, rangeEnd)` on the apply thread: the latest state's
verdict on the write. -/
abbrev auth.authStore.IsDeleteRangePermitted.specL : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : auth.AuthMode) (hs : List auth.AuthState) (b : Bool)
    (sc : auth.AuthState) (a : Loc) (info : AuthInfo) (dq : DFrac) (key re : GoSlice)
    (k e : List w8) (dk de : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗
      authRd st R M ∗ a ↦{dq} info ∗ key ↦*{dk} k ∗ re ↦*{de} e ∗ ⌜sint.Z key.len < 2 ^ 63 - 1⌝ ∗
      authOwn M hs ∗ flagAt st M b ∗ cacheAt st M sc ∗ ⌜latestTie M hs b sc⌝ }}
    (App (App (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"IsDeleteRangePermitted")) (Val #a)) (Val #key)) (Val #re))
  {{ (err : GoInterface), RET #err; authRd st R M ∗ a ↦{dq} info ∗ key ↦*{dk} k ∗
      re ↦*{de} e ∗ authErrIs err ∗ authOwn M hs ∗ flagAt st M b ∗ cacheAt st M sc ∗
      ⌜permVerdictL M hs (authInfoM info) k e .write err⌝ }}

end spec

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem auth.authStore.IsPutPermitted.wp_latest
    (h_isOpPermitted : auth.authStore.isOpPermitted.specL (GF := GF) (hG := hG)) :
    auth.authStore.IsPutPermitted.specL (GF := GF) (hG := hG) := by
  intro st R M hs b sc a info dq key k dk
  wp_start as ⟨#Hinv, Hrd, Ha, Hk, %Hlen, Hown, Hfl, Hca, %Htie⟩
  ihave %Hann := typedPointsto_not_null $$ Ha
  iStructNamed Ha
  wp_auto
  wp_apply (h_isOpPermitted st R M hs b sc info key slice.nil k [] dk (DFrac.own 1)
      (W32 1)) $$ [$Hinv $Hrd $Hk $Hown $Hfl $Hca] as %err ⟨Hrd, Hk, -, Herr, Hown, Hfl, Hca, %Hv⟩
  · isplitl
    · iapply ownSlice_nil (V := w8) (DFrac.own 1)
    ipureintro; exact ⟨by simp [permTypOk], Hlen, Htie⟩
  ihave Ha : a ↦{dq} info $$ [Username Revision]
  · iapply typedPointsto_combine a info dq Hann
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  iapply HΦ
  iframe
  ipureintro; exact auth.permVerdictL_permOp M hs _ k [] (W32 1) .write err (by simp [permOp]) Hv

theorem auth.authStore.IsRangePermitted.wp_latest
    (h_isOpPermitted : auth.authStore.isOpPermitted.specL (GF := GF) (hG := hG)) :
    auth.authStore.IsRangePermitted.specL (GF := GF) (hG := hG) := by
  intro st R M hs b sc a info dq key re k e dk de
  wp_start as ⟨#Hinv, Hrd, Ha, Hk, He, %Hlen, Hown, Hfl, Hca, %Htie⟩
  ihave %Hann := typedPointsto_not_null $$ Ha
  iStructNamed Ha
  wp_auto
  wp_apply (h_isOpPermitted st R M hs b sc info key re k e dk de
      (W32 0)) $$ [$Hinv $Hrd $Hk $He $Hown $Hfl $Hca] as %err ⟨Hrd, Hk, He, Herr, Hown, Hfl, Hca, %Hv⟩
  · ipureintro; exact ⟨by simp [permTypOk], Hlen, Htie⟩
  ihave Ha : a ↦{dq} info $$ [Username Revision]
  · iapply typedPointsto_combine a info dq Hann
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  iapply HΦ
  iframe
  ipureintro; exact auth.permVerdictL_permOp M hs _ k e (W32 0) .read err (by simp [permOp]) Hv

theorem auth.authStore.IsDeleteRangePermitted.wp_latest
    (h_isOpPermitted : auth.authStore.isOpPermitted.specL (GF := GF) (hG := hG)) :
    auth.authStore.IsDeleteRangePermitted.specL (GF := GF) (hG := hG) := by
  intro st R M hs b sc a info dq key re k e dk de
  wp_start as ⟨#Hinv, Hrd, Ha, Hk, He, %Hlen, Hown, Hfl, Hca, %Htie⟩
  ihave %Hann := typedPointsto_not_null $$ Ha
  iStructNamed Ha
  wp_auto
  wp_apply (h_isOpPermitted st R M hs b sc info key re k e dk de
      (W32 1)) $$ [$Hinv $Hrd $Hk $He $Hown $Hfl $Hca] as %err ⟨Hrd, Hk, He, Herr, Hown, Hfl, Hca, %Hv⟩
  · ipureintro; exact ⟨by simp [permTypOk], Hlen, Htie⟩
  ihave Ha : a ↦{dq} info $$ [Username Revision]
  · iapply typedPointsto_combine a info dq Hann
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  iapply HΦ
  iframe
  ipureintro; exact auth.permVerdictL_permOp M hs _ k e (W32 1) .write err (by simp [permOp]) Hv

end proof

end EtcdGrove
end Perennial
