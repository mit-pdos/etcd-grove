/-
**Why a request was refused: the auth store's vocabulary** (auth-guard-completeness G0/G1,
2026-11-14; `notes/auth-guard-scope.md`, §2.1-2.2). Lean-first (no Rocq counterpart).

The reasons a refusal of the auth store's checks names, each at states recorded at indices at least a
reader's lower bound `n` of the published index (`authPubLbM`; without the bound a refusal could
cite the boot state, in which auth is disabled and no user exists):

* `noPrincipalFrom`: the request side gave no principal: no token in the context, or auth disabled
  at such a state (`AuthInfoFromCtx.specLb`, `FreshCtx.lean`);
* `tokRefusedFrom`: the context's token was refused (until token liveness, the Scope's G5, only that
  there was one);
* `adminRefusalFrom`, `adminVerdictFromO`: `IsAdminPermitted`'s refusal, its error tied to its case
  (`IsAdminPermitted.specLbO`, `FreshAdmin.lean`);
* `histFrozenFrom`, `authOwn_frozen`: no admin change after `n` in the authority's history, what makes
  the reasons exclude a refusal.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.Fresh

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth auth

namespace auth

section defs
variable [GooseExts] {GF : BundledGFunctors} [AllG GF]

/-- **No principal from the request side, seen with the lower bound `n`** (persistent): the flag
read `true` at a state recorded at an index at least `n` and the context carries no token; or the flag
read `false` at such a state (`AuthInfoFromCtx`'s own read, `store.go:1073`). A guard refuses on the
second only beside a read of `true` at such a state too (`reqSideWhy`): together they say the flag
changed since `n`, a race with `AuthDisable` (`requireAuthInfo` reads `true`, then `AuthInfoFromCtx`
`false`: `nonissues/etcd-auth-requireauthinfo-disable-race-user-empty.md`) or with `AuthEnable` (the
admin check: `AuthInfoFromCtx` reads `false`, then `IsAdminPermitted` `true`; the watch's
`isWatchPermitted`: `AuthInfoFromCtx` reads `false`, then `IsRangePermitted`'s `isOpPermitted` `true`
(`store.go:864`), refusing the substituted `AuthInfo{}` with `ErrUserEmpty`; both in
`nonissues/etcd-admin-check-authenable-race.md`). The two reads are not ordered here: the store's
freshness (`revFresh`) gives each read's flag as some state's at an index at least the published one,
not the later read's state as the later one. -/
def noPrincipalFrom (M : AuthMode) (n : Nat) (ctx : GoInterface) : IProp GF :=
  iprop((enabledVerdictFrom M n true ∗ ⌜ctxTokenOf ctx = none⌝) ∨ enabledVerdictFrom M n false)

instance noPrincipalFrom_persistent (M : AuthMode) (n : Nat) (ctx : GoInterface) :
    Persistent (noPrincipalFrom (GF := GF) M n ctx) := by
  unfold noPrincipalFrom; infer_instance

/-- **The context's token was refused, seen with the lower bound `n`** (persistent): the context
carries a token. Nothing more: the token provider's contract (`tokenProviderOkA`'s `info`) says
nothing when it refuses, so a token valid at every state may be refused (the simple provider's TTL
keeper may delete any token: the model has no clock). Token liveness is the Scope's G5. -/
def tokRefusedFrom (_M : AuthMode) (_n : Nat) (ctx : GoInterface) : IProp GF :=
  iprop(⌜∃ t : GoString, ctxTokenOf ctx = some t⌝)

instance tokRefusedFrom_persistent (M : AuthMode) (n : Nat) (ctx : GoInterface) :
    Persistent (tokRefusedFrom (GF := GF) M n ctx) := by
  unfold tokRefusedFrom; infer_instance

end defs

section refusal
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **Why `IsAdminPermitted(authInfo)` refused, at states no older than `n`** (persistent;
`store.go:916-933`): the flag read `true` at a state recorded at an index at least `n`, and
- `ErrUserEmpty`: the auth info `nil` or its user name empty;
- `ErrUserNotFound`: a named user absent at such a state;
- `ErrPermissionDenied`: a named user present at such a state, without the root role. -/
def adminRefusalFrom (γa : AuthNames) (n : Nat) (oinfo : Option go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (err : GoInterface) : IProp GF :=
  iprop((∃ (i : Nat) (sf : AuthState), authStateAt γa i sf ∗ ⌜n ≤ i ∧ sf.enabled = true⌝) ∗
    ((authErrOf .userEmpty err ∗ ⌜∀ info, oinfo = some info → info.Username' = []⌝) ∨
     (∃ info : go_etcd_io.etcd.server.v3.auth.AuthInfo, ⌜oinfo = some info ∧ info.Username' ≠ []⌝ ∗
       ((authErrOf .userNotFound err ∗ ∃ (j : Nat) (su : AuthState), authStateAt γa j su ∗
           ⌜n ≤ j ∧ su.users !! info.Username' = none⌝) ∨
        (authErrOf .permissionDenied err ∗ ∃ (j : Nat) (su : AuthState) (u : User),
           authStateAt γa j su ∗ ⌜n ≤ j ∧ su.users !! info.Username' = some u ∧ ¬ isRoot u⌝)))))

instance adminRefusalFrom_persistent (γa : AuthNames) (n : Nat)
    (oinfo : Option go_etcd_io.etcd.server.v3.auth.AuthInfo) (err : GoInterface) :
    Persistent (adminRefusalFrom (GF := GF) γa n oinfo err) := by
  unfold adminRefusalFrom; infer_instance

/-- **`IsAdminPermitted`'s verdict no older than `n`, both halves** (persistent), for the auth info
`oinfo` (`none`: a `nil` pointer): in `on γa`, a pass admits the principal (`adminOk`) at a state
recorded at an index at least `n`, and a refusal names why (`adminRefusalFrom`); in `off`, a pass; in
`any`, nothing. -/
def adminVerdictFromO (M : AuthMode) (n : Nat) (oinfo : Option go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (err : GoInterface) : IProp GF :=
  match M with
  | .off => iprop(⌜err = GoInterface.nil⌝)
  | .any => iprop(True)
  | .on γa => iprop((∃ (i : Nat) (st : AuthState), authStateAt γa i st ∗
        ⌜n ≤ i ∧ (err = GoInterface.nil → adminOk st (oinfo.map authInfoM))⌝) ∗
      (∀ _ : err ≠ GoInterface.nil, adminRefusalFrom γa n oinfo err))

instance adminVerdictFromO_persistent (M : AuthMode) (n : Nat)
    (oinfo : Option go_etcd_io.etcd.server.v3.auth.AuthInfo) (err : GoInterface) :
    Persistent (adminVerdictFromO (GF := GF) M n oinfo err) := by
  unfold adminVerdictFromO; cases M <;> infer_instance

/-- **The authority's history `hs` is frozen at `st` from the index `n` on** (no admin change after
`n` in the history as it stands; the Scope's §2.1 form). -/
def histFrozenFrom (hs : List AuthState) (n : Nat) (st : AuthState) : Prop :=
  ∀ (k : Nat) (s : AuthState), n ≤ k → hs[k]? = some s → s = st

/-- With the authority's history frozen at `st` from `n` on, a state recorded at an index at least
`n` is `st`. -/
theorem authOwn_frozen (γa : AuthNames) (hs : List AuthState) (n : Nat) (st : AuthState) (i : Nat)
    (s' : AuthState) (hf : histFrozenFrom hs n st) (hi : n ≤ i) :
    authOwn (GF := GF) (.on γa) hs ∗ authStateAt γa i s' ⊢ authOwn (.on γa) hs ∗ ⌜s' = st⌝ := by
  simp only [authOwn]
  have key : authHistHalf (GF := GF) γa hs ∗ authStateAt γa i s' ⊢
      authHistHalf γa hs ∗ ⌜hs[i]? = some s'⌝ :=
    (and_intro (by iintro ⟨H, -⟩; iexact H) (authHistHalf_lookup γa hs i s')).trans
      persistent_and_sep_mp
  iintro ⟨⟨Hh, Hc⟩, #Hs⟩
  ihave ⟨Hh, %Hi⟩ := key $$ [Hh]
  · iframe Hh Hs
  iframe Hh Hc
  ipureintro; exact hf i s' hi Hi

end refusal

end auth

section zero
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

/-- **The trivial lower bound** (E3u; moved from `etcdserver/ReadOn.lean` so that the guards' proofs
derive their reason-free specs): any reader may take `0`. -/
theorem authPubLbM_zero (M : auth.AuthMode) : ⊢ |==> auth.authPubLbM (GF := GF) M 0 := by
  cases M with
  | on γa => unfold auth.authPubLbM auth.authPubLb; exact monoNatLbOwn_0 γa.pub
  | _ => unfold auth.authPubLbM; iintro; imodintro; itrivial

end zero

end EtcdGrove
end Perennial
