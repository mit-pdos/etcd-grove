/-
**The auth store at the server's boot, in the mode `on γa`** (the auth plan's E2e, 2026-10-25;
`notes/decisions.md`, "E2e of the auth plan"). Lean-first (no Rocq counterpart).

`newAuthStore_on` (`NewAuthStoreOn.lean`) takes the auth names `γa` with the admin side's
authority and the other half of the latest state's ghost variable from its caller, and the
backend's contracts (`authBackendOk`, `authWBackendOkR`, `CreateAuthBuckets`) for those names. At
the server's boot nobody has the names yet: `newAuthStore_boot` allocates them (`authBoot_alloc`)
over the boot state `bootState` (disabled, revision `0`, no user, no role: the buckets created
empty), with the token provider's names `γt`, `γf` (the simple provider's, `tokenSimple_new`),
hands the batch lock's half of the history (`authLockI`) to the backend, and runs
`newAuthStore_on`.

**What only D22 can prove** is the named premise `authSchemaBoot`: given the lock's half at the
boot state, schema's auth backend meets the store's backend contracts for the new names (the real
backend keeps `∃ st, buckets(st) ∗ authLockI M st` under its batch lock; `notes/decisions.md`,
"S4f of the auth plan", the list of what D22 discharges). The token provider's contract for the
names (`tokenProviderOkA`) is a premise for any names with the provider's `γt`, `γf`, which the
simple provider meets (`tokenSimple_okA`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.NewAuthStoreOn
public import Proof.go_etcd_io.etcd.server.v3.auth.Fuel

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace auth

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth

/-- **The auth state of freshly created buckets**: disabled, revision `0`, no user, no role. -/
def bootState : AuthState := ⟨false, 0, ∅, ∅⟩

theorem bootState_permKeysOk : permKeysOk bootState := by
  intro r ps h
  simp [bootState] at h

theorem bootState_permsFit : permsFit bootState := by
  intro u roles h
  simp [bootState] at h

/-- The boot state is small (`Fuel.lean`, the auth plan's E2l). -/
theorem bootState_small : authSmall bootState := by
  refine ⟨?_, ?_, ?_, [], List.nodup_nil, ?_, ?_⟩ <;> simp [bootState, permsOn]

section ghost
variable [FfiSyntax] {GF : BundledGFunctors} [AllG GF]

/-- **The auth names at boot**: a history of the boot state alone, with the token names `γt`,
`γf`: the admin side's authority, the other half of the latest state's ghost variable (the store's
revision invariant takes it, `newAuthStore_on`) and the batch lock's half of the history at the
boot state (the backend's, `authSchemaBoot`). -/
theorem authBoot_alloc (γt γf : GName) :
    ⊢ |==> ∃ γa : AuthNames, ⌜γa.tok = γt ∧ γa.fresh = γf⌝ ∗
      authOwn (GF := GF) (.on γa) [bootState] ∗ authStoreInit γa bootState ∗
      authLockI (.on γa) bootState := by
  iintro
  imod (authHist_alloc (GF := GF) γt γf [bootState] bootState
    (by intro st h; rw [List.mem_singleton] at h; subst h; exact bootState_permKeysOk))
    with ⟨%γa, %Hγ, Hh, Hc1, Hc2, Hp, He, Hk⟩
  imodintro
  iexists γa
  isplitr
  · ipureintro; exact Hγ
  ihave HF : authOwnF (.on γa) [bootState] $$ [Hh Hc1]
  · simp only [authOwnF]
    iframe Hh
    iexists bootState; iframe Hc1; ipureintro; rfl
  icases authOwnF_lockI_split (.on γa) [bootState] bootState rfl $$ HF with ⟨Hown, HI⟩
  iframe Hown HI
  iunfold authStoreInit; iframe Hc2 Hp; isplitl [He]
  · iexists false; iframe He
  iexists ((null : Loc), 0); iframe Hk

/-- **A right to issue a token, minted** from the rights' authority (`tokenSimple_new` gives it,
empty, with the provider): one for any token not minted before. The server's apply thread, which
runs `Authenticate`, would hold the authority and mint the right of the token it is about to issue
(`<prefix>.<raft index>`, the index unique per entry). -/
theorem tokFresh_mint (γa : AuthNames) (m : GMap GoString Unit) (token : GoString)
    (h : m.lookup token = none) :
    ghostMapAuth (GF := GF) γa.fresh 1 m ⊢
      |==> (ghostMapAuth γa.fresh 1 (m.insert token ()) ∗ tokFresh γa token) := by
  iintro H
  unfold tokFresh
  imod (ghost_map_insert token () h) $$ H with ⟨Ha, He⟩
  imodintro
  iframe Ha
  iexact He

end ghost

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **What D22 discharges at boot** (a named premise of `newAuthStore_boot`; see the file
header): for any auth names with the token names `γt`, `γf`, the batch lock's half of the history
at the boot state makes schema's auth backend `ab` (`bi`) meet the store's backend contracts for
those names: the read side for the reader resource `R`, the write side (`authWBackendOkR`) at the
batch lock's contract `P f` with the write token `T`, and `CreateAuthBuckets` as one transaction
keeping `T`. -/
def authSchemaBoot (ab : GoInterface) (bi : GoInterfaceOk) (γt γf : GName) (R P : IProp GF)
    (f : val) (T : IProp GF) : IProp GF :=
  iprop(∀ γa : AuthNames, ⌜γa.tok = γt ∧ γa.fresh = γf⌝ -∗ authLockI (.on γa) bootState -∗
    |==> (authBackendOk ab R (.on γa) ∗ authWBackendOkR ab (.on γa) P f T ∗
      □ ({{ T }} (App (Val #(methods bi.ty go!"CreateAuthBuckets" bi.v)) (Val #()))
        {{ RET #(); T }})))

/-- **The token provider `tp`'s contract for any names with its token names** `γt`, `γf`
(persistent; the simple provider's, `tokenSimple_okA`), with its admin resource `A`. -/
def tokenProviderBoot (tp : GoInterface) (γt γf : GName) (A : IProp GF) : IProp GF :=
  iprop(□ ∀ γa : AuthNames, ⌜γa.tok = γt ∧ γa.fresh = γf⌝ -∗ tokenProviderOkA tp (.on γa) A)

instance tokenProviderBoot_persistent (tp : GoInterface) (γt γf : GName) (A : IProp GF) :
    Persistent (tokenProviderBoot tp γt γf A) := by
  unfold tokenProviderBoot; infer_instance

/-- **The admin side's fuel at the store's start** (the auth plan's E2l, `Fuel.lean`): the history
`newAuthStore_boot` gives, `[bootState, bump bootState]`, from no receipt. -/
theorem authFuel_boot : ⊢ |==> authFuel (GF := GF) [bootState, bump bootState] :=
  authFuel_init _ (bump bootState) rfl (authSmall_bump _ bootState_small)
    (by simp [bump, bootState])

end defs

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

set_option maxRecDepth 16384 in
/-- **`NewAuthStore(lg, be, tp, cost)` at the server's boot, in the mode `on γa`** (see the file
header): the names allocated over the boot state, the store's invariant, the admin side's write
resource, the provider's share and the admin side's authority at the history `[bootState, bump
bootState]` (the constructor's `commitRevision` of the revision `0`), with the names' token parts
the provider's. -/
theorem newAuthStore_boot
    (h_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (h_Int : zap.Int'.spec (GF := GF) (hG := hG))
    (h_Revision : auth.authStore.Revision.spec (GF := GF) (hG := hG))
    (h_commit : auth.authStore.commitRevision.spec (GF := GF) (hG := hG))
    (h_metrics : auth.authStore.setupMetricsReporter.spec (GF := GF) (hG := hG))
    (h_refresh : auth.authStore.refreshRangePermCache.spec (GF := GF) (hG := hG))
    (lg : Loc) (ab tp : GoInterface) (cost : w64) (bi : GoInterfaceOk) (γt γf : GName)
    (R P : IProp GF) (f : val) (T A Pre Q Post : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ ⌜lg ≠ null⌝ ∗
        ⌜ab = GoInterface.ok bi⌝ ∗ authSchemaBoot ab bi γt γf R P f T ∗
        T ∗ mvcc.csContract P f Pre Q Post ∗ tokenProviderBoot tp γt γf A ∗ A }}
      (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.auth.NewAuthStore)) (Val #lg))
        (Val #ab)) (Val #tp)) (Val #cost))
    {{ (st : GoInterface), RET #st; ∃ (γa : AuthNames) (stp : Loc),
        ⌜γa.tok = γt ∧ γa.fresh = γf⌝ ∗ ⌜st = authIface stp⌝ ∗ authInv stp R (.on γa) ∗
        authWR stp (.on γa) P f T ∗ tpAdmin stp (.on γa) ∗ Post ∗
        authOwn (.on γa) [bootState, bump bootState] ∗
        ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
          enabledRd stp (.on γa) ∗ cacheRd stp (.on γa) ∗ beRd stp R (.on γa)) }} := by
  wp_start_folded as ⟨%Hlg, %Hab, HD, HT, Hcs, #Htp, HA⟩
  ihave #Hpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth $$ []
  · iPkgInit
  imod (authBoot_alloc (GF := GF) γt γf) with ⟨%γa, %Hγ, Hown, Hcur, HI⟩
  iunfold authSchemaBoot at HD
  ihave HD' := HD $$ %γa [] HI
  · ipureintro; exact Hγ
  imod HD' with ⟨#Hrd, #Hw, #Hcr⟩
  iunfold tokenProviderBoot at Htp
  ihave #HtpA := Htp $$ %γa []
  · ipureintro; exact Hγ
  wp_apply (newAuthStore_on h_Warn h_Int h_Revision h_commit h_metrics h_refresh lg ab tp cost bi
      γa R P f T A Pre Q Post [bootState] bootState rfl bootState_permsFit
      ⟨bootState, List.mem_singleton_self _, rfl⟩) $$ [$Hpkg $Hrd $Hw $Hcr $HT $Hcs $HtpA $HA $Hown $Hcur]
    as %st ⟨%stp, %hs', %Hst, #Hinv, HWR, HtpAd, HPost, Hown', %Hhs, Hslots⟩
  · iframe; isplitr
    · ipureintro; exact Hlg
    ipureintro; exact Hab
  have Hhs' : hs' = [bootState, bump bootState] := by
    rcases Hhs with ⟨h0, -⟩ | ⟨-, h1⟩
    · exact absurd rfl h0
    · simpa using h1
  subst Hhs'
  ihave HWR := authWRAt_authWR stp (.on γa) P f T ab $$ HWR
  iapply HΦ
  iexists γa, stp
  iframe Hinv HWR HtpAd HPost Hown' Hslots
  ipureintro; exact ⟨Hγ, Hst⟩

end proof

end auth
end EtcdGrove
end Perennial
