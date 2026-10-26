/-
**The server's auth store in either auth mode** (the auth plan's E2i, 2026-10-26;
`notes/decisions.md`, "E2i of the auth plan"). Lean-first (no Rocq counterpart).

`NewServer` calls `auth.NewTokenProvider` and, after `mvcc.New` (whose watchable store's owner tag
names the auth mode, `auth.modeTag`), `auth.NewAuthStore`. Its proof (`NewServer.wp_proofM`) takes
the two through one contract, `authSrvTP on`, generic in whether auth is on: the token provider's
call gives, with no error, a mode `M` (`M.isOn = on`) and the auth store's construction in that
mode (`authStoreKit M tp`): `NewAuthStore`'s axiom's triple with the apply contract in the mode
`M` (`authApplyOkM`), at a resource `K` the kit holds.

* **auth off** (`authSrvTP_off`): from `NewTokenProvider`'s proof and `NewAuthStore`'s axiom, the
  mode `off` (`NewServer.spec`'s, the closed theorems').
* **auth on** (`authSrvTP_on`): the simple provider (`"simple"`, a positive TTL); the auth names
  allocated over the boot state with the provider's token names (`auth.authBoot_alloc`), the store
  from its proof in the mode `on γa` (`auth.newAuthStore_on`), its request side and apply contract
  of its invariant (`authSrvContracts_on`). What only D22 can prove is the named premise
  `authSchemaSrv`: given the batch lock's half of the history at the boot state, schema's auth
  backend over the server's backend meets the store's backend contracts (`authBackendOk`,
  `authWBackendOkR`, `CreateAuthBuckets`), taking the backend resources `NewAuthStore`'s axiom
  takes and giving back what it gives back (as `auth.authSchemaBoot`, E2e, at the server's
  backend). The simple provider's contract rests on `isValidSimpleToken`'s spec for any context
  (`auth.ValidSpec`, a premise: it is proved on contexts only, `tokenSimple_okCtx`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthApplyOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthApplyRes
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvServe
public import Proof.go_etcd_io.etcd.server.v3.auth.Boot
public import Proof.go_etcd_io.etcd.server.v3.auth.TokenKeeperRun
public import Spec.go_etcd_io.etcd.server.v3.auth.NewAuthStore
public import Spec.go_etcd_io.etcd.server.v3.auth.NewTokenProvider

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The rest buckets after `NewAuthStore` on the buckets `r` (its buckets created, the revision
`1` committed: `NewAuthStore`'s axiom's post). -/
abbrev authBucketsAfter (r : GMap GoString backend.BktData) : GMap GoString backend.BktData :=
  ((r.insert go!"auth" authBoot).insert go!"authUsers" ∅).insert go!"authRoles" ∅

/-- **The auth store's construction in the mode `M`** with the token provider `tp` (see the file
header): `NewAuthStore`'s axiom's triple, the apply contract in the mode `M`, at a resource `K`
the kit holds (`True` in the mode `off`; the admin side's authority, the batch lock's half and the
provider's admin resource in the mode `on`). -/
def authStoreKit (M : auth.AuthMode) (tp : GoInterface) : IProp GF :=
  iprop(∃ K : IProp GF, K ∗ □ ∀ (lg : Loc) (ab : GoInterface) (abl : Loc)
      (d : mvcc.KBReal) (W Pk : IProp GF) (qo : Qp) (r : GMap GoString backend.BktData) (cost : w64),
    {{ K ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ ⌜lg ≠ null⌝ ∗
        ⌜tp ≠ GoInterface.nil⌝ ∗ ⌜authRecordsFit⌝ ∗ ⌜ab = authBkIface abl⌝ ∗
        structFieldRef go_etcd_io.etcd.server.v3.storage.schema.authBackend go!"be" abl ↦□
          (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
            #d.be : GoInterface) ∗
        structFieldRef go_etcd_io.etcd.server.v3.storage.schema.authBackend go!"lg" abl ↦□ lg ∗
        backend.isBackend d.γB d.P W Pk d.be ∗ backend.bOpen d.γB qo ∗
        backend.plHook d.γB func.nil ∗ ownToks d.γB.wb 2 ∗ backend.rbOwn d.γB r ∗
        ⌜(r.lookup go!"auth").getD ∅ = ∅ ∧ (r.lookup go!"authUsers").getD ∅ = ∅ ∧
          (r.lookup go!"authRoles").getD ∅ = ∅⌝ }}
      (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.auth.NewAuthStore)) (Val #lg))
        (Val #ab)) (Val #tp)) (Val #cost))
    {{ (st : GoInterface), RET #st; backend.bOpen d.γB qo ∗ backend.plHook d.γB func.nil ∗
        backend.rbOwn d.γB (authBucketsAfter r) ∗
        ∃ (RD : IProp GF) (stl : Loc), ⌜st = auth.authIface stl⌝ ∗ authBeOn stl d.be ∗
        ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (), RD) ∗
        isReqAuth st RD ∗ authApplyOkM M stl RD ∗ authApplyRes M stl }})

/-- **`NewTokenProvider` at the server, with auth on or off** (see the file header): with auth on
(`on = true`) its options `"simple"` and its TTL positive; with no error, a mode `M` with
`M.isOn = on` and the auth store's construction in it. -/
abbrev authSrvTP (on : Bool) : Prop :=
  ∀ (lg : Loc) (opts : GoString) (iw : GoFunc) (ttl : time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ ⌜lg ≠ null⌝ ∗
      ⌜on = true → opts = go!"simple" ∧ 0 < sint.Z ttl⌝ }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.auth.NewTokenProvider)) (Val #lg))
      (Val #opts)) (Val #iw)) (Val #ttl))
  {{ (tp err : GoInterface), RET (PairV #tp #err);
      ⌜err = GoInterface.nil → tp ≠ GoInterface.nil⌝ ∗
      (⌜err = GoInterface.nil⌝ -∗ |==> ∃ M : auth.AuthMode, ⌜M.isOn = on⌝ ∗ authStoreKit M tp) }}

/-- **What only D22 can prove at the server** (a named premise of the server in the mode `on`;
see the file header; the server's form of `auth.authSchemaBoot`): for any auth names, given the
batch lock's half of the history at the boot state, schema's auth backend `abl` over the server's
backend `d` meets the store's backend contracts, for some reader resource `R` (one per reader),
batch lock contract `P f`, write token `T` and constructor's critical section `Pre Q Post`, from
the backend resources `NewAuthStore`'s axiom takes, given back with its post's buckets after
`Post`. -/
def authSchemaSrv : IProp GF :=
  iprop(□ ∀ (γa : auth.AuthNames) (lg abl : Loc) (d : mvcc.KBReal) (W Pk : IProp GF) (qo : Qp)
      (r : GMap GoString backend.BktData),
    ⌜lg ≠ null⌝ -∗
    ⌜(r.lookup go!"auth").getD ∅ = ∅ ∧ (r.lookup go!"authUsers").getD ∅ = ∅ ∧
      (r.lookup go!"authRoles").getD ∅ = ∅⌝ -∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.schema.authBackend go!"be" abl ↦□
      (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
        #d.be : GoInterface) -∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.schema.authBackend go!"lg" abl ↦□ lg -∗
    backend.isBackend d.γB d.P W Pk d.be -∗ backend.bOpen d.γB qo -∗
    backend.plHook d.γB func.nil -∗ ownToks d.γB.wb 2 -∗ backend.rbOwn d.γB r -∗
    auth.authLockI (.on γa) auth.bootState -∗
    |==> ∃ (R P : IProp GF) (f : val) (T Pre Q Post : IProp GF),
      auth.authBackendOk (authBkIface abl) R (.on γa) ∗
      auth.authWBackendOkR (authBkIface abl) (.on γa) P f T ∗
      □ ({{ T }} (App (Val #(methods
          (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBackend.ty)
          go!"CreateAuthBuckets" #abl)) (Val #())) {{ RET #(); T }}) ∗
      T ∗ mvcc.csContract P f Pre Q Post ∗
      ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (), R) ∗
      (Post -∗ backend.bOpen d.γB qo ∗ backend.plHook d.γB func.nil ∗
        backend.rbOwn d.γB (authBucketsAfter r)))

instance authSchemaSrv_persistent : Persistent (authSchemaSrv (GF := GF)) := by
  unfold authSchemaSrv; infer_instance

end defs

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]
variable [auth_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- **The kit in the mode `off`**, of `NewAuthStore`'s axiom. -/
theorem authStoreKit_off (h30 : auth.NewAuthStore.spec (GF := GF) (hG := hG)) (tp : GoInterface) :
    ⊢ authStoreKit (GF := GF) .off tp := by
  iunfold authStoreKit
  iexists iprop(True)
  isplitr
  · itrivial
  iintro !> %lg %ab %abl %d %W %Pk %qo %r %cost %Φ !> ⟨-, Hpre⟩ HΦ
  iapply (h30 lg ab tp cost abl d W Pk qo r) $$ Hpre
  iintro !> %st ⟨Ho, Hh, Hr, %RD, %stl, %Hst, Hbe, Hsl, #Hreq, #Hok⟩
  iapply HΦ
  iframe Ho Hh Hr
  iexists RD, stl
  iframe Hbe Hsl Hreq
  isplitr
  · ipureintro; exact Hst
  isplitr
  · iExactEq Hok; rfl
  unfold authApplyRes
  itrivial

/-- **`authSrvTP false`**, of `NewTokenProvider`'s proof and `NewAuthStore`'s axiom. -/
theorem authSrvTP_off (h25 : auth.NewTokenProvider.spec (GF := GF) (hG := hG))
    (h30 : auth.NewAuthStore.spec (GF := GF) (hG := hG)) :
    authSrvTP (GF := GF) false := by
  intro lg opts iw ttl
  iintro %Φ ⟨#Hpkg, %Hlg, -⟩ HΦ
  iapply (h25 lg opts iw ttl) $$ [Hpkg]
  · iframe Hpkg; ipureintro; exact Hlg
  iintro !> %tp %err ⟨%Htp, -⟩
  iapply HΦ
  isplitr
  · ipureintro; exact Htp
  iintro -
  imodintro
  iexists .off
  isplitr
  · ipureintro; rfl
  iapply (authStoreKit_off h30 tp)

set_option maxRecDepth 16384 in
/-- **The kit in the mode `on γa`** (see the file header): the store's proof in the mode `on γa`
at the boot state, over D22's named premise, with the admin side's authority, the batch lock's
half and the other half of the latest state's variable at the boot state, and the provider's
contract with its admin resource `A`. -/
theorem authStoreKit_on
    (h_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (h_Int : zap.Int'.spec (GF := GF) (hG := hG))
    (h_Revision : auth.authStore.Revision.spec (GF := GF) (hG := hG))
    (h_commit : auth.authStore.commitRevision.spec (GF := GF) (hG := hG))
    (h_metrics : auth.authStore.setupMetricsReporter.spec (GF := GF) (hG := hG))
    (h_refresh : auth.authStore.refreshRangePermCache.spec (GF := GF) (hG := hG))
    (hCtx : auth.authStore.AuthInfoFromCtx.spec (GF := GF) (hG := hG))
    (hTLS : auth.authStore.AuthInfoFromTLS.spec (GF := GF) (hG := hG))
    (hPut : auth.authStore.IsPutPermitted.spec (GF := GF) (hG := hG))
    (hRange : auth.authStore.IsRangePermitted.spec (GF := GF) (hG := hG))
    (hDel : auth.authStore.IsDeleteRangePermitted.spec (GF := GF) (hG := hG))
    (hAdmin : auth.authStore.IsAdminPermitted.spec (GF := GF) (hG := hG))
    (hEn : auth.authStore.IsAuthEnabled.spec (GF := GF) (hG := hG))
    (hD22 : ⊢ authSchemaSrv (GF := GF))
    (tp : GoInterface) (γa : auth.AuthNames) (A : IProp GF) :
    auth.tokenProviderOkA tp (.on γa) A ∗ A ∗ auth.authOwn (.on γa) [auth.bootState] ∗
      auth.authCurHalf γa auth.bootState ∗ auth.authLockI (.on γa) auth.bootState ⊢
      authStoreKit (GF := GF) (.on γa) tp := by
  iintro ⟨#HtpA, HA, Hown, Hcur, HI⟩
  iunfold authStoreKit
  iexists iprop(A ∗ auth.authOwn (.on γa) [auth.bootState] ∗ auth.authCurHalf γa auth.bootState ∗
    auth.authLockI (.on γa) auth.bootState)
  iframe HA Hown Hcur HI
  iintro !> %lg %ab %abl %d %W %Pk %qo %r %cost %Φ !> ⟨⟨HA, Hown, Hcur, HI⟩, #Hpkg, %Hlg, %Htp,
    %Hfit, %Hab, #Habbe, #Hablg, #HB, Hopen, Hhook, Hwb, Hrbo, %Hr⟩ HΦ
  ihave #HD := hD22
  -- (E2k) the fuel at the history the store starts at (`[bootState, bump bootState]`)
  ihave Hfu := auth.authFuel_boot (GF := GF)
  imod Hfu
  iunfold authSchemaSrv at HD
  ihave HD' := HD $$ %γa %lg %abl %d %W %Pk %qo %r [] [] Habbe Hablg HB Hopen Hhook Hwb Hrbo HI
  · ipureintro; exact Hlg
  · ipureintro; exact Hr
  imod HD' with ⟨%R, %P, %f, %T, %Pre, %Q, %Post, #Hrdok, #HwokR, #HCreate, HT, Hcs, HRs, Hback⟩
  subst Hab
  wp_apply (auth.newAuthStore_on h_Warn h_Int h_Revision h_commit h_metrics h_refresh lg
      (authBkIface abl) tp cost
      (interface.mk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBackend.ty)
        #abl) γa R P f T A Pre Q Post [auth.bootState] auth.bootState rfl auth.bootState_permsFit
      ⟨auth.bootState, List.mem_singleton_self _, rfl⟩)
    $$ [$Hpkg $Hrdok $HwokR $HCreate $HT $Hcs $HtpA $HA $Hown $Hcur]
    as %st ⟨%stp, %hs', %Hst, #Hinv, HWR, HtpAd, HPost, Hown', %Hhs', Hslots⟩
  · iframe; isplitr
    · ipureintro; exact Hlg
    ipureintro; rfl
  ihave ⟨Hopen, Hhook, Hrbo⟩ := Hback $$ HPost
  iunfold auth.authWRAt at HWR
  icases HWR with ⟨⟨Hbe, #Hwok⟩, HT', Hen, Hca⟩
  -- (E2k) the boot state's revision is `0`: the history `[bootState, bump bootState]`, its fuel
  have hhs' : hs' = [auth.bootState, auth.bump auth.bootState] := by
    rcases Hhs' with ⟨h, -⟩ | ⟨-, h⟩
    · exact absurd rfl h
    · exact h
  ihave ⟨#HisReq, #HisAuth⟩ := authSrvContracts_on hCtx hTLS hPut hRange hDel hAdmin hEn h_Revision
    stp R γa $$ [$Hpkg $Hinv]
  subst hhs'
  -- (E2v) the halves tied to the start's history, whose states are disabled
  ihave ⟨Hown', HX⟩ := auth.tieRes_of_disabled stp γa [auth.bootState, auth.bump auth.bootState]
    (by intro s hs; simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl <;> rfl) $$ [Hown' Hen Hca]
  · iframe Hown' Hen Hca
  ihave HAR : authApplyRes (.on γa) stp $$ [Hown' Hfu HT' HX HtpAd]
  · unfold authApplyRes
    iexists [auth.bootState, auth.bump auth.bootState], P, f, T, (authBkIface abl)
    iunfold auth.authOwnFu
    iframe Hown' Hfu HT' HX HtpAd Hwok
  iapply HΦ
  iframe Hopen Hhook Hrbo
  iexists (auth.authRd stp R (.on γa)), stp
  subst Hst
  iframe HisReq HisAuth HAR
  isplitr
  · ipureintro; rfl
  isplitl [Hbe]
  · iunfold authBeOn
    iexists abl, lg
    iframe Hbe Habbe Hablg
    ipureintro; exact Hlg
  ihave Hsl := BigSepL.bigSepL_sep_eqv.2 $$ [Hslots HRs]
  · iframe Hslots HRs
  iapply (replicate_mono _ (auth.authRd stp R (.on γa)) _
    (by iintro ⟨⟨He, Hc, Hb⟩, HR⟩; unfold auth.authRd; iframe He Hc Hb HR)) $$ Hsl

/-- **`authSrvTP true`** (see the file header): the simple provider, its names the auth names'
token names, the auth names allocated over the boot state, the kit in the mode `on`. -/
theorem authSrvTP_on (h25 : auth.NewTokenProvider.spec (GF := GF) (hG := hG))
    (hValid : auth.ValidSpec (GF := GF) (hG := hG))
    (h_Debug : zap.Logger.Debug.spec (GF := GF) (hG := hG))
    (h_String : zap.String.spec (GF := GF) (hG := hG))
    (h_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (h_Int : zap.Int'.spec (GF := GF) (hG := hG))
    (h_Revision : auth.authStore.Revision.spec (GF := GF) (hG := hG))
    (h_commit : auth.authStore.commitRevision.spec (GF := GF) (hG := hG))
    (h_metrics : auth.authStore.setupMetricsReporter.spec (GF := GF) (hG := hG))
    (h_refresh : auth.authStore.refreshRangePermCache.spec (GF := GF) (hG := hG))
    (hCtx : auth.authStore.AuthInfoFromCtx.spec (GF := GF) (hG := hG))
    (hTLS : auth.authStore.AuthInfoFromTLS.spec (GF := GF) (hG := hG))
    (hPut : auth.authStore.IsPutPermitted.spec (GF := GF) (hG := hG))
    (hRange : auth.authStore.IsRangePermitted.spec (GF := GF) (hG := hG))
    (hDel : auth.authStore.IsDeleteRangePermitted.spec (GF := GF) (hG := hG))
    (hAdmin : auth.authStore.IsAdminPermitted.spec (GF := GF) (hG := hG))
    (hEn : auth.authStore.IsAuthEnabled.spec (GF := GF) (hG := hG))
    (hD22 : ⊢ authSchemaSrv (GF := GF)) :
    authSrvTP (GF := GF) true := by
  intro lg opts iw ttl
  iintro %Φ ⟨#Hpkg, %Hlg, %Hon⟩ HΦ
  obtain ⟨hopts, httl⟩ := Hon rfl
  iapply (h25 lg opts iw ttl) $$ [Hpkg]
  · iframe Hpkg; ipureintro; exact Hlg
  iintro !> %tp %err ⟨%Htp, Hres⟩
  iapply HΦ
  isplitr
  · ipureintro; exact Htp
  iintro %Herr
  icases Hres with (%Hno | ⟨%p, %γt, %γf, %Hp, -, #Hok, HA, -⟩)
  · exfalso; rcases Hno with h | h
    · exact h hopts
    · omega
  obtain ⟨-, rfl⟩ := Hp
  imod (auth.authBoot_alloc (GF := GF) γt γf) with ⟨%γa, %Hγ, Hown, Hcur, HI⟩
  obtain ⟨hγt, hγf⟩ := Hγ
  subst hγt hγf
  ihave #HtpA := auth.tokenSimple_okA_run hValid h_Debug h_String p γa $$ [$Hpkg $Hok]
  imodintro
  iexists (.on γa)
  isplitr
  · ipureintro; rfl
  iapply (authStoreKit_on h_Warn h_Int h_Revision h_commit h_metrics h_refresh hCtx hTLS hPut hRange
    hDel hAdmin hEn hD22 _ γa (auth.simpleAdmin p)) $$ [$HtpA $HA $Hown $Hcur $HI]

end proof

end EtcdGrove
end Perennial
