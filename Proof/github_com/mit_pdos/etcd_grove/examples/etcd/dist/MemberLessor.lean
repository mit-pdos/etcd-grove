/-
**A started member whose lessor is at a given name** (F2's P-L1, PROPOSED with `Serve_dist_proposed.spec`
(`AuthServeProposed.lean`, the merged F2/F7 proposal), 2026-11-26; the auth-lease review's F2, `/shared/tmp/coord-03/rev-f7c-report.md`). Lean-first (no Rocq
counterpart). Definitions only (and `memberUpOnL_eq`, by `rfl`). Also here, moved from `AuthServeProposed.lean` so that the Spec files can
import them (F7 step 3's preparation): `authNamesFreshD` (a member's fresh auth authorities, with auth on) and
`etcdstart.memberUpOnL` (`memberUpOn` with the lessor at `γl`).

`etcdstart.memberUpL s ρ E₀ lg γn id m γl` is `etcdstart.memberUp s ρ E₀ lg γn id m` with its server's
environment's lessor name `mvcc.api.mvccLeases E.γ` equal to `γl`: the name the lessor was made at
(`lease.NewLessor.specAt`, through `NewServer.specG_dist_proposed`'s `mvccLeases E.γ = γl`). Through
`Serve_dist`'s exclusive resources (the member's start), it ties the view's `Γ.ls mid` to the serving member's
real lessor; `etcdAddr_set` mints address facts for any `Γ`, so `Serve_dist`'s premise is the only place that can.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Defs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthApplyRes
public import Proof.go_etcd_io.etcd.server.v3.auth.Boot
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorSlot

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]

/-- **`γa`'s fresh authorities, which P-A1 moves from `NewServer` to the start** (one per name of
`auth.AuthNames`, each at the value the server's boot allocates today). Today they are allocated inside
`NewServer` (its post's `∃ γa`): the history and its companions by `auth.authBoot_alloc` /
`auth.authHist_alloc` (`auth/Boot.lean`, `auth/Model.lean`), inside `NewAuthStore`'s boot proof
(`auth.newAuthStore_boot`, `auth_store_boot_on` in `etcdserver/Results.lean`); the token names by the
simple provider (`newTokenProviderSimple.lean`: `γf` an empty map, `γt` by `auth.tokAlloc γf`); the
readiness cell `γy` by `srvTpInv_alloc` (`InvStart.lean`). With P-A1 the start allocates them per member
(as `clusterAllocN` does the KV names) and hands them over:
* `hist`: the history's whole authority at the boot state `[bootState]` (`authHist_alloc` at
  `hs := [bootState]`; split into `authHist`'s three quarters and `authHistRev`'s quarter, `authHist_full`);
* `cur`: the latest state's ghost variable, whole, at `bootState` (`authHist_alloc` splits it in halves);
* `tok`: the issued tokens' authority, none issued (`auth.tokAuth γa.tok γa.fresh ∅`, `tokAlloc`);
* `fresh`: the issue rights' authority, none minted (`authFreshInit (.on γa)`);
* `pub`: the published index's authority at `0` (`auth.authPubAuth γa 0`);
* `fen`, `fca`: the `enabled` field's and the permission cache's ghost variables, at `false` and
  `(null, 0)`;
* `cap`: the cap's authority at `[bootState, bump bootState]` (`auth.capAuth`; its lower bound
  `capLb` follows from it);
* `bk`: the current backend's ghost variable, unset (any value), whole;
* `succ`: the succession token;
* `rdt`: the readers' tickets' authority, none out (`ownTokAuth γa.rdt 0`);
* `rdy`: the readiness cell's mono-nat authority at `0`, whole (`srvTpInv_alloc`'s; `NewServer` keeps a
  half and puts the other in the readiness invariant, which names the server's location).
Not here: the simple provider's token keeper map (`γk`, a ghost map of `Loc`s, not an `AuthNames`
field: the provider's own, allocated in `NewServer` as now) and the backend's names (`d.γB`, the
member's backend, allocated by `NewServer`'s backend construction). -/
def authNamesFreshD (γa : auth.AuthNames) : IProp GF :=
  iprop(monoListAuthOwn γa.hist 1 [auth.bootState] ∗
    ghostVar γa.cur 1 auth.bootState ∗
    auth.tokAuth γa.tok γa.fresh ∅ ∗
    authFreshInit (.on γa) ∗
    auth.authPubAuth γa 0 ∗
    ghostVar γa.fen 1 false ∗
    ghostVar γa.fca 1 ((null : Loc), 0) ∗
    auth.capAuth γa [auth.bootState, auth.bump auth.bootState] ∗
    (∃ γ0 : GName × GName × GName, ghostVar γa.bk 1 γ0) ∗
    token γa.succ ∗
    ownTokAuth γa.rdt 0 ∗
    monoNatAuthOwn γa.rdy 1 0)

end defs

namespace etcdstart

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`memberUp` with the lessor at `γl`** (PROPOSED, see the file header): `memberUp`'s body verbatim, and
`mvcc.api.mvccLeases E.γ = γl` for its environment `E`. -/
def memberUpL (s : Loc) (ρ : ReqNames) (E₀ : apply.AEnv GF) (lg : Loc) (γn : NetNames GF)
    (id : w64) (m : lease.Mode) (γl : GName) : IProp GF :=
  iprop(∃ (E : apply.AEnv GF) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (γw : GName),
    ⌜envAgree E E₀ ∧ E.authOn = false ∧ cfg.Logger' = lg ∧ cfg.TracerOptions' = slice.nil ∧
      cfg.WatchProgressNotifyInterval' = 0 ∧ mvcc.api.mvccLeases E.γ = γl⌝ ∗
    srvServeStock s E ∗ srvRunReadStock s ρ.rd ∗
    isServerReq s E { ρ with wait := γw } ∗ isServerRead s E ρ.rd ∗ srvGoRes s ∗ srvLgReader s ∗
    ([∗list] _x ∈ List.replicate memberReadN (), srvReadReader s ρ.rd) ∗
    srvWatchBuilt s E ∗ srvServeFacts s E cfg ∗
    srvBemuReader s ∗
    srvPeerCtl γn s id ∗ srvLeaseRd s E m ∗
    (∃ dd : GoString, srvStopRight s E ρ.rd.raft.raft ρ id dd))

/-- `memberUpL` forgets the lessor's name: `memberUp` (F7 step 2, until `Serve_dist` takes `memberUpL`). -/
theorem memberUpL_memberUp (s : Loc) (ρ : ReqNames) (E₀ : apply.AEnv GF) (lg : Loc) (γn : NetNames GF)
    (id : w64) (m : lease.Mode) (γl : GName) :
    memberUpL (GF := GF) s ρ E₀ lg γn id m γl ⊢ memberUp s ρ E₀ lg γn id m := by
  iintro Hup
  iunfold memberUpL at Hup
  iunfold memberUp
  icases Hup with ⟨%E, %cfg, %γw, %HE, Hrest⟩
  iexists E, cfg, γw
  isplitr
  · ipureintro; exact ⟨HE.1, HE.2.1, HE.2.2.1, HE.2.2.2.1, HE.2.2.2.2.1⟩
  iexact Hrest

/-- **`memberBuilt` with the lessor at `γl`** (F7 step 2): `etcdstart.memberBuilt`'s body verbatim, and
`mvcc.api.mvccLeases E.γ = γl` for its environment `E` (`NewServer.specGAt`'s post); `Start` turns it into
`memberUpL` (`etcdstart.wp_Start_builtL`). -/
def memberBuiltL (s : Loc) (ρ : ReqNames) (E₀ : apply.AEnv GF) (lg : Loc) (γn : NetNames GF)
    (id : w64) (N : Nat) (served : Bool) (m : lease.Mode) (γl : GName) : IProp GF :=
  iprop(∃ (γA : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF)
      (γrn : RNNames GF) (b : GoInterface) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig)
      (γk : GName) (τ : SrvTr GF),
    ⌜envAgree E E₀ ∧ E.authOn = false ∧ cfg.Logger' = lg ∧ cfg.TracerOptions' = slice.nil ∧
      cfg.WatchProgressNotifyInterval' = 0 ∧ mvcc.api.mvccLeases E.γ = γl⌝ ∗
    srvServeStock s E ∗
    srvWatchBuilt s E ∗
    isServerBuilt s γA ci TM E ρ ρ.rd (srvEr ρ E₀ (W64 0) (W64 0) bootKV id (srvTrKey γn γk) (srvTrStopK γk))
      γrn b (W64 0) (W64 0) (W64 0) bootKV N ∗
    srvServeBuilt s E cfg ∗ srvSVRes s E ∗ srvMonitorsOff s ∗ srvMonitorRes s ∗
    srvReadyCloser s E ∗ srvNetMember γn s id τ ∗ srvTrTok γn τ ∗
    memberPeerServeRes γn τ served ∗
    srvLeaseRd s E m ∗ srvStop.keep s cfg E γrn γk)

end defs

section defsL
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`memberUpOn` with the lessor at `γl`** (PROPOSED, F7 review C's F2, 2026-11-26; F2's `memberUpL`
with auth on): `memberUpOn`'s body verbatim, at the lease mode `m`, and `mvcc.api.mvccLeases E.γ = γl` for its
environment `E` (the name the lessor was made at: `NewServer.specG_dist_proposed`'s `γl`, P-L1). The request and
read views are at the auth slot `AuthC.on γa`'s mode (`(AuthC.on γa).isOn`, which is `true`: `memberUpOnL_eq`). -/
def memberUpOnL (s : Loc) (ρ : ReqNames) (E₀ : apply.AEnv GF) (lg : Loc) (γn : NetNames GF)
    (id : w64) (γa : auth.AuthNames) (m : lease.Mode) (γl : GName) : IProp GF :=
  iprop(∃ (E : apply.AEnv GF) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (γw : GName),
    ⌜envAgree E E₀ ∧ E.authMode = .on γa ∧ cfg.Logger' = lg ∧ cfg.TracerOptions' = slice.nil ∧
      cfg.WatchProgressNotifyInterval' = 0 ∧ mvcc.api.mvccLeases E.γ = γl⌝ ∗
    srvServeStock s E ∗ srvRunReadStock s ρ.rd ∗
    isServerReqM (AuthC.on γa).isOn s E { ρ with wait := γw } ∗ isServerReadM (AuthC.on γa).isOn s E ρ.rd ∗
    srvAuthLb s E ∗
    srvGoRes s ∗ srvLgReader s ∗
    ([∗list] _x ∈ List.replicate memberReadN (), srvReadReader s ρ.rd) ∗
    srvWatchBuilt s E ∗ srvServeFacts s E cfg ∗
    srvBemuReader s ∗
    srvPeerCtl γn s id ∗
    □ (srvTLSId s -∗ False) ∗ srvAuthStoreOn s E.RD ∗
    srvLeaseRd s E m)

/-- **`memberUpOnL`'s body with the views at a mode `b` that is `true`** (the F9 AuthC-slot refactor,
2026-11-26): the definition before it (the views at the literal `true`), so `memberUpOnL` means what it meant
(`Serve_dist`'s auth-on premise unchanged). By `rfl`: `(AuthC.on γa).isOn` is `true` by definition. -/
theorem memberUpOnL_eq (s : Loc) (ρ : ReqNames) (E₀ : apply.AEnv GF) (lg : Loc) (γn : NetNames GF)
    (id : w64) (γa : auth.AuthNames) (m : lease.Mode) (γl : GName) (b : Bool) (hb : b = true) :
    memberUpOnL s ρ E₀ lg γn id γa m γl =
      iprop(∃ (E : apply.AEnv GF) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (γw : GName),
        ⌜envAgree E E₀ ∧ E.authMode = .on γa ∧ cfg.Logger' = lg ∧ cfg.TracerOptions' = slice.nil ∧
          cfg.WatchProgressNotifyInterval' = 0 ∧ mvcc.api.mvccLeases E.γ = γl⌝ ∗
        srvServeStock s E ∗ srvRunReadStock s ρ.rd ∗
        isServerReqM b s E { ρ with wait := γw } ∗ isServerReadM b s E ρ.rd ∗ srvAuthLb s E ∗
        srvGoRes s ∗ srvLgReader s ∗
        ([∗list] _x ∈ List.replicate memberReadN (), srvReadReader s ρ.rd) ∗
        srvWatchBuilt s E ∗ srvServeFacts s E cfg ∗
        srvBemuReader s ∗
        srvPeerCtl γn s id ∗
        □ (srvTLSId s -∗ False) ∗ srvAuthStoreOn s E.RD ∗
        srvLeaseRd s E m) := by
  subst hb; rfl

end defsL

end etcdstart
end EtcdGrove
end Perennial
