# auth-lease S3c Draft: the server couplings and the served lease registrations, at auth on with leases

2026-11-15 · branch `auth-lease` (lean `6c7ff6d645`, S3a, S3a2, S3b landed) · plan: `notes/auth-lease-handoff.md`
("S3c", the S3b decision D6, "Left"), `notes/auth-lease-scope.md` §2.3 (the four couplings, the entry points, the
expiry arm), §3 (trusted text), §7; the S3b Draft §5 (D6's sketch). Probe: `Scratch/S3cProbe.lean` (untracked; copy
`/shared/tmp/auth-lease-s3c/S3cProbe.lean`), §9. Reviews: `/shared/tmp/auth-lease-s3c/review-r*.md`.

**Revision 1 (2026-11-15).**

## 0. What S3c does, and what it leaves

After S3b the auth-on apply thread and request side handle grants, revocations and leased puts and transactions at
the revocable mode, but no built auth-on server reaches them: four couplings make "auth on" imply "no lease granted",
and `NewServer` proves them. S3c removes them:

1. the grant guard `srvGrantGuard lg on` stops being `False` at auth on (§1);
2. the boot slot `lease.bootCfg` stops requiring `on = true → m = .none` (§2; **hub change**);
3. `lease.srvInvAt` loses `□ (⌜on⌝ → srvLessorNil s)` and its `on` parameter (§3; hub slot);
4. `srvUberOn`, `srv_uberKVL(_on)`, `srvUberOn_kv`, the three apply specs and the auth component's `acLessor` lose
   the `srvLessorNil(M)` premise; `srvLessorNil`, `srvLessorNilM`, `lookupNil_of_guard`, `apply.lookupNil` go (§3).

With them: `NewServer`'s auth-on construction (§4), the expiry arm's auth-off premise (§5, Q2: `leasesNoExpiry`
kept at auth on), the `NewLessor` docstring (§6, **trusted text**), and the S3b decision D6, the gRPC lease handlers'
contracts at the mode and etcdstart's lease registrations at auth on (§7).

**Why removing `srvLessorNil` is sound now.** Since S2 the apply layer's latest-state checks no longer assume the
lessor finds no lease: `srv_uberKVL` already discards its `srvLessorNil` premise (`UberOn.lean:134`, `⟨#Hpkg, #Hb,
#Hst, -⟩`) and nothing in `apply/` takes `apply.lookupNil` (grep: only its definition, `AuthApplyLatest.lean:145`,
and docstrings). The premise is dead weight that `NewServer` pays for with the coupling.

**Left.** S4: the client library (`Lease.Grant`/`Revoke`, `WithLease`, the leased put through the gRPC KV path,
whose `putPermitM_of_dep` keeps lease `0`), the read handlers at auth on (`LeaseTimeToLive`, `LeaseLeases`,
`LeaseKeepAlive`: `etcdLeaseReadAt` stays auth-off registrations), the closed theorem. S5: expiry with auth on
(`WithRoot`'s root-token branch). The cleanup stage after S3c: the mode divergence (§8).

## 1. The grant guard (`InvApplier.lean:519`)

```lean
-- old
def srvGrantGuard (lg on : Bool) : w64 → IProp GF := fun _ => iprop(⌜lg = true ∧ on = false⌝)
-- new (decision C1)
def srvGrantGuard (lg on : Bool) : w64 → IProp GF :=
  fun _ => iprop(⌜lg = true ∧ (on = true → lease.leasesNoExpiry)⌝)
```

The Scope (§2.3) said `⌜lg = true⌝`, with `run`'s expiry arm discharging auth off "from the channel's payload,
`¬ leasesNoExpiry`, and the new `bootCfg` row". **`run` does not hold the `bootCfg` row**: it holds `lease.runCfg
lm m` (`srvBuilt`'s `%Hslg`, from `lease.bootCfg_run`), which has no auth mode. Giving it one changes `runCfg`
(a slot of `LeaseRun`, read by `memberBoot`, `newServerMode`, every restart path). **C1** puts the row in the guard
instead: every lease the lessor holds, and every lease of an expired slice, carries "with auth on, no lease expires",
which `NewServer` proves at the grant guard from `bootCfg` (§4) and `run` combines with the payload (§5). The
guard is a predicate the server picks for `NewLessor` (`GA`, a parameter of the axiom): the axiom's text is
unchanged and was already used at a non-`False` guard (auth off, `lg = true`), so no new trust (Scope §3).

Laws: `srvGrantGuard_false` (used only by `lookupNil_of_guard`) **deleted**; `srvGrantGuard_expired` restated:

```lean
-- old
lease.expiredLeases (srvGrantGuard lg on) ls ⊢ ⌜lg = true ∧ on = false⌝
-- new
lease.expiredLeases (srvGrantGuard lg on) ls ⊢ ⌜lg = true ∧ (on = true → lease.leasesNoExpiry)⌝
```

and a new law for the expiry arm, `srvGrantGuard_expired_off : ⌜¬ lease.leasesNoExpiry⌝ ∗ lease.expiredLeases
(srvGrantGuard lg on) ls ⊢ ⌜lg = true ∧ on = false⌝` (probed: `expired_authOff`). The docstrings of
`srvGrantGuard` and `lessorOk` (`InvApplier.lean:505-518, 545-555`) lose "auth off is required" and say C1.

Meaning only (text unchanged): `lessorOk lg on` (its `expiredC` payload), `lease.lessorExpiredC lp (srvGrantGuard lg
on)`, `LessorOk.lean:83` (`lessorOk_of_lessorInv`), and the exported `Results.lean:1192` (its statement names
`srvGrantGuard lg on`): the payload's guard is weaker at `on = true` (no longer `False`), so these say more.

## 2. The boot slot `lease.bootCfg` (`LeaseApi.lean:67`) — **hub change (Q7)**

```lean
-- old
@[no_expose] def lease.bootCfg (lm : lease.Mode) (m : lease.Mode) (on : Bool) : Prop :=
  lm = m ∧ (on = true → m = .none) ∧ (m = .mono → lease.leasesNoExpiry) ∧
    (m = .revocable → srvRevokeLevels (GF := GF) ∧ srvRevokeOpen (GF := GF) (hG := hG))
-- new (the Scope's row)
@[no_expose] def lease.bootCfg (lm : lease.Mode) (m : lease.Mode) (on : Bool) : Prop :=
  lm = m ∧ (on = true → m = .revocable → lease.leasesNoExpiry) ∧ (m = .mono → lease.leasesNoExpiry) ∧
    (m = .revocable → srvRevokeLevels (GF := GF) ∧ srvRevokeOpen (GF := GF) (hG := hG))
```

With auth on, a cluster may grant leases (monotone or revocable); in either granting mode no lease expires during the
run (the monotone mode's row already says so; the new row adds it for the revocable mode at auth on). Auth off
unchanged. At `m = .none` the slot is what it was (both rows vacuous).

Laws (`LeaseApi.lean`):

| law | old | new |
|---|---|---|
| `lease.bootCfg_none` | any `on` | unchanged text |
| `lease.bootCfg_mono` | `(hon : on = false)` | `hon` dropped (auth on admitted) |
| `lease.bootCfg_lm`, `lease.bootCfg_run` | | unchanged text |
| `lease.bootCfg_auth` | `on = true → lm = .none` | **deleted** (its one user, `NewServer.lean:421`'s `Hlgon`, goes, §4) |
| `lease.bootCfg_noExpiry` (new) | | `bootCfg lm m on → on = true → lm ≠ .none → lease.leasesNoExpiry` |
| `lease.bootCfg_of_run` | `(hon : on = true → m = .none)` | `(hon : on = true → m = .revocable → lease.leasesNoExpiry)` |

Callers: `etcdstart/newServerMode.lean:104, 228` pass `fun h => absurd h (by decide)` at `on = false`; unchanged
text, it still type-checks at the new `hon` (probed). The header comment's "Couplings" paragraph and
`NewServer.specG`'s comment at `lease.bootCfg` (`Spec/…/NewServer.lean:234-240`, "with auth on no lease granted")
are restated.

**The monotone mode at auth on** is admitted by the Scope's row. S3a's model admits grants at `lm ≠ .none`
(`grantPropOk`), and `srvGrantFresh`'s monotone branch reads the lessor's mode, both mode-generic; no S3c consumer
reads auth on at `mono`, and no closed theorem runs it. If the Prove step finds an auth-on proof that is not generic
in the granting mode, the fallback is the narrower row `on = true → m = .none ∨ (m = .revocable ∧ leasesNoExpiry)`,
reported (a hub text change).

## 3. The lessor premise: `srvInvAt`, `srvUberOn`, the apply specs, `acLessor`

**`lease.srvInvAt` (`LeaseApi.lean:132`, sealed hub slot).** Its first conjunct is dropped, and with it the auth
mode, which nothing else in the body reads (decision C2):

```lean
-- old
@[no_expose] def lease.srvInvAt (on : Bool) (s : Loc) (E : apply.AEnv GF) (m : lease.Mode) (σ₀ : lease.LSnap) :=
  iprop(□ (⌜on = true⌝ → srvLessorNil s) ∗ srvPeerRt s ∗ srvLessorRd s (mvcc.api.mvccLeases E.γ) ∗
    lease.lessorRdPool … ∗ lease.lessorModeIs … (decide (m = .mono)) ∗ lease.lessorAt … 0 σ₀)
@[no_expose] def lease.srvInv (on : Bool) (s : Loc) (E : apply.AEnv GF) (m : lease.Mode) := lease.srvInvAt on s E m (∅, ∅, ∅)
-- new
@[no_expose] def lease.srvInvAt (s : Loc) (E : apply.AEnv GF) (m : lease.Mode) (σ₀ : lease.LSnap) :=
  iprop(srvPeerRt s ∗ srvLessorRd s (mvcc.api.mvccLeases E.γ) ∗
    lease.lessorRdPool … ∗ lease.lessorModeIs … (decide (m = .mono)) ∗ lease.lessorAt … 0 σ₀)
@[no_expose] def lease.srvInv (s : Loc) (E : apply.AEnv GF) (m : lease.Mode) := lease.srvInvAt s E m (∅, ∅, ∅)
```

Hub texts this changes: `NewServer.specG`'s post `lease.srvInv on srv E m` → `lease.srvInv srv E m`
(`Spec/…/NewServer.lean:372`); `NewServer.specR`'s `lease.srvInvAt false …` → `lease.srvInvAt …`
(`Spec/…/NewServerR.lean:150`); every law of the slot drops `on` (`srvInvAt_intro`/`srvInv_intro` also drop the
conjunct from their premise; `_first`, `_peerRt`, `_grantedAt`, `srvLeaseRd_srvInv`, …). `lease.srvInvAt_lessorNil`,
`lease.srvInv_lessorNil` **deleted**. Users of the deleted laws: `examples/etcd/auth/startServer.lean:153`,
`examples/etcd/auth3/startMember.lean:169` (proof bodies of closed examples; the line goes).
*Alternative (C2'):* keep the unused `on` (no signature change; `lit-mode` keeps `srvInvAt false` twice).

**`srvUberOn` (`ServerOnDefs.lean:260`).** As the Scope:

```lean
-- old:  (∀ γc : auth.AuthBkNames, srvLessorNil s -∗ ∃ stl : Loc, srvAuthStoreAddr s ↦□ … ∗ apply.uberKVC …) ∗ …
-- new:  (∀ γc : auth.AuthBkNames, ∃ stl : Loc, srvAuthStoreAddr s ↦□ … ∗ apply.uberKVC …) ∗ …
```

`srvUberOn_kv` (`ServerOnDefs.lean:337`), `srv_uberKVL` (`UberOn.lean:133`), `srv_uberKVL_on` (`UberOn.lean:159`)
drop the conjunct `srvLessorNil s` from their premise. **Exported:** `Results.lean:1754, 1766` restate
`srv_uberKVL`/`srv_uberKVL_on` (their statements lose `∗ srvLessorNil s`; `Results.lean:1750`'s docstring).

**The apply specs** (exported in `interface/`? no: no `etc/api` list covers the server; they are proved internal
specs), each drops `srvLessorNilM E.authOn s ∗` from its precondition, and its docstring's sentence:
`EtcdServer.apply.spec` (`Spec/…/EtcdServer__apply.lean:101`), `applyEntries.spec` (`__applyEntries.lean:81`),
`applyEntryNormal.spec` (`__applyEntryNormal.lean:86`), `ModeSpecs.lean:148`'s `applyEntryNormal.specOn`
(`srvLessorNil s`).

**The auth component's `acLessor` (`AuthComp.lean:146`; the component's statements frozen by the user,
2026-11-04).** Its body is `srvLessorNilM C.isOn s`. Decision **C3**:
- **(a), recommended:** delete `acLessor` and its laws (`srvLessorNilM_eq`, `acLessor_on`, `acLessor_off`,
  `acLessor_persistent`), and the conjunct `acLessor C s` from `EtcdServer.Start.spec` (`Spec/…/EtcdServer__Start.lean:48`),
  `EtcdServer.start.spec` (`__start.lean:58`), `EtcdServer.applyAll.spec` (`__applyAll.lean:73`), `AuthCompRows`'
  `"#Hlnil" ∷ acLessor C s` (`AuthCompRows.lean:370`) and `run`'s loop row (`EtcdServer__run.lean:194`). Each is a
  premise removed (the specs are stronger); the frozen component loses one sealed predicate that says nothing.
- (b): keep `acLessor`, its body `True` in both modes, `acLessor_intro : ⊢ acLessor C s` in place of `_on`/`_off`
  (no spec text changes; a vacuous slot left for the cleanup stage).

Users: `etcdstart/StartStop.lean:83` (`acLessor_off`), `auth/startServer.lean:179`, `auth3/startMember.lean:195`
(`acLessor_on`), `ModeSpecs.lean:612-620`: proof bodies only.

**Deleted:** `srvLessorNil` (`ServerOnDefs.lean:245`), `srvLessorNilM` (+ `_false`, `_true`, `_persistent`;
`UberOn.lean:60`), `lookupNil_of_guard` (`UberOn.lean:75`), `apply.lookupNil` (`apply/AuthApplyLatest.lean:145`,
unused), the `match-mode` allow line `::srvLessorNilM::` (`etc/mode-allow.txt:62`). Docstrings restated:
`UberOn.lean:1-23`, `ServerOnDefs.lean:7, 251-258`, `apply/AuthApplyLatest.lean:13`, `apply/UberKVLBase.lean:8`,
`apply/AuthApplyLatestPut.lean:4`, `InvRequest.lean:215`, `LeaseGrant.lean:36-41`, `LeaseApi.lean:1-26, 116-128`,
`auth/startServer.lean:9`, `Spec/…/EtcdServer__applyAll.lean:38`, `__start.lean:34`, `__apply.lean:51`,
`__applyEntries.lean:44`, `__applyEntryNormal.lean:52`.

## 4. `NewServer`'s auth-on construction

`NewServer.specG`'s text: only the slot `lease.srvInv` (§3, C2) and its comments change; its premise
`lease.bootCfg ρ.rd.kv.lm m on` keeps its text with the new body (§2). Proof (`NewServer.lean`):
- `Hlgon` (`:421`) deleted; the grant guard's proof in `srvGrantable` (`:2390-2404`) at `lg = true` in either auth
  mode: `⟨rfl, fun hon => lease.bootCfg_noExpiry Hlbc hon hlm⟩` (probed: `newServer_guard`);
- the `Hlnil` block (`:770-773`) and the `HLnil` block (`:1906-1911`) deleted; `lease.srvInv_intro` without them;
- `kvInvM on`, `srvKVInvsOn`'s rows: nothing new (S3a dropped `γr.kv.lg = false`; `srvKVInvsOn`'s `lm = E.lm`
  holds at any lease mode).

`NewServerR` (auth off, `lease.bootCfg … false`): spec text changes only by C2; proof: the guard's proof at
`on = false` (`:638`, `⟨hg, rfl⟩` → `⟨hg, fun h => absurd h (by decide)⟩`, probed: `newServerR_guard`), the
`Hlnil`/`HLnil` blocks (`:653-655`, `:1827`) deleted.

The brief's "`NewServer`/`NewServerR`'s spec premise `on → lg = false`" is `lease.bootCfg`'s row (§2): neither spec
states it separately (`NewServer.lean:421`'s `Hlgon` is derived from the slot).

## 5. `revokeExpiredLeases` and `run`'s expiry arm (Q2: `leasesNoExpiry` kept at auth on)

```lean
-- old (Spec/…/EtcdServer__revokeExpiredLeases.lean:51)
      lease.expiredLeases (srvGrantGuard E.lg E.authMode.isOn) ls ∗
      srvRevokeCtx s E ρ γr γg ∗ ⌜ρ.rd.kv.lm = .revocable ∧ srvRevokeLevels (GF := GF)⌝ ∗
-- new
      lease.expiredLeases (srvGrantGuard E.lg E.authMode.isOn) ls ∗
      srvRevokeCtx s E ρ γr γg ∗ ⌜ρ.rd.kv.lm = .revocable ∧ srvRevokeLevels (GF := GF) ∧ E.authOn = false⌝ ∗
```

The Scope's text. Its proof takes `hoff` from the new conjunct instead of `srvGrantGuard_expired`'s second
(`EtcdServer__revokeExpiredLeases.lean:69-70`); the rest unchanged (`srvRevokeCtx_views … hoff`,
`srvRevokeCtx_withRoot … hoff`). Docstring: "auth off follows from the slice's grant guard" → "auth off is a
premise (with auth on no lease expires, `lease.bootCfg`; S5 lifts it)".

`run`'s expiry arm (`EtcdServer__run.lean:1465-1470`): `hCoff` from `srvGrantGuard_expired_off` with the payload's
`%Hnx` (probed: `expired_authOff`), then passes `⟨hlm, hlev, hoff⟩`; the mode split after it unchanged (`none`: dead
by `γr.kv.lg = false`; `mono`: dead by `Hnx`; `revocable`: the call). `run`'s spec text is unchanged. So with auth on
the arm is dead in every granting mode (`leasesNoExpiry`), and `WithRoot`'s auth-on branch stays unreached (S5).
`authStore__WithRoot.lean:34`'s docstring: "runs with auth off (`srvGrantGuard`, …)" → "runs with auth off (the
premise of `revokeExpiredLeases`, from the slice's guard and the payload's `¬ leasesNoExpiry`)".

## 6. The `NewLessor` docstring — **trusted text** (`Spec/go_etcd_io/etcd/server/v3/lease/NewLessor.lean:197-201`)

A docstring sentence of the axiom `lease.NewLessor.wp_proof`; no statement changes (the axiom's text takes `GA` as a
parameter). Exact wording:

Old (lines 197-201):
```
  concurrent readers, which no etcd process reaches: the clause takes no slot. (The auth plan's
  E3zb, 2026-10-28) A lease it returns has the grant guard `GA` of its id: every lease of the map
  was granted (`lessorAuth`'s `leaseGranted`, kept by `Grant`, `Revoke` and `Recover`, which empties
  the map), and the lock's acquisition is the step that strips the guard's agreement's later (a
  server whose guard is `False`, `srvGrantGuard`, finds no lease: `lookupNil_of_guard`).
```

New:
```
  concurrent readers, which no etcd process reaches: the clause takes no slot. (The auth plan's
  E3zb, 2026-10-28) A lease it returns has the grant guard `GA` of its id: every lease of the map
  was granted (`lessorAuth`'s `leaseGranted`, kept by `Grant`, `Revoke` and `Recover`, which empties
  the map), and the lock's acquisition is the step that strips the guard's agreement's later.
  (Auth-lease S3c, 2026-11-15: until then the server's guard was `False` with auth on, so a lookup
  found no lease there, `lookupNil_of_guard`, deleted; the server's guard, `srvGrantGuard`, is now
  `False` only in a cluster that grants no lease.)
```

The first four lines are unchanged except the parenthesis at the end of the fourth; the meaning of the clause is
unchanged (it never depended on the guard's choice).

## 7. D6: the gRPC lease handlers' contracts at the mode, and etcdstart's lease registrations at auth on

S3b's `EtcdServer.LeaseGrant.spec`/`LeaseRevoke.spec` are at `isServerReqM E.authOn` with the permit
`leaseGrantPermitM E.authOn ρ.raft ρ.kv (hdrBoundM true s E (ok ctx)) ttl Q` and the result `leaseGrantResM E.authOn …`
(`LeaseReqOn.lean`). Their v3rpc callers instantiate them at auth off. D6 carries the mode up to the gRPC
registrations, as the KV path does (`kvDepOwnM`, `kvPutOk_of_serverM`, `etcdPutSpecOn`), without twins: one contract
at the mode, its off instance today's by a `_false` law.

**7.1 The contracts (`v3rpc/InvLease.lean`).** The token-level permit and result (the KV path's `hdrBoundT` over the
caller's token `tok`, `hdrBoundM_tok`):

```lean
-- new (LeaseReqOn.lean, beside the server's): the permit and the result at a token, not a context
def leaseGrantResT (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (tok : Option GoString)
    (ttl id : w64) (Q : w64 → KVState → IProp GF) : IProp GF :=
  match on with | false => iprop(True)
  | true => iprop(∃ (hm : apply.HeaderModel) (L : List EntryModel), hdrBoundT s E.authMode tok hm ∗
      pubAfterM true E ρ (apply.withHeader (irrLeaseGrant id ttl) hm) L ∗
      Q id (kvStateOf (kvModelOn ρ.kv srvAuthSt0 L) (kvLeasesOn ρ.kv srvAuthSt0 L)))
def leaseRevokeResT (on …) (tok) (id : w64) (Q : KVState → IProp GF) : IProp GF   -- likewise, with `grantedAt`
-- (`leaseGrantResM on s E ρ ctx ttl resp Q ⊢ ∃ id, ID ↦□ id ∗ leaseGrantResT on s E ρ (ctxTokenOf ctx) ttl id Q`)
```

The contracts at the mode, **new names beside today's** (decision C5): `lessorGrantOkGM`, `lessorGrantOkM`,
`lessorRevokeOkM`, `raftLessorM`; today's `lessorGrantOkG s E S G R`, `lessorGrantOk`, `lessorRevokeOk`, `raftLessor`
keep their texts (`InvLease.lean:150-158, 135-141, 168-173, 180`) as the auth-off contracts their many off users read
(`InvLeaseGrant`, `InvLeaseRead`, client `LeaseGrantServed`, etcdstart), equal to the new ones at `false` by `_false`
bridges:

```lean
def lessorGrantOkGM (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (S : IProp GF)
    (G : w64 × w64 → w64 → IProp GF) (R : w64 × w64 → Prop := fun _ => True) : IProp GF :=
  iprop(∀ (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (r : Loc) (m : w64 × w64)
      (Q : w64 → KVState → IProp GF),
    {{ S ∗ context.isContext ci cd ∗ grpcRunCtx ci ∗ leaseGrantReqIs r m ∗ leaseGrantReqIdOwn r m.2 ∗ ⌜R m⌝ ∗
        leaseGrantPermitM on ρ.raft ρ.kv (hdrBoundT s E.authMode (auth.ctxTokenOf (GoInterface.ok ci))) m.1 Q }}
      (App (App (Val (srvM s go!"LeaseGrant")) (Val #(GoInterface.ok ci))) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); S ∗ leaseGrantAns E resp err ∗
        (⌜err ≠ GoInterface.nil⌝ ∨ ∃ id : w64,
          structFieldRef etcdserverpb.LeaseGrantResponse go!"ID" resp ↦□ id ∗ G m id ∗
          leaseGrantResT on s E ρ (auth.ctxTokenOf (GoInterface.ok ci)) m.1 id Q) }})
def lessorRevokeOkM (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (S : IProp GF) : IProp GF :=
  iprop(∀ ci cd r (id : w64) (Q : KVState → IProp GF),
    {{ S ∗ context.isContext ci cd ∗ grpcRunCtx ci ∗ leaseRevokeReqIs r id ∗
        leaseRevokePermitM on ρ.raft ρ.kv (hdrBoundT s E.authMode (auth.ctxTokenOf (GoInterface.ok ci))) id Q }}
      (App (App (Val (srvM s go!"LeaseRevoke")) (Val #(GoInterface.ok ci))) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); S ∗ leaseRevokeAns E resp err ∗
        (⌜err ≠ GoInterface.nil⌝ ∨ leaseRevokeResT on s E ρ (auth.ctxTokenOf (GoInterface.ok ci)) id Q) }})
-- lessorGrantOkM: lessorGrantOkGM at G := True, R := True; raftLessorM on s E ρ S := lessorGrantOkM … ∗ lessorRevokeOkM …
```

Laws: `lessorGrantOkGM_false : lessorGrantOkGM false s E ρ S G R ⊣⊢ lessorGrantOkG s E S G R` (at `false` the permit
and the result are `True`: `leaseGrantPermitM_false`, `leaseGrantResT_false`; the `∀ Q` is idle), likewise
`lessorRevokeOkM_false`, `raftLessorM_false`; `lessorGrantOkGM_mono` (today's `_mono` with `on`, `ρ`).

The server's discharges (`ServerLeaseGrant.lean`'s `lessorGrantOkLive_of_server`, `lessorGrantOkL_of_server`;
`ServerLeaseRevoke.lean`'s `lessorRevokeOk_of_server`): restated at `isServerReqM E.authOn s E ρ` (old: `isServerReq
s E ρ`), concluding the `M` contract at `E.authOn`; the permit is `_mono` from the token form to `hdrBoundM true s E
(ok ci)` by the converse of `hdrBoundM_tok` (`hdrBoundM true … ctx` and `hdrBoundT … (ctxTokenOf ctx)` are the same
proposition, by `unfold`; new law `hdrBoundT_ctx`), the result by `leaseGrantResM`'s law above. Their off callers
(the v3rpc `Results` corollaries, etcdstart) take the old contract by `_false` at `hoff` (`isServerReq_authOn`).
**Exported (v3rpc `Results.lean:2097-2135`):** `lessorGrantOkL_server`, `lessorGrantOkLive_server`,
`lessorRevokeOk_server` keep their texts (auth off, `isServerReq`), proved through the bridge; new exported
corollaries at the mode are not needed (the auth-on chain is internal until S4).

The handlers' specs (`Spec/…/v3rpc/LeaseServer__LeaseGrant.lean:40`, `__LeaseRevoke.lean:37`) take the contract at
the mode (`lessorGrantOkGM on s E ρ S G R`, `raftLessorM on s E ρ S`) and pass the caller's `Q` and permit through
(the handler forwards `ctx` and `r` unchanged: `v3rpc/lease.go` `LeaseGrant`/`LeaseRevoke`): their texts gain `on`,
`ρ`, the `Q` binder, the permit conjunct and the post's result disjunct; the off users instantiate them at
`E.authOn` with `hoff` and the bridge (not at a literal `false`). `quotaLeaseServer.LeaseGrant.spec` is generic in the
handler's `GrpcSpec` (`grpcHandlerOwnOk … Spec`): unchanged.

**7.2 The gRPC registration (client side, `client/v3`).** As `etcdPutSpecOn` (`KVServiceOn.lean:50`), metadata
specs whose permit is at the attempt's token `auth.mdTokenOf md`, written at `E.authOn` (no literal mode; the
registration lemma has `E.authOn = true`):

```lean
def etcdLeaseGrantSpecOn (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γl : GName) :
    GrpcSpecMd (GF := GF) pbLeaseGrantRequest pbLeaseGrantResponse :=
  fun md (req : w64 × w64) (Φ : LeaseGrantRespM → IProp GF) (Ψe : GoString → IProp GF) =>
    iprop((□ ∀ d, Ψe d) ∗ ⌜req.2 = W64 0⌝ ∗ ∃ Q : w64 → KVState → IProp GF,
      leaseGrantPermitM E.authOn ρ.raft ρ.kv (v3rpc.hdrBoundT s E.authMode (auth.mdTokenOf md)) req.1 Q ∗
      ∀ m : LeaseGrantRespM, ⌜m.id ≠ W64 0⌝ -∗ etcdReached (EM := v3rpc.etcdModelOfServer E ρ.rd E.authOn) m.hdr.revision -∗
        (∃ (i : Nat) (l : Loc), lease.leaseLiveFrom γl i m.id l ∗ lease.leaseReqIs γl m.id req.1) -∗
        v3rpc.leaseGrantResT E.authOn s E ρ (auth.mdTokenOf md) req.1 m.id Q -∗ Φ m)
def etcdLeaseRevokeSpecOn (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) :
    GrpcSpecMd (GF := GF) pbLeaseRevokeRequest pbLeaseRevokeResponse :=
  fun md (id : w64) Φ Ψe => iprop((□ ∀ d, Ψe d) ∗ ∃ Q : KVState → IProp GF,
      leaseRevokePermitM E.authOn ρ.raft ρ.kv (v3rpc.hdrBoundT s E.authMode (auth.mdTokenOf md)) id Q ∗
      ∀ m : LeaseRevokeRespM, etcdReached (EM := …) m.hdr.revision -∗
        v3rpc.leaseRevokeResT E.authOn s E ρ (auth.mdTokenOf md) id Q -∗ Φ m)
```

(the live grant's fact as `etcdLeaseGrantSpecLive`'s, the revocable mode's `ID = 0` as its filter; errors carry
nothing, as `etcdPutSpecOn`'s HS-4.) The off registrations (`etcdLeaseGrantAt`, `etcdLeaseGrantLiveAt`) keep their
texts.

**7.3 etcdstart (`ServedLease.lean`).** A new lemma `kv_lease_served_on`, `kv_lease_served`'s at auth on, from
`grpcUpM true` (whose `grpcLeaseUp` holds the Lease service) and `isServerReqM true`/`isServerReadM true`, in the
revocable mode: `isGrpcRpcMd addr "/etcdserverpb.Lease/LeaseGrant" (etcdLeaseGrantSpecOn s E ρ (mvcc.api.mvccLeases
E.γ)) ∗ isGrpcRpcMd addr "/etcdserverpb.Lease/LeaseRevoke" (etcdLeaseRevokeSpecOn s E ρ)`. `etcdLeaseServedAt` keeps
its text: it is the auth-off registration set (`isGrpcRpc`, at `etcdModelOfServer E γr false`), which the S3b sketch
proposed to move to `E.authOn`; but auth-on gRPC is `isGrpcRpcMd` (the token comes from the metadata), so the auth-on
set is a separate `Md` set, as the KV's is (`etcd_kv_auth_served_on`'s). `etcdLeaseServedAt` at `E.authOn` would be
a registration that only answers errors with auth on (no token reaches the server): true, useless. **Deviation from
the S3b sketch, decision C4.** The lease reads at auth on (`TimeToLive`, `Leases`, `KeepAlive`) stay S4.

**7.4 What D6 needs of the couplings.** `kv_lease_served_on` holds `isServerReqM true` and the lessor reader side at
the mode (`srvLeaseRd s E m`, from `lease.srvInv`, §3), and the registrations are reachable only if `NewServer` builds
an auth-on granting server: §§1–4.

## 8. Mode-gate impact (the cleanup stage comes next)

Expected (`etc/mode-check.py`, against `etc/mode-baseline.txt`):
- `match-mode`, etcdserver: **−1** (`srvLessorNilM`'s match; its allow line goes).
- `lit-mode`, etcdserver: **−4** (`srvLessorNilM_false`/`_true`'s bridges; `srvInvAt false` twice, by C2), plus the
  `simp only [srvLessorNilM_true/false, …]` sites if counted (lemma names, not applications: not counted).
- `lit-mode`, v3rpc: **+3 to +5**, all `bridge` (`leaseGrantResT`/`leaseRevokeResT`'s `_false`, `lessorGrantOkGM_false`,
  `lessorRevokeOkM_false`, `raftLessorM_false`); the contracts and the handler specs are at `on`, their off users at
  `E.authOn` with `hoff`.
- `lit-mode`, client/v3: **0** (the `On` specs at `E.authOn`).
- `lit-mode`, etcdstart: **+1 to +2** (`kv_lease_served_on`'s `grpcUpM true`, `isServerReqM true`, unless stated at
  `E.authOn` with `hon : E.authOn = true`: the form preferred).
- `twin`: **0** (no `specOn`/`wp_proofOn` added; `ModeSpecs.lean`'s `applyEntryNormal.specOn` loses a conjunct only).

Net: about −1 to −5 over the gated packages. C3 (a) also removes one `AuthC`-indexed sealed predicate (not counted).

## 9. Probe (`Scratch/S3cProbe.lean`, checked clean with `etc/lean-check.py -a`)

The riskiest point is the expiry arm: with the coupling gone, nothing in `run`'s context says auth is off when a slice
arrives, and `revokeExpiredLeases` (and `WithRoot`, auth off only) needs it. Probed: the guard C1 and its expiry law
(`srvGrantGuardC_expired`); auth off from the payload and the guard (`expired_authOff`); the new boot slot
(`bootCfgC`) with `_none`, `_mono` (no `hon`), `_run`, `_of_run` (and `newServerMode`'s `absurd` argument still
fits), `_noExpiry`; `NewServer`'s guard at a granting cluster in either auth mode (`newServer_guard`), `NewServerR`'s
at auth off (`newServerR_guard`); the guard at auth off equivalent to today's (`guard_off`). The `srvLessorNil`
removal needs no probe (§0: already unused by the apply layer). D6 is not probed (definitions over existing
vocabulary; the Prove step's risk is the handlers' proofs, +2–3 days as estimated).

## 10. Statements this changes (for the Freeze)

**Hub (Q7, for the coordinator):** `lease.bootCfg`'s body (§2); `lease.srvInvAt`/`lease.srvInv`'s signature and body
(§3, C2), so `NewServer.specG`'s and `NewServer.specR`'s slot occurrences.

**Trusted text:** `NewLessor.lean:197-201`'s docstring sentence (§6). No axiom statement, opaque or `sorry` changes;
`etc/tcb-baseline.txt` unchanged.

**Frozen or exported text:**

| statement | where | change |
|---|---|---|
| `srvGrantGuard`, `srvGrantGuard_expired` | `InvApplier.lean:519, 537` | C1 (§1); `_false` deleted, `_expired_off` new |
| `lease.bootCfg` + laws | `LeaseApi.lean` | §2 |
| `lease.srvInvAt`, `lease.srvInv` + laws | `LeaseApi.lean` | §3 (C2); `_lessorNil` laws deleted |
| `NewServer.specG`, `NewServer.specR` | `Spec/…/NewServer{,R}.lean` | the slot without `on` (C2); comments |
| `srvUberOn`, `srvUberOn_kv`, `srv_uberKVL`, `srv_uberKVL_on` | `ServerOnDefs`, `UberOn` | `srvLessorNil` dropped (§3) |
| exported `Results.lean:1754, 1766` | server `Results` | the same |
| `EtcdServer.apply.spec`, `applyEntries.spec`, `applyEntryNormal.spec`, `.specOn` | `Spec/…`, `ModeSpecs` | `srvLessorNilM` dropped (§3) |
| `acLessor` (C3 a) and `Start.spec`, `start.spec`, `applyAll.spec`, `AuthCompRows`, `run`'s loop row | `AuthComp` (frozen), `Spec/…` | deleted / conjunct removed |
| `EtcdServer.revokeExpiredLeases.spec` | `Spec/…/EtcdServer__revokeExpiredLeases.lean` | `∧ E.authOn = false` (§5) |
| `lessorGrantOkG`, `lessorGrantOk`, `lessorRevokeOk`, `raftLessor` | v3rpc `InvLease` | unchanged; new `…M` contracts beside them (C5, §7.1) |
| `LeaseServer.LeaseGrant.spec`, `.LeaseRevoke.spec` | `Spec/…/v3rpc/` | the contract at `on`, `Q`, the permit, the result (§7.1) |
| `lessorGrantOkLive_of_server`, `lessorGrantOkL_of_server`, `lessorRevokeOk_of_server` | v3rpc | at `isServerReqM E.authOn`, the `M` contract (§7.1); the exported `…_server` corollaries keep their texts |

**New:** `srvGrantGuard_expired_off`, `lease.bootCfg_noExpiry`, `leaseGrantResT`/`leaseRevokeResT` (+ laws),
`hdrBoundT_ctx`, `lessorGrantOkGM`, `lessorGrantOkM`, `lessorRevokeOkM`, `raftLessorM` (+ `_false`, `_mono`), `etcdLeaseGrantSpecOn`, `etcdLeaseRevokeSpecOn`, `kv_lease_served_on`.
**Deleted:** `srvLessorNil`, `srvLessorNilM` (+ laws), `lookupNil_of_guard`, `apply.lookupNil`,
`srvGrantGuard_false`, `lease.bootCfg_auth`, `lease.srvInv{,At}_lessorNil`, `acLessor` (+ laws, C3 a).

**Meaning only:** `lessorOk`, `lease.lessorExpiredC … (srvGrantGuard …)`, `Results.lean:1192` (§1); `run.spec`
(text unchanged; its expiry arm's proof changes); every caller of `NewServer.specM true` (an auth-on server may now be
built at a granting mode).

**Closed theorems: none change in text.** authkv (`etcd_auth_safe`) and auth3 (`etcd_auth3_safe`) run auth on at lease
mode `none` (`lease.bootCfg_none`, unchanged), where the new row is vacuous; their proofs lose the
`srvInv_lessorNil`/`acLessor_on` lines (`auth/startServer.lean:153, 179`, `auth3/startMember.lean:169, 195`, proof
bodies). The lease examples (leasegrant, leaseexpiry, k8s) run auth off: `newServerMode`'s `absurd` argument fits the
new `hon`. etcdstart's `ServedLease.lean` gains a lemma; its existing statements are unchanged. The land stop checks
it with the diff of `Proof/github_com` statements and `gen-interface --check` on every `etc/api` list (etcdstart's
covers `ServedLease`: the new lemma is an interface addition, regenerated and committed).

## 11. Decisions asked

- **C1. The guard carries `on = true → leasesNoExpiry`** (§1), instead of the Scope's `⌜lg = true⌝` with `runCfg`
  gaining the auth mode. **Recommended** (probed; `runCfg` and its readers untouched).
- **The hub change (Q7):** `lease.bootCfg`'s row as the Scope's (§2), monotone mode at auth on admitted.
  **Recommended**; fallback (narrower row) only if the Prove step finds an auth-on proof not generic in the mode.
- **C2. `lease.srvInvAt`/`srvInv` drop their `on`** (§3; a hub slot signature, `NewServer.specG`/`specR` texts).
  **Recommended** (−2 `lit-mode`); alternative C2' keeps the unused parameter.
- **C3. `acLessor`**: (a) deleted with its conjunct in four specs and two rows, **recommended**; (b) kept with body
  `True`.
- **C5. D6's contracts as new `…M` names beside today's auth-off ones** (§7.1), so that the off users
  (`InvLeaseGrant`, `InvLeaseRead`, client `LeaseGrantServed`, etcdstart) and the exported `…_server` corollaries keep
  their texts. **Recommended**; alternative: one contract at `on` and every off user at `false` (more `lit-mode`).
- **C4. D6's auth-on registrations as a separate `Md` set** (`kv_lease_served_on`, `etcdLease*SpecOn`), not
  `etcdLeaseServedAt` at `E.authOn` (§7.3). **Recommended.**
- **The `NewLessor` docstring** (§6): the exact new wording. **Recommended.**

## 12. Order of work (after the Freeze), estimate 4–6 agent-days (couplings 2–3, D6 2–3)

1. §1–§2: the guard, the boot slot and their laws; `NewServer`/`NewServerR`'s guard proofs; `run`'s expiry arm;
   `revokeExpiredLeases.spec` and its proof; `newServerMode`.
2. §3: `srvInvAt` (C2) and its callers; `srvUberOn` and the three `srv_uberKVL` lemmas; the apply specs; `acLessor`
   (C3); deletions; docstrings; §6's docstring.
3. §7: `leaseGrantResT`/`leaseRevokeResT`, the contracts, the server discharges, the handler specs and proofs, v3rpc
   `Results`; `etcdLease*SpecOn`; `kv_lease_served_on`.
4. Land-stop checks: merge lean, full build (flock, 64G), `tcb-report --check` (870/4), `gen-interface` on every
   `etc/api` list (etcdstart regenerated for the new lemma), bounds and mode gates (baseline lowered where it drops),
   closed statements unchanged (diff of `Proof/github_com` statements), STATUS, handoff, status-history.
