# auth-lease S3c Draft: the server couplings and the served lease registrations, at auth on with leases

2026-11-15 · branch `auth-lease` (lean `6c7ff6d645`, S3a, S3a2, S3b landed) · plan: `notes/auth-lease-handoff.md`
("S3c", the S3b decision D6, "Left"), `notes/auth-lease-scope.md` §2.3 (the four couplings, the entry points, the
expiry arm), §3 (trusted text), §7; the S3b Draft §5 (D6's sketch). Probe: `Scratch/S3cProbe.lean` (untracked; copy
`/shared/tmp/auth-lease-s3c/S3cProbe.lean`), §9. Reviews: `/shared/tmp/auth-lease-s3c/review-r*.md`.

**Revision 6 (2026-11-15), FROZEN** (etcd-grove-81's decisions, conditional on round 5, met: `questions.md`, "S3c
Freeze"): review round 5 (`/shared/tmp/auth-lease-s3c/review-r5.md`, fresh `spec-reviewer`) found no first-tier problem;
§1–§5 sound; the monotone mode at auth on generic everywhere the reviewer looked (`InvRest.lean:1018-1041`,
`ImageLeasesOn.lean:83-156`, `RestOn`, `KVModelM`, `ApplyEntryOn`; a leased put at auth on only in the revocable mode,
`ReqOn.lean:938, 1347`). Second tier applied: S1 `lessorGrantOkL_of_server` unchanged (§7.1, §10); S2
`srvAuthAt_of_viewsM` in `AuthGuard.lean`, no `hon`; S3 `lessorRevokeOkM_server`, the metadata quota bridges and the
client's metadata handler lemmas written out (§7.5); S4 the `Nx` tie named (§7.5); S6 `run_job_body`/`isServerRunC`
rows; S7 sites and docstrings; S8 line references; S9 options recorded (§11). **S5 not applied**: §6.2's wording is
the coordinator's decided text; the reviewer's extra clause ("`NewServer` and `NewServerR`") is listed for the
coordinator in the handoff.

**Revision 5 (2026-11-15)**: review round 4 (`/shared/tmp/auth-lease-s3c/review-r4.md`, fresh `spec-reviewer`; §1–§6
clean, both trusted wordings accurate): F1 `grpcUpOn` gains the Lease conjunct (the law alternative dropped), the
etcdstart `Defs` interface diff and the closed examples' destructuring sites listed; F2 two new exported v3rpc
corollaries at the mode (`lessorGrantOkLiveM_server`, `lessorRevokeOkM_server`) and `srvAuthAt_of_viewsM`'s text; F3
the revoke registration is the quota server's promoted method: metadata versions of `quotaLease_revokeHandlerOk` and
`quotaLease_grantHandlerOk_of`. Second tier: §6.1's owner (`lease.NewLessor.spec`'s docstring), off callers at a
literal `false` with an explicit `ρ` (§8), `lessorGrantOkL_of_server` unchanged. **Round 5 not run.**

**Revision 4 (2026-11-15)**: review round 3 (`/shared/tmp/auth-lease-s3c/review-r3.md`, fresh `spec-reviewer`): F1 the
registration lemma restated in `client/v3` from the persistent `grpcServerAt` (not the exclusive `grpcUpM true`), and
etcdstart's `grpcUpOn` keeping the Lease service (an etcdstart API change, listed); F2 §7.4 writes out the handler
specs, the quota spec, `leaseRevokeResT`'s body and the client lemma statements; F3 §6.2's wording (the auth-on row
reaches `run` through the guard, not `runCfg`). Second tier: `srvRevokeOpen`'s meaning change and `isServerRunC`'s
`acLessor` row listed. **Round 4 not yet run.**

**Revision 3 (2026-11-15)**: review round 2 (`/shared/tmp/auth-lease-s3c/review-r2.md`, fresh `spec-reviewer`): F1 the
seven exported `client/v3` results over `raftLessor` → C5′ (the off contracts kept, the mode's beside them, recorded as a
`pair`) recommended; F2 `srvAuthAtM` dropped (`srvAuthAt` is already at `E.authMode`; its auth-on source from the
mode's views); F3 `etcd_lease_auth_served_on` in etcdstart (where `grpcUpM` lives); F4 the quota wrappers: one metadata spec
each, the plain form a corollary (the `quotaKVServer.Put` precedent); F5 `acLessor` in `isServerBuilt_offC`'s statement
and `applyAll.spec`'s post listed. Second tier: §6.2 names `lease.runCfg`; the `ResT` results without a new `match`;
C6's grant-id rights (`kvInvOn_alloc_boot` already takes `hpo`).

**Revision 2 (2026-11-15)**: review round 1 (`/shared/tmp/auth-lease-s3c/review-r1.md`, fresh `spec-reviewer`):
F1 C2 → C2′ recommended (keeping `on`; C2 changed etcdstart's `Defs` API and v3rpc's `lessorGrantOkL_server`); F2 the
quota wrapper needs the metadata form (§7.1, D6 re-estimated); F3 the `leaseGrantResM` law at `true`; F4 the deposit
design is decision C7; F5 the `NewLessor` docstring without the server parenthesis, and the opaque `leasesNoExpiry`'s
docstring listed as trusted text (§6); F6 C6 (§4a), unprobed; F7 `etcd_lease_auth_served_on`'s premises (`srvAuthAtM`, no
`srvLeaseRd`) and etcdstart's `memberBootOn` (`lg = false`) as C8; F8 the contracts redefined in place at the mode
(C5 revised). Second tier applied (§1's direction, `hdrBoundM_tok`, `ctxTokenOf_md`, the module of `leaseGrantResT`,
the extra proof sites and docstrings, the monotone mode marked unprobed).

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
`srvGrantGuard lg on`): the payload's guard is weaker at `on = true` (no longer `False`), so `lessorOk` promises
less of a slice (a weaker contract; its consumers are the expiry arm's, §5, which get auth off from the payload).

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
are restated, and so are the docstrings of `lease.bootCfg` (`LeaseApi.lean:47-66`), `lease.bootCfg_mono` and
`lease.bootCfg_of_run` (review r5 S7).

**The monotone mode at auth on** is admitted by the Scope's row. S3a's model admits grants at `lm ≠ .none`
(`grantPropOk`), and `srvGrantFresh`'s monotone branch reads the lessor's mode, both mode-generic; no S3c consumer
reads auth on at `mono`, and no closed theorem runs it; **not probed**. If the Prove step finds an auth-on proof that is not generic
in the granting mode, the fallback is the narrower row `on = true → m = .none ∨ (m = .revocable ∧ leasesNoExpiry)`,
reported (a hub text change).

## 3. The lessor premise: `srvInvAt`, `srvUberOn`, the apply specs, `acLessor`

**`lease.srvInvAt` (`LeaseApi.lean:132`, sealed hub slot).** Its first conjunct is dropped. Decision **C2′
(recommended, rev 2)**: the auth mode `on` stays a parameter, unused by the body, so `NewServer.specG`/`specR`,
etcdstart's `Defs` API (`srvLeaseRd`, `interface/…/etcdstart/Defs.txt:13, 17, 67, 164`) and v3rpc's exported
`lessorGrantOkL_server` keep their texts (the cleanup stage may drop it); C2 (rev 1: drop `on`) changes them all:

```lean
-- old
@[no_expose] def lease.srvInvAt (on : Bool) (s : Loc) (E : apply.AEnv GF) (m : lease.Mode) (σ₀ : lease.LSnap) :=
  iprop(□ (⌜on = true⌝ → srvLessorNil s) ∗ srvPeerRt s ∗ srvLessorRd s (mvcc.api.mvccLeases E.γ) ∗
    lease.lessorRdPool … ∗ lease.lessorModeIs … (decide (m = .mono)) ∗ lease.lessorAt … 0 σ₀)
@[no_expose] def lease.srvInv (on : Bool) (s : Loc) (E : apply.AEnv GF) (m : lease.Mode) := lease.srvInvAt on s E m (∅, ∅, ∅)
-- new
@[no_expose] def lease.srvInvAt (on : Bool) (s : Loc) (E : apply.AEnv GF) (m : lease.Mode) (σ₀ : lease.LSnap) :=
  iprop(srvPeerRt s ∗ srvLessorRd s (mvcc.api.mvccLeases E.γ) ∗
    lease.lessorRdPool … ∗ lease.lessorModeIs … (decide (m = .mono)) ∗ lease.lessorAt … 0 σ₀)
@[no_expose] def lease.srvInv (on : Bool) (s : Loc) (E : apply.AEnv GF) (m : lease.Mode) := lease.srvInvAt on s E m (∅, ∅, ∅)
```

Under C2′ no hub text changes but the body; `srvInvAt_intro`/`srvInv_intro` drop the conjunct from their premise.
`lease.srvInvAt_lessorNil`,
`lease.srvInv_lessorNil` **deleted**. Users of the deleted laws: `examples/etcd/auth/startServer.lean:153`,
`examples/etcd/auth3/startMember.lean:169` (proof bodies of closed examples; the line goes).

**`srvUberOn` (`ServerOnDefs.lean:260`).** As the Scope:

```lean
-- old:  (∀ γc : auth.AuthBkNames, srvLessorNil s -∗ ∃ stl : Loc, srvAuthStoreAddr s ↦□ … ∗ apply.uberKVC …) ∗ …
-- new:  (∀ γc : auth.AuthBkNames, ∃ stl : Loc, srvAuthStoreAddr s ↦□ … ∗ apply.uberKVC …) ∗ …
```

`srvUberOn_kv` (`ServerOnDefs.lean:337`), `srv_uberKVL` (`UberOn.lean:133`), `srv_uberKVL_on` (`UberOn.lean:159`)
drop the conjunct `srvLessorNil s` from their premise (proof sites: `UberKit.lean:67-68`,
`EtcdServer__applyEntryNormal.lean:1839, 1998`). **Exported:** `Results.lean:1754, 1766` restate
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
  `EtcdServer.start.spec` (`__start.lean:58`), `EtcdServer.applyAll.spec` (`__applyAll.lean:73`, and its post's `acLessor`, `:126`), `isServerBuilt_offC`'s
conclusion (`ModeSpecs.lean:612-616`), `AuthCompRows`'
  `"#Hlnil" ∷ acLessor C s` (`AuthCompRows.lean:370`) and `run`'s loop row (`EtcdServer__run.lean:194`). Each is a
  premise removed (the specs are stronger) or, in `applyAll.spec`'s post and `isServerBuilt_offC`, a `True`-valued
  conjunct dropped from a conclusion; the frozen component loses one sealed predicate that says nothing.
- (b): keep `acLessor`, its body `True` in both modes, `acLessor_intro : ⊢ acLessor C s` in place of `_on`/`_off`
  (no spec text changes; a vacuous slot left for the cleanup stage).

Users: `etcdstart/StartStop.lean:83` (`acLessor_off`), `auth/startServer.lean:179`, `auth3/startMember.lean:195`
(`acLessor_on`): proof bodies only.

**Deleted:** `srvLessorNil` (`ServerOnDefs.lean:245`), `srvLessorNilM` (+ `_false`, `_true`, `_persistent`;
`UberOn.lean:60`), `lookupNil_of_guard` (`UberOn.lean:75`), `apply.lookupNil` (`apply/AuthApplyLatest.lean:145`,
unused), the `match-mode` allow line `::srvLessorNilM::` (`etc/mode-allow.txt:62`). Docstrings restated:
`UberOn.lean:1-23`, `ServerOnDefs.lean:7, 251-258`, `apply/AuthApplyLatest.lean:13`, `apply/UberKVLBase.lean:8`,
`apply/AuthApplyLatestPut.lean:4`, `InvRequest.lean:215`, `LeaseGrant.lean:36-41`, `LeaseApi.lean:1-26, 116-128`,
`auth/startServer.lean:9`, `Spec/…/EtcdServer__applyAll.lean:38`, `__start.lean:34`, `__apply.lean:51`,
`__applyEntries.lean:44`, `__applyEntryNormal.lean:52`.

## 4. `NewServer`'s auth-on construction

`NewServer.specG`'s text: only comments change (`Spec/…/NewServer.lean:145-146, 234-240, 372-375`; C2′); its premise
`lease.bootCfg ρ.rd.kv.lm m on` keeps its text with the new body (§2). Proof (`NewServer.lean`):
- `Hlgon` (`:421`) deleted; the grant guard's proof in `srvGrantable` (`:2390-2404`) at `lg = true` in either auth
  mode: `⟨rfl, fun hon => lease.bootCfg_noExpiry Hlbc hon hlm⟩` (probed: `newServer_guard`);
- the `Hlnil` block (`:770-773`) and the `HLnil` block (`:1906-1911`) deleted; `lease.srvInv_intro` without them;
- `kvInvM on`, `srvKVInvsOn`'s rows: nothing new (S3a dropped `γr.kv.lg = false`; `srvKVInvsOn`'s `lm = E.lm`
  holds at any lease mode).

`NewServerR` (auth off, `lease.bootCfg … false`): spec text unchanged (C2′); proof: the guard's proofs at
`on = false` (`:638` and `:2372`, `⟨hg, rfl⟩` → `⟨hg, fun h => absurd h (by decide)⟩`, probed: `newServerR_guard`), the
`Hlnil`/`HLnil` blocks (`:653-655`, `:1827`) deleted.

The brief's "`NewServer`/`NewServerR`'s spec premise `on → lg = false`" is `lease.bootCfg`'s row (§2): neither spec
states it separately (`NewServer.lean:421`'s `Hlgon` is derived from the slot).

### 4a. The auth-on cluster allocation at a lease mode (decision C6)

`NewServer` takes the KV invariant `kvInvM on ρ.rd.raft ρ.rd.kv srvAuthSt0` from its caller, which allocates it.
The auth-on allocation fixes the lease mode `none`: `srvClusterBootOn_alloc` (`NewServerAllocOn.lean:56`) builds
`γk0` at `lm = .none` (`:186-187`) and its post states `γk.lg = false` (`:65`). Its auth-off counterpart
`srvClusterBoot_alloc` (`NewServerAlloc.lean:151`) takes `(lm : lease.Mode := .none) (gp : w64 := 0)
(gps : List w64 := [gp])` (lease-mono3 step 2, 2026-11-14) and states `γk.lm = lm ∧ γk.ids.pfx = gp ∧ γk.gps = gps`.
So no auth-on granting server can be built until the auth-on allocation takes the mode. **C6 (recommended, in S3c,
about half a day):** `srvClusterBootOn_alloc` gains the same three parameters with the same defaults and premises,
its post `γk.lm = lm ∧ γk.ids.pfx = gp ∧ γk.gps = gps` in place of `γk.lg = false`; the exported restatement
(`Results.lean:~2215-2238`) likewise. Its callers (`examples/etcd/auth/MainAlloc.lean:60`,
`etcdstart/Alloc3On.lean:190`) use the defaults and derive `γk.lg = false` from `γk.lm = .none` (`KVNames.lg`): proof
bodies; their statements unchanged. `srvMemberBootOn_alloc` already takes `hpfx`/`hpo` (S3a). The 3-member revocable
mode (`Alloc3On`'s and `cluster3`'s scope premise `lm ≠ .revocable`) stays lease-mono3's and S4's. Not probed (it
mirrors the off allocation's lease-mode parameters, lease-mono3 step 2). At `lm = .revocable` the allocation also
mints the grant-id claim rights over `gps` (`kvInvOn`'s `kvGrantIds`), as the off one does (`NewServerAlloc.lean:151-170`);
`kvInvOn_alloc_boot` (`ServerOn.lean:631`) is already generic in the mode, given `kvPfxOk γk` (S3a).

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

## 6. Trusted text: the `NewLessor` docstring and the `leasesNoExpiry` docstring

No axiom statement, opaque's type or `sorry` changes; `etc/tcb-baseline.txt` unchanged. Two docstrings of the trust
base change (review r1 F5).

**6.1 `lease.NewLessor.wp_proof`** (`Spec/go_etcd_io/etcd/server/v3/lease/NewLessor.lean:197-201`, the docstring of `lease.NewLessor.spec`, which the
axiom `lease.NewLessor.wp_proof` states). The axiom takes the
guard `GA` as a parameter; the sentence names the server's instance and its deleted law. Rev 2 drops the
server-specific parenthesis (the axiom's docstring should not describe one caller's guard).

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
```

**6.2 The opaque `lease.leasesNoExpiry`** (`Proof/go_etcd_io/etcd/server/v3/lease/LessorBackend.lean:74-76`). With C1
the auth-on granting results also rest on it (through `lease.bootCfg`'s new row, the guard, and `NewLessor`'s payload
`¬ leasesNoExpiry`); the docstring's account of who takes it is stale.

Old (lines 74-76):
```
refutes it. `NewServer` takes it (gated on the cluster granting leases, `KVNames.lg = true`, review
S1) for its apply thread, the one place a grant is minted. -/
```

New:
```
refutes it. `NewServer` takes it through its boot slot `lease.bootCfg`: in the monotone lease mode
(which `run` keeps, `lease.runCfg`), and (auth-lease S3c, 2026-11-15) with auth on in either granting
mode, which the lessor's grant guard `srvGrantGuard` carries to every lease `expiredC` can deliver, so
that `run`'s expiry arm revokes with auth off only (`revokeExpiredLeases`). (Until 2026-11-04 gated on
the cluster granting leases, `KVNames.lg = true`, review S1.) -/
```

The docstring's "True of `examples/etcd/leasegrant`" paragraph stays; S4 adds the authlease example's justification
(its driver's run within the TTL of its leases) when its theorem takes the premise (Q2).

## 7. D6: the gRPC lease handlers' contracts at the mode, and the auth-on registrations

S3b's `EtcdServer.LeaseGrant.spec`/`LeaseRevoke.spec` are at `isServerReqM E.authOn` with the permit
`leaseGrantPermitM E.authOn ρ.raft ρ.kv (hdrBoundM true s E (ok ctx)) ttl Q` and the result `leaseGrantResM E.authOn …`
(`LeaseReqOn.lean`). Their v3rpc callers instantiate them at auth off. D6 carries the mode up to the gRPC
registrations, as the KV path does (`kvPutOk_of_serverM`, `quotaKVServer.Put`'s metadata spec, `etcdPutSpecOn`).

**7.0 The deposit (decision C7, review r1 F4).** The S3b sketch carried the client's update as a deposit `KVDep.lease
(d : LeaseDep)` through the handler's `KVAns` record, as the KV handlers' `kvDepOwnM`. The lease handlers have no
`KVAns`: their contracts are triples over the request (`lessorGrantOkG`). **C7 (recommended):** the contracts bind
`Q` and take the permit in their precondition, the result in their post (§7.1); the registration's spec (§7.2) hands
the permit over, as `etcdPutSpecOn` hands `kvOpAuOn` over. No `KVDep`/`LeaseDep` constructor. Alternative: the S3b
sketch's deposit, which needs a `KVAns`-like record for the lease handlers.

**7.1 The contracts at the mode, beside today's (decision C5′, rev 3; review r1 F8, r2 F1).** Rev 2 redefined
`lessorGrantOkG`, `lessorGrantOk`, `lessorRevokeOk`, `raftLessor` in place. Round 2 found that seven exported results of
`client/v3/Results.lean` take `v3rpc.raftLessor s E S` with no auth-mode fact to read it at (`etcd_leaseGrantHandlerOk`,
`etcd_leaseRevokeHandlerOk`, `etcd_leaseMethodsOk`, `etcd_lease_served`, `etcd_kv_lease_served`,
`client_lessor_isEtcdLease_served`, `client_new_isEtcdLeaseClient_served`): in place, each changes text (a literal
`false` and a `ρ` binder, +7 `lit-mode`). **C5′ (recommended):** today's four contracts keep their texts as the auth-off
contracts; new `lessorGrantOkGM`, `lessorGrantOkM`, `lessorRevokeOkM`, `raftLessorM` (`on` first, `ρ`, the permit, the
result) beside them, with `_false` laws (`lessorGrantOkGM false s E ρ S G R ⊣⊢ lessorGrantOkG s E S G R`, likewise the
others: at `false` the permit and result are `True`). The pair is recorded in `etc/mode-allow.txt` (class `pair`) and
in the handoff's "Left", for the cleanup stage, which can merge it when it reworks the client results. Alternative C5
(rev 2): in place, with the seven client results restated.

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
-- lessorGrantOkM on s E ρ S := lessorGrantOkGM on s E ρ S (fun _ _ => True); raftLessorM on s E ρ S := lessorGrantOkM … ∗ lessorRevokeOkM …
```

The token-level results (module: v3rpc, beside `hdrBoundT`, e.g. `ServerKVOn.lean` or a new `v3rpc/LeaseOn.lean`;
not `LeaseReqOn.lean`, which v3rpc imports, review r1):

Written as unfoldings of the server's results (no new `match`; review r2):

```lean
def leaseGrantResT (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (tok : Option GoString)
    (ttl id : w64) (Q : w64 → KVState → IProp GF) : IProp GF :=
  iprop(⌜on = true⌝ → ∃ (hm : apply.HeaderModel) (L : List EntryModel), hdrBoundT s E.authMode tok hm ∗
      pubAfterM on E ρ (apply.withHeader (irrLeaseGrant id ttl) hm) L ∗
      Q id (kvStateOf (kvModelOn ρ.kv srvAuthSt0 L) (kvLeasesOn ρ.kv srvAuthSt0 L)))
def leaseRevokeResT (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (tok : Option GoString)
    (id : w64) (Q : KVState → IProp GF) : IProp GF :=
  iprop(⌜on = true⌝ → ∃ (hm : apply.HeaderModel) (L : List EntryModel), hdrBoundT s E.authMode tok hm ∗
      ⌜grantedAt ρ.kv srvAuthSt0 (apply.withHeader (irrLeaseRevoke id) hm) L⌝ ∗
      pubAfterM on E ρ (apply.withHeader (irrLeaseRevoke id) hm) L ∗
      Q (kvStateOf (kvModelOn ρ.kv srvAuthSt0 L) (kvLeasesOn ρ.kv srvAuthSt0 L)))
```

Laws: `leaseGrantResT_false`, `leaseRevokeResT_false`; at `true` only (review r1 F3: at `false` `leaseGrantResM` gives no
points-to): `leaseGrantResM true s E ρ ctx ttl resp Q ⊢ ∃ id, ID ↦□ id ∗ leaseGrantResT true s E ρ (ctxTokenOf (ok ctx))
ttl id Q` (by `hdrBoundM_tok`), `leaseRevokeResM true … ⊢ leaseRevokeResT true …`; the contracts' `_mono` (today's with
`on`, `ρ`). The permit goes from the token form to the server's context form by `hdrBoundM_tok` (`hdrBoundM true s E ctx
hm ⊢ hdrBoundT s E.authMode (ctxTokenOf ctx) hm`) under `leaseGrantPermitM_mono` (the needed direction; no new law).

The server's discharges (`ServerLeaseGrant.lean`'s `lessorGrantOkLive_of_server`; `ServerLeaseRevoke.lean`'s
`lessorRevokeOk_of_server`; `lessorGrantOkL_of_server` keeps its text, its proof through the `_false` instance): at `isServerReqM E.authOn s E ρ` and `srvAuthAt s E` (already at
`E.authMode`, `AuthGuard.lean:181`; used at auth on beside `isServerReqM E.authOn`, `v3rpc/Results.lean:2087`),
concluding the `…M` contract at `E.authOn`. Its auth-on source: `srvAuthAt_of_views` (`AuthGuard.lean:242`, from the
auth-off views) generalized to the mode's views (`srvAuthAt_of_viewsM`, from `isServerReqM on`/`isServerReadM on`,
`ReqOn.lean:418, 422`, `ReadOn.lean:75, 87`): a new lemma in `AuthGuard.lean` beside `srvAuthAt_of_views` (which
client/v3 already imports), no new predicate (rev 2's `srvAuthAtM` dropped).
The off callers of the discharges (`lessorGrantOkL_server`, `lessorGrantOkLive_server`, `lessorRevokeOk_server`, etcdstart)
take today's contracts by `_false` at `hoff`; their texts unchanged.

**Texts this changes (C5′):** none of today's contracts or their users; new `…M` contracts and the discharges'
conclusions (the `lessor*_of_server` lemmas, internal: at the `…M` contract at `E.authOn`, premise `isServerReqM
E.authOn`).

**The handlers (review r1 F2).** `LeaseServer.LeaseGrant.spec`/`.LeaseRevoke.spec` (`Spec/…/v3rpc/`) take the contract
at `on` and pass `Q` and the permit through (the handler forwards `ctx` and `r` unchanged). The handlers' specs take the
`…M` contract at `on` (`lessorGrantOkGM on s E ρ S G R`; `LeaseRevoke`'s narrowed to `lessorRevokeOkM`, which is all it
calls), their off users at `E.authOn` with `hoff` and the `_false` laws. **The quota wrappers (review r2 F4):** as
`quotaKVServer.Put.spec` was, `quotaLeaseServer.LeaseGrant.spec` (`Spec/…/v3rpc/quotaLeaseServer__LeaseGrant.lean:36`) is
**replaced by one metadata spec** (`Spec : GrpcSpecMd Req Rep`, `grpcHandlerOwnOkMd`, the metadata `md` bound, with the
error clause of `quotaKVServer.Put.spec`), the plain form a corollary through the existing `grpcHandlerOwnOk_md`; its
callers (client `LeaseGrantServed`) through the corollary, texts unchanged. The revocation has no quota wrapper
(`quotaLeaseServer` embeds `LeaseServer`, whose `LeaseRevoke` is promoted); the client's revoke handler lemma gains a
metadata version (`LeaseGrantServed`'s, at `GrpcSpecMd`). The gRPC context's token is the metadata's by `auth.ctxTokenOf_md`
(`rfl`).

**7.2 The gRPC registration specs (client side, `client/v3`).** As `etcdPutSpecOn` (`KVServiceOn.lean:50`), metadata
specs whose permit is at the attempt's token `auth.mdTokenOf md`, written at `E.authOn` (no literal mode):

```lean
def etcdLeaseGrantSpecOn (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γl : GName) :
    GrpcSpecMd (GF := GF) pbLeaseGrantRequest pbLeaseGrantResponse :=
  fun md (req : w64 × w64) (Φ : LeaseGrantRespM → IProp GF) (Ψe : GoString → IProp GF) =>
    iprop((□ ∀ d, Ψe d) ∗ ⌜req.2 = W64 0⌝ ∗ ∃ Q : w64 → KVState → IProp GF,
      leaseGrantPermitM E.authOn ρ.raft ρ.kv (v3rpc.hdrBoundT s E.authMode (auth.mdTokenOf md)) req.1 Q ∗
      ∀ m : LeaseGrantRespM, ⌜m.id ≠ W64 0⌝ -∗
        etcdReached (EM := v3rpc.etcdModelOfServer E ρ.rd E.authOn) m.hdr.revision -∗
        (∃ (i : Nat) (l : Loc), lease.leaseLiveFrom γl i m.id l ∗ lease.leaseReqIs γl m.id req.1) -∗
        v3rpc.leaseGrantResT E.authOn s E ρ (auth.mdTokenOf md) req.1 m.id Q -∗ Φ m)
def etcdLeaseRevokeSpecOn (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) :
    GrpcSpecMd (GF := GF) pbLeaseRevokeRequest pbLeaseRevokeResponse :=
  fun md (id : w64) Φ Ψe => iprop((□ ∀ d, Ψe d) ∗ ∃ Q : KVState → IProp GF,
      leaseRevokePermitM E.authOn ρ.raft ρ.kv (v3rpc.hdrBoundT s E.authMode (auth.mdTokenOf md)) id Q ∗
      ∀ m : LeaseRevokeRespM, etcdReached (EM := v3rpc.etcdModelOfServer E ρ.rd E.authOn) m.hdr.revision -∗
        v3rpc.leaseRevokeResT E.authOn s E ρ (auth.mdTokenOf md) id Q -∗ Φ m)
```

(the live grant's fact as `etcdLeaseGrantSpecLive`'s, the revocable mode's `ID = 0` as its filter; errors carry nothing,
as `etcdPutSpecOn`'s HS-4.) The auth-off registrations (`etcdLeaseGrantAt`, `etcdLeaseGrantLiveAt`,
`etcdLeaseServedAt`) keep their texts: auth-on gRPC is `isGrpcRpcMd` (the token from the metadata), so the auth-on
set is a separate `Md` set, as the KV's (`etcd_kv_auth_served_on`); `etcdLeaseServedAt` at `E.authOn` (the S3b
sketch) would register specs that only answer errors with auth on (decision C4).

**7.3 The registration lemma (decision C8, review r2 F3, r3 F1).** In `client/v3`, beside
`etcd_kv_auth_served_on` (`AuthnServedOn.lean:301`), from the **persistent** `grpcServerAt` that `grpc.start'` gives
(the KV path's shape; a lease-only post from the exclusive `grpcUpM true` would leave the caller unable to register
KV and Auth too):

```lean
theorem etcd_lease_auth_served_on (addr : GoString) (ql pl s : Loc) (A : v3rpc.KVAns GF) (lcid lmid : w64)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (il im iu : GoFunc)
    (regs : List (GoString × GoFunc × GoInterface)) (γ : GName) (γa : auth.AuthNames)
    (hγa : E.authMode = .on γa) (hlm : ρ.rd.kv.lm = .revocable) (hρ : ρ.rd = γr)
    (hregs : ∀ x ∈ v3rpc.leaseRegs ql, x ∈ regs) (HL : srvLevels (GF := GF)) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReqM true s E ρ ∗ isServerReadM true s E γr ∗ □ (|==> idCred ρ.ids 1) ∗
      v3rpc.quotaLeaseServerAt ql
        ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer.ty, #pl⟩ s ∗
      v3rpc.leaseServerAt pl s A lcid lmid ∗
      srvInterceptorOk il (srvLgReader s) v3rpc.learnerReqOk ∗ srvInterceptorOk im iprop(True) v3rpc.learnerReqOk ∗
      srvInterceptorOk iu iprop(True) v3rpc.learnerReqOk ∗
      grpcServerAt addr [il, im, iu] regs γ ∗ srvRevokeBuilt s E ∗ srvRunPool s E γr ⊢
    |={⊤}=> isGrpcRpcMd addr go!"/etcdserverpb.Lease/LeaseGrant" (etcdLeaseGrantSpecOn s E ρ (mvcc.api.mvccLeases E.γ)) ∗
      isGrpcRpcMd addr go!"/etcdserverpb.Lease/LeaseRevoke" (etcdLeaseRevokeSpecOn s E ρ)
```

(`v3rpc.leaseRegs` registers `LeaseGrant` and `LeaseRevoke` on the quota server `ql`, `LeaseRevoke` being the
embedded `LeaseServer`'s promoted method, `InvGrpcStart.lean:285-289`; no `srvLeaseRd`: grant and revoke do not read the
lessor.) Its lessor contracts come from two **new exported v3rpc corollaries** (`client/v3` reaches the linked server
proofs only through v3rpc's `Results.lean`, whose `…_server` corollaries are auth off):

```lean
theorem lessorGrantOkLiveM_server (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (S : IProp GF)
    (R : w64 × w64 → Prop) (hR : ∀ m, R m → ρ.rd.kv.lm = .revocable → m.2 = W64 0) (h : srvGrantsLeases E ρ) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReqM E.authOn s E ρ ∗ srvAuthAt s E ∗ □ (|==> idCred ρ.ids 1) ∗
      □ (S -∗ srvLeadTimeReader s ∗ E.RD ∗ (srvLeadTimeReader s ∗ E.RD -∗ S)) ⊢
      lessorGrantOkGM E.authOn s E ρ S (grantLiveG E) R
theorem lessorRevokeOkM_server (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (S : IProp GF)
    (h : srvRevokesLeases E ρ) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReqM E.authOn s E ρ ∗ srvAuthAt s E ∗ □ (|==> idCred ρ.ids 1) ∗
      □ (S -∗ srvLeadTimeReader s ∗ E.RD ∗ (srvLeadTimeReader s ∗ E.RD -∗ S)) ⊢
      lessorRevokeOkM E.authOn s E ρ S
-- and (server, `AuthGuard.lean`, beside `srvAuthAt_of_views`; used from client/v3):
theorem srvAuthAt_of_viewsM (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) :
    isServerReqM on s E ρ ∗ isServerReadM on s E γr ⊢ srvAuthAt s E
```

(`lessorGrantOkL_of_server`, the history-fact form, stays as it is: no mode-indexed target is needed in S3c.) **etcdstart API change:** `grpcUpOn` (`etcdstart/Defs.lean:595`) keeps the Lease service, `grpcLeaseUp s
C.A regs`, which `grpcUpM_true` drops today: a conjunct of `grpcUpOn`'s body, at its own `C`/`regs` (a separate law
cannot tie `hregs` to them); `gen-interface` diff of etcdstart's `Defs` (`interface/…/etcdstart/Defs.txt:139`);
`grpcUpM_true`'s docstring and proof; the closed examples' destructurings `auth/Run.lean:142-143`,
`auth3/run.lean:140-141` (proof bodies; their statements unchanged).
**etcdstart's auth-on boot bundle `memberBootOn` still requires `lg = false`** (`Defs.lean:539`), so no
etcdstart-started member grants with auth on: C8 recommends lifting it in S4 with the driver's start (Scope §7.4),
listed in "Left"; alternative: in S3c (an etcdstart API change).

**7.4 The handler specs and the client's metadata lemmas, in full (review r3 F2).**

```lean
-- Spec/…/v3rpc/LeaseServer__LeaseGrant.lean (old: lessorGrantOkG s E S G R, no Q, no permit, no result)
abbrev v3rpc.LeaseServer.LeaseGrant.spec : Prop :=
  ∀ (p s : Loc) (A : v3rpc.KVAns GF) (cid mid : w64) (on : Bool) (E : apply.AEnv GF) (ρ : ReqNames) (S : IProp GF)
    (G : w64 × w64 → w64 → IProp GF) (R : w64 × w64 → Prop) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (r : Loc) (m : w64 × w64) (Q : w64 → KVState → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      v3rpc.leaseServerAt p s A cid mid ∗ v3rpc.lessorGrantOkGM on s E ρ S G R ∗ S ∗
      context.isContext ci cd ∗ grpcRunCtx ci ∗ v3rpc.leaseGrantReqIs r m ∗
      v3rpc.leaseGrantReqIdOwn r m.2 ∗ ⌜R m⌝ ∗
      leaseGrantPermitM on ρ.raft ρ.kv (v3rpc.hdrBoundT s E.authMode (auth.ctxTokenOf (GoInterface.ok ci))) m.1 Q }}
    (App (App (Val (p @!! go.GoType.PointerType v3rpc.LeaseServer.ty @!! go!"LeaseGrant"))
      (Val #(GoInterface.ok ci))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); S ∗ v3rpc.leaseGrantOut E cid mid resp err ∗
      (⌜err ≠ GoInterface.nil⌝ ∨ ∃ id : w64,
        structFieldRef etcdserverpb.LeaseGrantResponse go!"ID" resp ↦□ id ∗ G m id ∗
        v3rpc.leaseGrantResT on s E ρ (auth.ctxTokenOf (GoInterface.ok ci)) m.1 id Q) ∗
      go_etcd_io.etcd.cache.v3.srvErrOk err }}

-- Spec/…/v3rpc/LeaseServer__LeaseRevoke.lean (old: raftLessor s E S; narrowed to the revoke contract)
abbrev v3rpc.LeaseServer.LeaseRevoke.spec : Prop :=
  ∀ (p s : Loc) (A : v3rpc.KVAns GF) (cid mid : w64) (on : Bool) (E : apply.AEnv GF) (ρ : ReqNames) (S : IProp GF)
    (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (r : Loc) (m : w64) (Q : KVState → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      v3rpc.leaseServerAt p s A cid mid ∗ v3rpc.lessorRevokeOkM on s E ρ S ∗ S ∗
      context.isContext ci cd ∗ grpcRunCtx ci ∗ v3rpc.leaseRevokeReqIs r m ∗
      leaseRevokePermitM on ρ.raft ρ.kv (v3rpc.hdrBoundT s E.authMode (auth.ctxTokenOf (GoInterface.ok ci))) m Q }}
    (App (App (Val (p @!! go.GoType.PointerType v3rpc.LeaseServer.ty @!! go!"LeaseRevoke"))
      (Val #(GoInterface.ok ci))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); S ∗ v3rpc.leaseRevokeOut E cid mid resp err ∗
      (⌜err ≠ GoInterface.nil⌝ ∨ v3rpc.leaseRevokeResT on s E ρ (auth.ctxTokenOf (GoInterface.ok ci)) m Q) ∗
      go_etcd_io.etcd.cache.v3.srvErrOk err }}

-- Spec/…/v3rpc/quotaLeaseServer__LeaseGrant.lean (old: Spec : GrpcSpec, grpcHandlerOwnOk, Spec m Φ):
-- one metadata spec, as quotaKVServer.Put.spec; the handler writes r.ID, so the Own form
abbrev v3rpc.quotaLeaseServer.LeaseGrant.spec : Prop :=
  ∀ (Req Rep : ProtoMsg GF) (Spec : GrpcSpecMd Req Rep) (q s : Loc) (ls : GoInterfaceOk)
    (S : IProp GF) (m : Req.M) (Φ : Rep.M → IProp GF) (Ψe : GoString → IProp GF)
    (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (r : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      v3rpc.quotaLeaseServerAt q ls s ∗
      grpcHandlerOwnOkMd #(methods ls.ty go!"LeaseGrant" ls.v) iprop(S ∗ srvLgReader s) Spec ∗
      S ∗ v3rpc.quotaRd s ∗
      context.isContext ci cd ∗ grpcRunCtx ci ∗ Req.recv r m ∗ Req.recvOwn r m ∗
      Spec (metadata.incomingOf (GoInterface.ok ci)) m Φ Ψe }}
    (App (App (Val (q @!! go.GoType.PointerType v3rpc.quotaLeaseServer.ty @!! go!"LeaseGrant"))
      (Val #(GoInterface.ok ci))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); S ∗ v3rpc.quotaRd s ∗
      (⌜err = GoInterface.nil⌝ -∗ ∃ m' : Rep.M, Rep.send resp m' ∗ Φ m') ∗
      (⌜err ≠ GoInterface.nil ∧ go_etcd_io.etcd.cache.v3.errDesc err ∈ handlerDescs⌝ -∗
        Ψe (go_etcd_io.etcd.cache.v3.errDesc err)) ∗ go_etcd_io.etcd.cache.v3.srvErrOk err }}
-- today's plain form: a corollary through grpcHandlerOwnOk_md (GrpcSpec.md Spec, Ψe := fun _ => True)
```

The client's metadata lemmas (`client/v3/LeaseGrantServed.lean`, beside the plain ones, which keep their texts):
`etcdLeaseGrantHandlerOkMd` — from `quotaLeaseServerAt`, `leaseServerAt`, `lessorGrantOkGM true s E ρ S (grantLiveG E)
(fun m => m.2 = W64 0)` and the run's `S`, `grpcHandlerOwnOkMd` of the quota server's `LeaseGrant` at
`etcdLeaseGrantSpecOn s E ρ (mvcc.api.mvccLeases E.γ)`; `etcdLeaseRevokeHandlerOkMd` — from `quotaLeaseServerAt`,
`leaseServerAt`, `lessorRevokeOkM true s E ρ S`, `grpcHandlerOkMd` of the **quota server's** promoted `LeaseRevoke` at
`etcdLeaseRevokeSpecOn s E ρ`; over new metadata versions of the quota bridges `quotaLease_revokeHandlerOk` and
`quotaLease_grantHandlerOk_of` (`QuotaLeaseLemmas.lean:36, 60`, plain form only today; v3rpc, internal) (each
at `E.authMode = .on γa`; the context's token is the metadata's by `auth.ctxTokenOf_md`, `rfl`). They are what
`etcd_lease_auth_served_on`'s proof uses.

**7.5 The statements §7.3–§7.4 left in prose (review r5 S3, S4).**

```lean
-- v3rpc, QuotaLeaseLemmas.lean (internal), beside the plain ones
theorem v3rpc.quotaLease_grantHandlerOkMd_of
    (wp_Grant : v3rpc.quotaLeaseServer.LeaseGrant.spec (GF := GF) (hG := hG))
    {Req Rep : ProtoMsg GF} (Spec : GrpcSpecMd Req Rep) (q s : Loc) (ls : GoInterfaceOk) (S : IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        v3rpc.quotaLeaseServerAt q ls s ∗
        grpcHandlerOwnOkMd #(methods ls.ty go!"LeaseGrant" ls.v) iprop(S ∗ srvLgReader s) Spec ⊢
      grpcHandlerOwnOkMd (q @!! go.GoType.PointerType v3rpc.quotaLeaseServer.ty @!! go!"LeaseGrant")
        iprop(S ∗ v3rpc.quotaRd s) Spec
theorem v3rpc.quotaLease_revokeHandlerOkMd {Req Rep : ProtoMsg GF} (Spec : GrpcSpecMd Req Rep)
    (q s : Loc) (ls : GoInterfaceOk) (S : IProp GF) :
    v3rpc.quotaLeaseServerAt (GF := GF) q ls s ∗
        grpcHandlerOkMd #(methods ls.ty go!"LeaseRevoke" ls.v) S Spec ⊢
      grpcHandlerOkMd (q @!! go.GoType.PointerType v3rpc.quotaLeaseServer.ty @!! go!"LeaseRevoke") S Spec

-- client/v3, LeaseGrantServed.lean (the `Nx` tie as the plain lemmas' `hNx`; its source in
-- `etcd_lease_auth_served_on` is `srvKVCoreM_of_readM true` then `srvKVCoreM_Nx`, `WatchFire.lean:123`)
theorem etcdLeaseGrantHandlerOkMd (lp s : Loc) (A : v3rpc.KVAns GF) (cid mid : w64)
    (E : apply.AEnv GF) (ρ : ReqNames) (γa : auth.AuthNames) (hγa : E.authMode = .on γa)
    (hNx : E.Nx = srvApi.kvNx ρ.rd true) (S : IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        v3rpc.leaseServerAt lp s A cid mid ∗
        v3rpc.lessorGrantOkGM true s E ρ S (grantLiveG E) (fun m => m.2 = W64 0) ⊢
      grpcHandlerOwnOkMd (lp @!! go.GoType.PointerType
          go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer.ty @!! go!"LeaseGrant") S
        (etcdLeaseGrantSpecOn s E ρ (mvcc.api.mvccLeases E.γ))
theorem etcdLeaseRevokeHandlerOkMd (lp s : Loc) (A : v3rpc.KVAns GF) (cid mid : w64)
    (E : apply.AEnv GF) (ρ : ReqNames) (γa : auth.AuthNames) (hγa : E.authMode = .on γa)
    (hNx : E.Nx = srvApi.kvNx ρ.rd true) (S : IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        v3rpc.leaseServerAt lp s A cid mid ∗ v3rpc.lessorRevokeOkM true s E ρ S ⊢
      grpcHandlerOkMd (lp @!! go.GoType.PointerType
          go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer.ty @!! go!"LeaseRevoke") S
        (etcdLeaseRevokeSpecOn s E ρ)
```

(The handler lemmas at the `LeaseServer`'s methods, as the plain `etcd_leaseGrantHandlerOkGR`; the quota bridges carry
them to the quota server's in `etcd_lease_auth_served_on`. A form decided at the Prove step if the handler's `S` must be
`S ∗ srvLgReader s`, as the plain chain's.)

## 8. Mode-gate impact (the cleanup stage comes next)

Expected (`etc/mode-check.py`, against `etc/mode-baseline.txt`):
- `match-mode`, etcdserver: **−1** (`srvLessorNilM`'s match; its allow line goes).
- `lit-mode`, etcdserver: **−2** (`srvLessorNilM_false`/`_true`'s bridges); with C2 (not recommended) −2 more.
- `match-mode`, v3rpc: **0** (the `ResT` results as `⌜on = true⌝ → …`, no `match`).
- `lit-mode`, v3rpc: **+5 to +7**, `bridge` (the `ResT` and the four `…M` contracts' `_false` laws, the two `true` laws);
  the contracts and the handler specs at `on`, their off users at `E.authOn` with `hoff`.
- `lit-mode`, client/v3: **+4 to +6** (`etcd_lease_auth_served_on`'s `isServerReqM true`/`isServerReadM true`, the two
  `Md` handler lemmas' `lessor…M true`, as `etcd_kv_auth_served_on`'s); etcdstart: 0.
- `twin`: **0**; one `pair` recorded (C5′'s contracts; not counted by the gate, listed for the cleanup stage).

Net: about +4 to +7 over the gated packages, nearly all `bridge`/`flag` lines for the new mode-indexed results, against
−3 for the deleted coupling. C3 (a) also removes one `AuthC`-indexed sealed predicate (not counted).

## 9. Probe (`Scratch/S3cProbe.lean`, checked clean with `etc/lean-check.py -a`)

The riskiest point is the expiry arm: with the coupling gone, nothing in `run`'s context says auth is off when a slice
arrives, and `revokeExpiredLeases` (and `WithRoot`, auth off only) needs it. Probed: the guard C1 and its expiry law
(`srvGrantGuardC_expired`); auth off from the payload and the guard (`expired_authOff`); the new boot slot
(`bootCfgC`) with `_none`, `_mono` (no `hon`), `_run`, `_of_run` (and `newServerMode`'s `absurd` argument still fits),
`_noExpiry`; `NewServer`'s guard at a granting cluster in either auth mode (`newServer_guard`), `NewServerR`'s at auth
off (`newServerR_guard`); the guard at auth off equivalent to today's (`guard_off`). Not probed: C6 (§4a), the
monotone mode at auth on (§2), D6 (§7: definitions over existing vocabulary; the Prove step's risk is the handlers'
the quota wrapper's metadata spec and `srvAuthAt_of_viewsM`).

## 10. Statements this changes (for the Freeze)

**Hub (Q7, for the coordinator):** `lease.bootCfg`'s body (§2); `lease.srvInvAt`'s body (§3, C2′; with C2 also its
signature and `NewServer.specG`/`specR`'s occurrences).

**Trusted text:** two docstrings (§6): `NewLessor.lean:197-201`, `LessorBackend.lean:74-76`. No axiom, opaque or `sorry`
added or changed in statement; `etc/tcb-baseline.txt` unchanged.

**Frozen or exported text:**

| statement | where | change |
|---|---|---|
| `srvGrantGuard`, `srvGrantGuard_expired` | `InvApplier.lean:519, 537` | C1 (§1); `_false` deleted, `_expired_off` new |
| `lease.bootCfg` + laws | `LeaseApi.lean` | §2 (`_auth` deleted, `_noExpiry` new, `_mono`/`_of_run`'s `hon`) |
| `lease.srvInvAt`, `lease.srvInv`, `_intro` laws | `LeaseApi.lean` | first conjunct dropped (§3, C2′); `_lessorNil` laws deleted |
| `srvUberOn`, `srvUberOn_kv`, `srv_uberKVL`, `srv_uberKVL_on` | `ServerOnDefs`, `UberOn` | `srvLessorNil` dropped (§3) |
| exported `server_uber_kvl`, `server_uber_kvl_on` (`Results.lean:1751-1766`, both docstrings) | server `Results` | the same |
| `EtcdServer.apply.spec`, `applyEntries.spec`, `applyEntryNormal.spec`, `.specOn` | `Spec/…`, `ModeSpecs` | `srvLessorNilM` dropped (§3) |
| `acLessor` (C3 a) and `Start.spec`, `start.spec`, `applyAll.spec`, `AuthCompRows`, `run`'s loop row | `AuthComp` (frozen), `Spec/…` | deleted / conjunct removed |
| `srvClusterBootOn_alloc` and its exported restatement (C6) | `NewServerAllocOn`, server `Results` | `lm`/`gp`/`gps`; post `γk.lm = lm ∧ …` for `γk.lg = false` (§4a) |
| `grpcUpOn` (Lease service kept) | etcdstart `Defs` (API) | §7.3 |
| `srvRevokeOpen` (meaning: `revokeExpiredLeases.spec` weakened, inside `bootCfg`/`runCfg`) | `LeaseRun` | meaning only, discharged by the linked proof as before (§5) |
| `isServerRunC` (`run.spec`'s pre; its body) | `AuthCompRows.lean:364-370` | its `acLessor` row dropped (C3 a) |
| `run_job_body`'s pre (internal) | `EtcdServer__run.lean:167-194` | its `acLessor` conjunct dropped (C3 a) |
| `EtcdServer.revokeExpiredLeases.spec` | `Spec/…/EtcdServer__revokeExpiredLeases.lean` | `∧ E.authOn = false` (§5) |
| `lessorGrantOkG`, `lessorGrantOk`, `lessorRevokeOk`, `raftLessor` | v3rpc `InvLease` | unchanged; `…M` contracts beside them (C5′, §7.1) |
| `LeaseServer.LeaseGrant.spec`, `.LeaseRevoke.spec` (the `…M` contract; revoke narrowed); `quotaLeaseServer.LeaseGrant.spec` (one metadata spec, plain a corollary) | `Spec/…/v3rpc/` | §7.1 |
| `lessorGrantOkLive_of_server`, `lessorRevokeOk_of_server` (`lessorGrantOkL_of_server` unchanged, r5 S1) | v3rpc | `isServerReqM E.authOn`, the `…M` contract at `E.authOn`; the exported `…_server` corollaries and the seven client `Results` keep their texts (§7.1) |
| the client's lease handler lemmas | client `LeaseGrantServed` | metadata versions added (§7.1) |
| `acLessor` in `isServerBuilt_offC`'s conclusion, `applyAll.spec`'s post | `ModeSpecs.lean:612-616`, `__applyAll.lean:126` | dropped (C3 a) |

**New:** `srvGrantGuard_expired_off`, `lease.bootCfg_noExpiry`, `leaseGrantResT`/`leaseRevokeResT` (+ laws),
`lessorGrantOkGM`/`lessorGrantOkM`/`lessorRevokeOkM`/`raftLessorM` (+ `_false`), `srvAuthAt_of_viewsM`, `lessorGrantOkLiveM_server`, `lessorRevokeOkM_server` (exported, v3rpc), the metadata quota bridges, `etcdLeaseGrantSpecOn`, `etcdLeaseRevokeSpecOn`, `etcd_lease_auth_served_on`.
**Deleted:** `srvLessorNil`, `srvLessorNilM` (+ laws), `lookupNil_of_guard`, `apply.lookupNil`,
`srvGrantGuard_false`, `lease.bootCfg_auth`, `lease.srvInv{,At}_lessorNil`, `acLessor` (+ laws, C3 a).

**Meaning only:** `lessorOk`, `lease.lessorExpiredC … (srvGrantGuard …)`, `Results.lean:1192` (§1: a weaker payload);
`run.spec` (text unchanged); every caller of `NewServer.specM true` (an auth-on server may now be built at a granting
mode).

**Off callers of the restated handler specs** (client `Results.lean:3806, 3861`, `LeaseGrantServed.lean:142`) have no
auth-mode fact: they instantiate them at `on := false` with an explicit `ρ` (no `Inhabited ReqNames`), +3 `lit-mode` in
`client/v3` (§8's count rises accordingly). Proof sites of the deleted names, beyond those cited: `ModeSpecs.lean:208,
240, 620`, `EtcdServer__apply.lean:210, 1258`, `EtcdServer__applyAll.lean:102`, `EtcdServer__applyEntryNormal.lean:1489,
2403, 2428`; the destructurings of `isServerBuilt_offC`'s post at `etcdstart/Start.lean:55` and server
`Results.lean:2322` (review r5 S7). `leaseexpiry`'s `Main` premise
`srvRevokeOpen` changes meaning only (§5).

**Closed theorems: none change in text.** authkv (`etcd_auth_safe`) and auth3 (`etcd_auth3_safe`) run auth on at lease
mode `none` (`lease.bootCfg_none`, unchanged; C6's defaults), where the new row is vacuous; their proofs lose the
`srvInv_lessorNil`/`acLessor_on` lines (`auth/startServer.lean:153, 179`, `auth3/startMember.lean:169, 195`) and
`MainAlloc`/`Alloc3On` derive `lg = false` from the default mode (proof bodies). The lease examples (leasegrant,
leaseexpiry, k8s) run auth off: `newServerMode`'s `absurd` argument fits the new `hon`; their registrations go through
the in-place contracts at auth off (proof bodies). Land stop: the diff of `Proof/github_com` statements and
`gen-interface --check` on every `etc/api` list (etcdstart's `Defs` interface changes by `grpcUpOn`'s Lease conjunct, §7.3; nothing else under C2′).

## 11. Decisions asked

- **C1. The guard carries `on = true → leasesNoExpiry`** (§1), not the Scope's `⌜lg = true⌝` with `runCfg` gaining
  the auth mode. **Recommended** (probed; `runCfg` and its readers untouched).
- **The hub change (Q7):** `lease.bootCfg`'s row as the Scope's (§2), the monotone mode at auth on admitted (unprobed).
  **Recommended**; fallback (narrower row) if the Prove step finds an auth-on proof not generic in the mode.
- **C2′. `lease.srvInvAt` keeps its unused `on`** (§3). **Recommended** (no API change; the cleanup stage may drop it).
- **C3. `acLessor`**: (a) deleted with its conjunct in four specs and two rows, **recommended**; (b) kept, body `True`.
- **C4. The auth-on lease registrations as a separate `Md` set** (§7.2), not `etcdLeaseServedAt` at `E.authOn`.
  **Recommended.**
- **C5′. The lease contracts at the mode beside today's**, recorded as a `pair` for the cleanup stage (§7.1, rev 3).
  **Recommended** (seven exported client results keep their texts); alternative C5: in place (the spec skill's
  principle), the seven restated now.
- **C6. The auth-on allocation at a lease mode** (§4a), in S3c. **Recommended**; alternative: S4.
- **C7. The client's update as the contracts' `∀ Q` and permit**, no `KVDep.lease` deposit (§7.0). **Recommended.**
- **C8. `etcd_lease_auth_served_on` in S3c (client/v3, from `grpcServerAt`; `grpcUpOn` keeps the Lease service); etcdstart's `memberBootOn` `lg = false` to S4** (§7.3). **Recommended.**
- **The two trusted docstrings** (§6): the exact wordings. **Recommended.**
- (Review r4 S7–S9, r5 S9; not taken, recorded:) a v3rpc-level name for the client's permit (`leaseGrantAuOn`): not
  taken (the KV path's `etcdPutSpecOn` exposes its permit the same way); the old contracts defined as the `…M` ones at
  `false`: not taken in S3c (C5′'s pair, for the cleanup stage, which can make that the merge); `lease.srvInvAt`'s
  unused `on`: C2′, in the handoff's "Left".

## 12. Order of work (after the Freeze), estimate 5–8 agent-days (couplings 2–3, C6 0.5, D6 3–4)

1. §1–§2: the guard, the boot slot and their laws; `NewServer`/`NewServerR`'s guard proofs; `run`'s expiry arm;
   `revokeExpiredLeases.spec` and its proof; `newServerMode`.
2. §3: `srvInvAt`'s body, `srvUberOn` and the three `srv_uberKVL` lemmas; the apply specs; `acLessor` (C3); deletions;
   docstrings; §6's two docstrings. §4a (C6).
3. §7: `leaseGrantResT`/`leaseRevokeResT`, `srvAuthAt_of_viewsM`, the `…M` contracts, the server
   discharges, the handler specs, the quota wrapper's metadata instance, the client's metadata handler lemmas, v3rpc
   `Results`; `etcdLease*SpecOn`; `etcd_lease_auth_served_on`.
4. Land-stop checks: merge lean, full build (flock, 64G), `tcb-report --check` (870/4), `gen-interface --check` on every
   `etc/api` list, bounds and mode gates (raise for §8's `bridge`/`flag` lines, for the coordinator), closed statements
   unchanged, STATUS, handoff, status-history.
