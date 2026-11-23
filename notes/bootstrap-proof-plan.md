# Verifying `bootstrap`: discharging `bootPremise` (claim #34, design note, 2026-11-23)

The goal is to make `bootstrapContract` (`etcdserver/InvBoot.lean`) and `bootstrapRestartContract` (`InvRestart.lean`)
theorems, so that `bootPremise` (`examples/lib/etcdstart/Defs.lean`, inside each example's `premises`) leaves every top-level
etcd theorem, without growing any top-level premise (#18's ruling). Go is cited at the etcd pin `edc800c6f`
(`.lake/go-src/etcd` may sit at another commit: `8c28a4296`'s `bootstrap.go` differs).

## 0. The finding that shapes the plan: the contract can't be discharged at the current quantifiers

Every top-level statement has the form `∀ id ctxs boot, BootFacts id ctxs boot → (⊢ premises … id ctxs boot) → …`
(`etcd/all/TopLevelRobustness.lean`, `putget/Main.lean`). `BootFacts`/`BootCore` (`SrvRaftLog.lean:515`) never ties `id`,
`ps`, `ctxs` or `boot` to the configuration. `bootOk`, in turn, asserts `cv.ID' = id`, `γ.vs = ps` in `Members()` order
(`Hraft`, `Hmembers`), `peersCtx pv ctxs`, and `clusterMem (memBoot γ.boot)`. So `bootstrapContract` is **false at every
instance except Go's own values**: `id = computeMemberID(sorted peer URLs ++ token)` (the first 8 bytes of a SHA-1,
big-endian), `ps` = the members' ids sorted, `ctxs[k] = json.Marshal(cl.Member(ps[k]))`.

The theorems are sound (vacuous at the wrong instances), but no proof gives `⊢ bootPremise …` at an arbitrary `id`.
**Removing premises alone can't work: `id`/`ps`/`ctxs`/`boot` must be instantiated with definitions** of Go's values
(`etcdstart.memberID name urls token`; `ctxs`/`boot` from a JSON model of `Member`). `BootFacts` becomes a fact about
concrete terms: a pure premise still, or proved by kernel evaluation if SHA-1 and the JSON model are computable. This substitution is a change to
the statements, and it needs the owner's sign-off (§4). No other clause looked false or unsatisfiable at Go's own
instance. One could not be settled by reading (`Hss`'s source, flagged in §1).

## 1. The contract's clauses

T = a trusted claim about untranslated code today. P = provable over translated code once its callees have specs.

| clause(s) of `bootOk` | Go | status |
|---|---|---|
| precondition: `bootCfgOk`, `bootCfgFresh`, `dbOpensOk`, `zapLoggerOk`, feature gate, `envVerifyOff`, `bootCfgRO`, `memStorRegAuth ∅`, `wal.bootRes` | configuration / environment | the spec's own premises. `dbOpensOk` is already a top-level premise (`Hdbo`). The rest come from the caller |
| `Hb Hsto Hbk Hbw Hbc Hbv` (records) | `bootstrap`'s literal (`:121`), `bootstrapStorage` | P (trivial) |
| `Hprt` | `rafthttp.NewRoundTripper` (proved) | P |
| `Hwal` (`wal.bootOk`) | `bootstrapNewWAL` → `wal.Create` (proved), `MustMarshalMessage` (proved) | P (#15's area) |
| `Hss Hsdo Hsfree` | `bootstrapSnapshot`: `TouchDirAll` (proved), `RemoveMatchFile` ×3 (translated, unproved), `snap.New` (names-only) | P. The claims are carved out of `wal.bootRes`'s `dataAreaFresh`. **Check**: whether `memberAreasFresh` holds the snapshot names' claims (`snapFreeAll`, `snapDirOwn`); if not, `bootRes`'s body must grow (a slot change, not a top-level premise) |
| `Hraft` (`rnStartCfg`, heartbeat, `lg`, `ID = id`, `ps` nodup / non-zero / sorted, `γ.vs = ps`, `srvBootLogOk`) | `bootstrapRaftFromCluster`, `raftConfig`, `MemberIDs` | P, **only at Go's `id`/`ps` (§0)**. `NewRaftLoggerZap` is the top-level premise `rnLoggerZapOk` |
| `Hc Hlok Hreg Hγsz Hrauth Hmlock Hlog0 Hend Hsnone Hmeta Hfresh` | `bootstrappedWAL.MemoryStorage` (proved), `raft.NewMemoryStorage` (proved), plus a ghost registration | P |
| `Hpeers Hctx` (`peersCtx pv ctxs`) | `json.Marshal((*cl).Member(id))` | **T unless json is specified**: `MarshalMember` claims nothing about the bytes, and its argument shape is a value, not `*Member` |
| `Hcl` (`IsIDRemoved`), `Hrc` (`isRaftCluster`), `Hcid`, `Hid`, `Hclg`, `Hvcn`, `Hrms`, `Hrms0` | `NewClusterFromURLsMap`/`NewCluster`/`genID`/`SetID` (names-only), `bootstrapNewClusterNoWAL` | T today, P in stage 2 (`IsIDRemoved` is proved already) |
| `Hmembers` (`Members()` = `ps` in order, `memberDirIs dir`) | `Members` (proved over `rcLockInv`), the map `NewClusterFromURLsMap` builds | T: `rcLockInv` says nothing of the members' contents. P in stage 2 once `memAt` is built from the URLs map |
| `Hmem` (`clusterMem (memBoot γ.boot)`) | in-memory members vs. the decodings of the contexts | **T, not provable without a JSON trust spec**: `ccMemberOf` is `opaque` (`SrvRaftLog.lean:460`). The proof needs `ccMemberOf (Marshal m) = m` for valid UTF-8 (§5) |
| `Hclok` (`lease.clusterOk`: `Version` returns nil or `↦□`), `Hcvm` (`clusterVersionMono`), `Hisc` (`clusterApplyOk` → `apply.isCluster`'s `Version`/`ID`/`SetVersion`/`UpdateAttributes`/`SetDowngradeInfo` rows) | `RaftCluster.Version` (8 lines), `SetVersion` (37), `UpdateAttributes` (~40), `SetDowngradeInfo` (~15), all names-only | T, P in stage 1 |
| `HclBe` (`clusterBeOn`), `HDr`'s three membership buckets | `Finalize` → `SetBackend` (proved), `MustCreateBackendBuckets` | P |
| `Hci HisCI Hcons Hbh Hthr Happ Hown Hmeta HmetaSnap Hbe HhkAt Hnew Hm0 HD Hlate HmEmpty Hpath Hbfile` | `bootstrapBackend`: `OpenBackend` (**axiom**), `NewConsistentIndex`, `NewBackendHooks`, `ci.SetBackend`, `UnsafeCreateMetaBucket` (proved), plus a ghost allocation (`consInv_alloc`) | P over the `OpenBackend` axiom (it stays). `BootBackend.lean` / `BootStore.lean` already hold most of the glue |

The restart contract's `bootOkR` has the same rows, except: `Hwal` is `wal.restartOk` (over `openWALFromSnapshot`,
`wal.Open`/`ReadAll`, proved, #15); `Hrest` (`memStorRestarted`) is proved through `MemoryStorage`; `Hmem` holds at
`restModel … L`, from `Recover` (axiom); `Hm0` holds at `i`, from `recoverSnapshot`/`RecoverSnapshotBackend`; `Hraft`
uses `rnRestartCfg` with the WAL metadata's `nodeID`. Its premise `walReadFacts σ` is trusted inside the contract and
waits on #15's crash model (C6): **not discharged by this claim**. `clusterVerLogOk L` comes from the KV invariant.

## 2. The call tree (P proved, A axiom, N names-only, T translated but unproved; Go lines)

- `bootstrap` (79 N): `TouchDirAll` ×2, `NewRoundTripper`, `wal.Exist` P; `config` path methods N (over `datadir.*` P).
  `bootstrapSnapshot` (44 N): `RemoveMatchFile` T (over `ReadDir` P), `snap.New` (11 N).
- `bootstrapBackend` (51 N): `fileutil.Exist`, `NewConsistentIndex`, `NewBackendHooks`, `ci.SetBackend`, `ConsistentIndex` P;
  `OpenBackend` **A**; `CreateMetaBucket` N (over `UnsafeCreateMetaBucket` P). Restart: `recoverSnapshot` (58 N:
  `ValidSnapshotEntries` P, `newestSnapshotEntry` T, `RecoverSnapshotBackend` 12 N over `OpenSnapshotBackend` A), `schema.Validate` N.
- `bootstrapCluster` (16 N). `bootCfgFresh` excludes `bootstrapExistingClusterNoWAL` (so `GetClusterFromRemotePeers` and
  `ValidateClusterAndAssignIDs` need no spec) and the `v3discovery` branch.
  - `bootstrapNewClusterNoWAL` (36 N): `VerifyBootstrap` (18 N: `hasLocalMember` 8, `advertiseMatchesCluster` 51 over
    `netutil.URLStringsEqual`, **untranslated package**, `CheckDuplicateURL` 14, `URLsMap.String`);
    `NewClusterFromURLsMap` (16 N: `NewCluster` 15, `NewMember` 7, `computeMemberID` 15 and `genID` 10 over
    **`crypto/sha1.Sum`, untranslated**, `newMember` 12); `MemberByName` 15 N; `isMemberBootstrapped` (23 N:
    `getRemotePeerURLs` 16, `getClusterFromRemotePeers` 62 over the **`net/http` client, untranslated**, `json.Unmarshal`
    into `[]*Member`, `IDFromString` A, `NewClusterFromMembers` 9).
  - restart: `bootstrapClusterWithWAL` (26 N): `IsDirWriteable` P, `NewCluster`, `ValidateMaxLearnerConfig` 19 N, `SetID` 6 N.
- `bootstrapStorage` (11 N) → `bootstrapNewWAL` (18 N: `MustMarshalMessage`, `wal.Create` P). Restart:
  `bootstrapWALFromSnapshot` (51 N) → `openWALFromSnapshot` (41 N; #15's L5).
- `Finalize` (16 N): `SetID` (+ `buildMembershipMetric` 15 N), `NewMembershipBackend` P, `SetBackend` P,
  `ValidateMaxLearnerConfig`. Restart: `buildConfStateFromV3store` N (over `MustReadMembersFromBackend` A,
  `confStateFromMembers` T), `Recover` (44, **A**; `UnsafeLoad` 6 N: `ClusterVersionFromBackend` 20,
  `MustReadMembersFromBackend` A, `DowngradeInfoFromBackend` 31; `MustDetectDowngrade` 15) and `databaseFileMissing`
  (4 N: `Version`, `semver.New` P, **`semver.Version.LessThan` A**).
- `bootstrapRaft` (13 N) → `bootstrapRaftFromCluster` (25 N: `MemberIDs` 11 N, `Member` P, `json.Marshal(*Member)`, no
  spec) or `bootstrapRaftFromWAL` (9 N); both use `raftConfig` (13 N: `NewRaftLoggerZap` via the premise `rnLoggerZapOk`,
  `zap.Logger.Named`) and `MemoryStorage` P.
- The cluster's `Version` (8)/`SetVersion` (37): `semver.MustParse` P (over `NewVersion` A), **`semver.Version.String` A**,
  `version.Cluster`, `MustSaveClusterVersionToBackend` 11.

Reached Go: ~900 lines new-cluster, ~350 more restart (beyond `OpenBackend`/`wal`/`raft`, done or axioms).

## 3. Stages (each lands alone; Lean sizes are rough)

**Stage 1: the cluster's version (~200 Go, ~2000 Lean).** `rcLockInv` gains `c.version`: nil, or a read-only
`*semver.Version` (`semverIs`), with a `monoNatLb γcv 1` witness once non-nil. Translate and prove `Version`,
`SetVersion`, `UnsafeLoad`, and `Recover` over a widened `clusterImageOk` ("the version is present once observed");
the schema/version callees above get bodies (`UpdateAttributes`/`SetDowngradeInfo` optional). `bootOk`/`bootOkR`'s
`Hcvm`, `Hclok` and `Hisc`'s Version/SetVersion rows become lemmas. `isRaftCluster` instead carries the state claim
`c.version = nil` at boot, which stage 2 proves. That restates a premise clause, so it needs owner sign-off; it is
arguably no stronger, since the new claim plus the proofs give the old clauses.
- **Retires** `membership.RaftCluster.Recover.wp_proof` and `semver.Version.LessThan.wp_proof` (#18's proof comes back
  once `Version()` gives `v ↦□ x`).
- **`semver.Version.String.wp_proof`** retires only with a Perennial model of `fmt.Fprintf` into a `bytes.Buffer`
  (`semver/v3.toml`). That is a TrustedCode change: it moves the trust rather than removing it. Until then `Version`
  is proved over the `String` axiom.

**Stage 2: cluster construction (~400 Go, ~3000 Lean).** `NewCluster`, `NewClusterFromURLsMap`,
`NewMember`/`computeMemberID`/`newMember`, `genID`, `SetID`, `buildMembershipMetric`, `MemberByName`, `MemberIDs`,
`ValidateMaxLearnerConfig`, `bootstrapCluster`, `bootstrapNewClusterNoWAL` with `VerifyBootstrap`, and `Finalize`.
Yields `isRaftCluster`, the members map from the URLs map at `id = memberID …`, and `Hcid Hclg Hvcn Hrms0 Hmembers`.
No axiom exists here to retire. Needs `sha1.Sum` (§5.1).

**Stage 3: `bootstrap`'s body (~150 Go, ~1500 Lean).** New specs `Spec/…/etcdserver/bootstrap{,Snapshot,Backend,
Storage,NewWAL,Raft}.lean`. `bootstrap.wp_proof` takes the unproved callees' specs as hypotheses (`?` in `Link.lean`),
and `bootstrapContract_holds` is derived from it. Not linked to the top level, so trust is unchanged.

**Stage 4: the callees (~250 Go, ~2000 Lean).** `bootstrapSnapshot` (`RemoveMatchFile`, `snap.New`), `bootstrapBackend`
(over the `OpenBackend` axiom), `bootstrapNewWAL` (with #15), `bootstrapRaftFromCluster`, `raftConfig`,
`CreateMetaBucket`, `isMemberBootstrapped` (§5.3). After this, `bootstrapContract` is a closed theorem.

**Stage 5: restart (~350 Go, ~2500 Lean).** `bootstrapClusterWithWAL`, `recoverSnapshot`/`RecoverSnapshotBackend`,
`bootstrapWALFromSnapshot`/`openWALFromSnapshot` (#15), `bootstrapRaftFromWAL`, `buildConfStateFromV3store`,
`databaseFileMissing`, and the `haveWAL` branches, over stage 1's `Recover`/`LessThan`. Proves
`bootstrapRestartContract`, with `walReadFacts σ` a hypothesis until #15's C6.

**Final (~40 example files, mostly deletions).** Instantiate §0's quantifiers. Drop `bootPremise` from
`etcdstart.premises` (`OneMember`, `MembersDefs`, `MembersAuthDefs`, `cluster3/Defs`) and the contract premises from
`NewServer.spec`/`NewServerR.spec`; `bootPremise_of` users switch to `bootstrapContract_holds`. Lands after #28
`net-swap` (kaashoek's request on #34).

## 4. The interfaces

Consumers that switch to the proved specs: `NewServer`, `NewServerR`, `BuiltRestart` (all of `bootOk`/`bootOkR`,
unchanged: the contract becomes a lemma); `InvStart`, `EtcdServer__ClusterVersion` (`Hcvm`); `lease/InvLessor`'s
`clusterOk` (`Hclok`); `SnapRO`, `SnapApply{Opts,OptsLemmas,Post}`, `applySnapshot` (`clusterApplyOk`, `Recover`);
`apply/Contracts`'s `isCluster` via `ClusterVersionSet` and `version.LessThan` (#18); `NodeStart`/`InvNodeStart`
(`Hraft`, `Hctx`); `BootBackend`/`BootStore` (`Hnew`).

Top-level statements change in two ways: (a) the `bootPremise` conjunct is removed; (b) `∀ id ps ctxs boot` become
defined terms, with `BootFacts` a pure premise about them (or proved; Go tests already check it, `TestMemberIDs`).
(b) is not a pure premise removal, so it needs the owner's decision. No premise is added.

## 5. Risks, and callees that could need a new axiom (flagged; the goal is none)

1. **`crypto/sha1.Sum`**, used by `computeMemberID` and `genID`, is untranslated. Either goose translates it under
   `purego` (the generic block function; `boring`/`fips140only` to handle), or it is **+1 axiom** returning a defined
   FIPS-180 model. An opaque digest would suffice for `bootstrap`, but leaves `BootFacts` an unprovable pure premise.
2. **`json.Marshal(*Member)` with its bytes**, and `ccMemberOf (bytes) = member` for valid UTF-8, are needed by `Hctx`
   and `Hmem`. JSON is reflection, so this is **+1 axiom** (a new spec shape or a strengthened `MarshalMember`),
   unavoidable while `ccMemberOf` is opaque. A definitional `ctxs` also needs a trusted Lean `memberJSON`.
3. **`isMemberBootstrapped`** with two or more members makes HTTP GETs to the peers' `/members` (`http.Client.Get`,
   `io.ReadAll`, `Body.Close`, `json.Unmarshal` into `[]*Member`). None of these is translated or specified:
   **+3-4 axioms**, although "returns or errors" suffices. One-member examples never reach it.
4. **`netutil.URLStringsEqual`** does DNS for hosts that aren't IP literals. With IP literals it is string work and
   likely translatable; otherwise **+1 axiom**.
5. Other Iris premises in the way of "none": `bootMarshal`, `commonPremises` (`rnLoggerZapOk`, needed by `raftConfig`;
   `rnTimeoutDetectorOk`; `rnNewStorageOk`, #15). `walReadFacts σ` waits on #15. Regenerated `Code/…` collides with #18.

## 6. Collisions and the files per stage

- **#18 (proving session 2: `membership`, `etcdserver`, `v3rpc`).** Stage 1 is the work #18 scoped
  (`prove-ps2-version`, local `prove-ps2-semstr` at `3456c06e18`). Agree on who does stage 1 before starting; it shares
  `apply/Contracts.lean`, `semver`, and `ClusterVersionSet`.
- **#15 (kaashoek: `wal`, `bootstrapWAL`, L5).** Stages 4 (`bootstrapNewWAL`) and 5 (`openWALFromSnapshot`,
  `bootstrapWALFromSnapshot`, `walReadFacts`). Take their specs from #15, or leave those functions to it.
- **#28 net-swap** (top-level statements, `etcdstart`'s api list): the final stage goes after it.

| stage | files |
|---|---|
| 1 | `Code/…/membership.toml`, `schema.toml`, `version.toml`, (`semver/v3.toml`); `Proof/…/membership/{Defs,RaftCluster__Version,SetVersion,Recover,UnsafeLoad}.lean`, `Spec/…/membership/*`; `schema/{ClusterVersionFromBackend,DowngradeInfoFromBackend,MustSaveClusterVersionToBackend}`; `version/MustDetectDowngrade`; `etcdserver/{InvBoot,InvRestart,InvStart,SnapRO,SnapApply*,EtcdServer__ClusterVersion}.lean`; `apply/Contracts.lean`; `lease/InvLessor.lean`; `semver/Version__LessThan.lean`; `etc/tcb-baseline.txt` |
| 2 | `membership.toml`, `config.toml` (+ new `pkg/netutil`, `crypto/sha1` configs); `Proof/…/membership/{NewCluster*,NewMember,genID,SetID,MemberByName,MemberIDs,ValidateMaxLearnerConfig}.lean`; `Proof/…/config/VerifyBootstrap.lean`; `etcdserver/{bootstrapCluster,bootstrapNewClusterNoWAL,bootstrappedCluster__Finalize}.lean` |
| 3 | `etcdserver.toml`; `Spec/…/etcdserver/bootstrap*.lean`; `Proof/…/etcdserver/{bootstrap,InvBoot}.lean`, `Link.lean` |
| 4 | `Proof/…/etcdserver/{bootstrapSnapshot,bootstrapBackend,bootstrapNewWAL,bootstrapRaftFromCluster,raftConfig,isMemberBootstrapped}.lean`; `snap.toml`; `schema/CreateMetaBucket`; json/sha1/http trust specs if approved |
| 5 | `Proof/…/etcdserver/{bootstrapClusterWithWAL,recoverSnapshot,bootstrapWALFromSnapshot,openWALFromSnapshot,databaseFileMissing,buildConfStateFromV3store,InvRestart,NewServerR}.lean`; `storage/RecoverSnapshotBackend` |
| final | `Spec/…/etcdserver/{NewServer,NewServerR}.lean`; `examples/lib/etcdstart/{Defs,OneMember,MembersDefs,MembersAuthDefs,Restart,newServerMode,AllocNOn}.lean`, `lib/cluster3/Defs.lean`; every `examples/{etcd,k8s}/*/{Defs,Main,Run,startMember,startCluster}.lean` that names `bootPremise` (about 40); `Spec/…/examples/**/TopLevelRobustness.lean` |

## 7. The proof plan (refined 2026-11-23, after the owner's decisions and the stage-1 handover)

Decided on #34: the top-level statements stop quantifying over `id`/`ps`/`ctxs` (they become the
definitions of §7.2); stage 1's interim `bootOk` change is approved; new trust only where Perennial's
semantics can't support the code, each case brought to the owner first. **Stage 1 is proving
session 2's** (zeldovich, branch `prove-ps2-bootstage1/2026-11-23`). This claim keeps out of
`membership/` and the cluster parts of `InvBoot`/`InvRestart` until it lands. The order here becomes
**3 → 2 → 4 → 5 → final**: stage 3 needs nothing from stage 1 (its callees are hypotheses), and stage 2
builds `isRaftCluster`, whose lock invariant stage 1 changes.

### 7.1 The stage-1 interface (what stages 2-5 assume; proving session 2 takes it verbatim)

- **I1 (the version slot).** `rcLockInv` gains the field `c.version`, read through a new
  `membership.rcVersionAddr c` (`structFieldRef membership.RaftCluster go!"version" c`). Under the
  lock it is nil, or read-only (`vp ↦□ ver`) with the witness `monoNatLbOwn γcv 1`, where `γcv` is
  the slot's `monoNatAuthOwn` name. If `γcv` must be visible (`Recover`'s link to the snapshot
  image), the predicate becomes `membership.isRaftClusterV c γcv`, and `bootOk`/`bootOkR` say
  `∃ γcv, isRaftClusterV bc.cl' γcv` in place of `Hrc` and `Hcvm`'s existential. Otherwise
  `isRaftCluster c` keeps its arity.
- **I2 (the starting-state claim, the approved interim premise).** At boot the slot is nil.
  `bootOk`'s clause is the widened `Hrc` alone, no separate conjunct. Its construction lemma is
  `membership.rcLockInv_boot : <rcLockInv's other fields as today> ∗ rcVersionAddr c ↦ null ⊢ |==>
  ∃ γcv, <the widened rcLockInv at γcv>`. Stage 2 proves `isRaftCluster` through it: `NewCluster`'s
  literal leaves `version` nil.
- **I3 (what leaves `bootOk`).** `Hcvm` becomes a lemma of `Hrc`, and so does `Hclok`
  (`lease.clusterOk` of the cluster's interface). In `Hisc`, the `Version`/`ID`/`SetVersion` rows (and
  `UpdateAttributes`/`SetDowngradeInfo` if proved) become lemmas from `Hrc` with `HclBe` and
  `Hvcn`'s read-only form. `clusterApplyOk`'s statement does not change, so its consumers
  (`SnapApply*`, `apply/Contracts`) do not move. No other clause of `bootOk`/`bootOkR` changes.
- **I4.** `rcLockInv`'s other fields (members `memAt` half, `rcLocalIn`, `removed` empty) stay as they
  are. Stage 2 relies on them.

### 7.2 Go's values (a defs module `Proof/…/etcdserver/BootValues.lean`, written in stage 3)

These are pure definitions, not trust. They are what the final stage substitutes for the quantified
`id ps ctxs boot dir` (decision 1). Each is proved to be what Go computes in the stage named.

- `bootGo.sha1 : List w8 → List w8`, FIPS 180-4 written out in Lean (computable, so `decide`/kernel
  evaluation settles the examples' `BootFacts`). Stage 2 proves `crypto/sha1.Sum` (goose over the
  `purego` generic block) equal to it.
- `bootGo.memberID urls token : w64`: big-endian first 8 bytes of
  `sha1(join(sort(urls), "") ++ token)` (`computeMemberID`, `now = nil`). `bootGo.ps U cfg` is the
  sorted `memberID` of each `initMap` entry. `bootGo.id cfg U` is the entry named `cfg.Name'`.
  `bootGo.cid` is `genID`'s value over `ps`. `bootGo.dir U` maps an id to its member's URL strings.
- `bootGo.memberJSON : MemberM → List w8` is the bytes `json.Marshal(*Member)` writes. Its field
  order, escaping and `omitempty` follow `encoding/json` on `membership.Member`'s tags, cross-checked
  against `models/json/jsongen.py`'s codec and a Go test. `bootGo.ctxs` maps `memberJSON` over the
  members in `ps` order. `bootGo.bootLog` is `BootLog ps ctxs`'s log.

Checked 2026-11-23 against Go 1.27.3: `sha1([])`, `memberID(["http://127.0.0.1:2380"], "tok")`,
`genID` of two ids and `memberJSON` of a member named `a<b"` + U+2028 agree byte for byte with
`crypto/sha1`/`encoding/json` (a throwaway Go program and `#eval`; stage 4 turns it into a Go test).
A peer URL's string is `urlStr u = "http://" ++ u.Host'`, which is `URL.String()` only for a plain URL
(`http.urlRootPlain`, the only case this repository specifies), so `bootstrap.spec` takes the pure
precondition `bootGo.bootURLsPlain U`. `bootstrapContract_holds` then holds for `U` meeting it, and the
final stage checks that each example's `Uok` implies it (as its `peerURLsDir` already does for
`cfg.PeerURLs`). This narrows no top-level statement: `bootPremise` is already `∀ U, Uok U → …`.

### 7.3 Stage 3: `bootstrap`'s body (first start), over its callees' specs

- Translate `bootstrap` with its body (`etcdserver.toml`), plus `config`'s path methods `MemberDir`,
  `WALDir`, `SnapDir` (`filepath.Join` over the proved `filepathlite`). The callees stay names-only.
- **`bootstrap.spec`** has `bootstrapContract`'s precondition. Its post is `err ≠ nil ∨ bootOk cfg γ
  (bootGo.id cfg U) (bootGo.ctxs cfg U) N (bootGo.dir U) b`, for every `γ` with `γ.vs = bootGo.ps`,
  `γ.boot = bootGo.bootLog`, `γ.rule = srvRule 0 γ.boot` (`bootPremise`'s conditions). It is not
  stated at an arbitrary `id`, which would be false (§0). **`bootstrapContract_holds`** (linking)
  restates it as `⊢ bootstrapContract cfg U γ (bootGo.id …) …`. The restart branch (`haveWAL`) is
  excluded by `wal.Exist`'s `false` on `wal.bootRes`. Stage 5 adds `bootstrap.specR`.
- **New callee specs** (`?` in the server's `Link`, so hypotheses of the linked result, and no trust
  change), one triple each, shaped so their posts join into `bootOk` row for row:
  - `bootstrapSnapshot.spec`: the snapshot directory's part of the data area. Post: `ss` with
    `isSnapshotter … (snapDirOf DataDir)`, `snapDirOwn`, `snapFreeAll` (`Hss Hsdo Hsfree`).
  - `bootstrapBackend.spec` (`haveWAL = false`): the backend file's part of the data area,
    `bootCfgOk`, `dbOpensOk`, the gate, `envVerifyOff`, and the logger. Post: an error, or `bk` with
    `Hci … Hbfile` (`γA`, `d`, `D` existential) and `bk.snapshot = nil`. It does not include `HDr`'s
    membership buckets.
  - `bootstrapCluster.spec` (`bwal = nil`, `bootCfgFresh`): `bootCfgRO`, the logger, `prt`. Post: an
    error, or `bc` with `bc.nodeID = bootGo.id`, `bc.remotes = nil`, and `clusterBuilt bc.cl' U cfg`.
    That is a **new def**, the cluster's fields owned before `SetID` and before the lock is shared:
    `members` as `memAt` at `1` over the `initMap` members, `removed` empty, `version` nil (I2),
    `cid ↦ bootGo.cid`, `lg` a zap logger, `localID`, `be`, `versionChanged` owned. It is written with
    `structFieldRef`, not with `rcLockInv`, so stage 1 cannot break it.
  - `bootstrapStorage.spec` (`wal = nil`): `walAreaFresh`, a share of `bc.nodeID`/`cid`. Post: `sto`
    with `Hwal` (`wal.bootOk cfg id cid`).
  - `bootstrappedCluster.Finalize.spec` (no WAL): `clusterBuilt`, `bk`'s backend. Post: `Hrc` (I1-I2),
    `Hcl Hcid Hclg Hvcn Hrms Hrmsi Hrms0 Hmembers Hmem HclBe`, and `HDr`'s membership buckets, or an
    error from `ValidateMaxLearnerConfig`. On a new cluster without learners it returns nil.
  - `bootstrapRaft.spec` (`bootstrapRaftFromCluster`): the cluster from `Finalize`, `bw`, the registry
    authority. Post: `Hraft Hc Hlok Hreg Hγsz Hrauth Hmlock Hlog0 Hend Hsnone Hmeta Hfresh Hpeers Hctx`
    at `bootGo.ctxs`.
- **The data area's split law** (`WalApi.lean`/`WalAreaFresh.lean`, a new law in the WAL's slot API; #15's
  files, coordinated through the owner): `wal.bootRes cfg ⊢` the claims the two `TouchDirAll`s take
  (`DataDir`, `member/`), then the snapshot part, the backend-file part, and the WAL area.
- **`bootstrap.wp_proof`**: straight-line over these. It covers the `MaxRequestBytes` warning
  (`humanize.Bytes`, translated), the two `TouchDirAll`s (proved), `NewRoundTripper` (proved),
  `wal.Exist` (proved), and `backend.Close` on the error paths (`bootstrappedBackend.Close`, proved).
  Trust change: none. The hypotheses are new specs of names-only functions, below the contract's
  premise.

### 7.4 Stages 2, 4, 5 and the final stage (unchanged scope; shapes)

- **Stage 2** (after stage 1 lands) proves `bootstrapCluster`/`bootstrapNewClusterNoWAL` (with
  `VerifyBootstrap`, `NewClusterFromURLsMap`, `NewCluster`, `NewMember`, `computeMemberID`, `genID`,
  `MemberByName`) and `Finalize` (`SetID`, `buildMembershipMetric`, `SetBackend` proved,
  `ValidateMaxLearnerConfig`) against §7.3's specs. The invariant of `NewClusterFromURLsMap`'s loop
  over `initMap` (in Go's unspecified order) is `members` = the map of the names seen so far, at
  `memberID`, all distinct and nonzero. `isMemberBootstrapped` belongs to stage 4.
- **Stage 4** proves the other callees: `bootstrapSnapshot`, `bootstrapBackend`, `bootstrapNewWAL`
  (#15), `bootstrapRaftFromCluster`/`raftConfig`, and `isMemberBootstrapped`. With them,
  `bootstrapContract_holds` is closed.
- **Stage 5** proves `bootstrap.specR`, the restart branches, and `bootstrapRestartContract_holds`.
  `walReadFacts σ` stays a hypothesis (#15's C6).
- **Final** (after #28 `net-swap`): `bootPremise` goes, and the top-level `∀ id ps ctxs` become §7.2's
  terms. `BootFacts` becomes a pure fact of concrete terms, proved by evaluation where it can be.

### 7.5 Stops (each reported to the owner before any trusted statement changes)

- **S1, `json.Marshal(*Member)`** (stages 4 and final, `Hctx`). `encoding/json` is reflection
  (`reflect`, `unsafe`). Goose has no `reflect`, so this is a case where the semantics genuinely
  can't support the code. The options to bring: (a) a trusted triple `json.Marshal(m) = memberJSON
  mm`; (b) replace the call by a generated codec (`models/json`). (b) changes the Go code, so it is
  not available. Expected: (a), brought first.
  Facts (2026-11-23): the call is `bootstrap.go:553`, `json.Marshal((*cl).Member(id))`. `Member`,
  `RaftAttributes`, `Attributes` and `types.ID` define no `MarshalJSON`/`MarshalText`
  (`git grep` at `edc800c6f`), so `encoding/json` goes through `reflect` (`encode.go`'s
  `typeEncoder`, `reflect.Value.Field`). Perennial translates `reflect` names-only
  (`Perennial/Code/reflect.toml`), because its values read runtime type descriptors through
  `unsafe`, which the semantics can't represent. No etcd code writes a member's JSON by hand. The
  proof can't avoid the bytes: `Hctx`'s `peersCtx pv ctxs` names them, and `BootCore`'s
  `ccBootOk`/`bootURLsOk`/`bootDataOk` are facts about them. The existing axiom
  `encoding.json.MarshalMember.spec` already covers the call, returning some bytes `b`. The
  proposal: **strengthen its post to `b = bootGo.memberJSON ⟨m.ID', ps, m.IsLearner', m.Name', cs⟩`
  for `ps`, `cs` and the name valid UTF-8.** That changes an existing axiom, not +1.
- **S2, `ccMemberOf`** (`Hmem`, `SrvRaftLog.lean:460`) is `opaque`. The proof needs
  `ccMemberOf (memberJSON m) = m`, which means defining it (`json.Unmarshal`'s model). That is a
  change to a trusted definition, brought first.
- **S3, `crypto/sha1`, `netutil.URLStringsEqual` (IP literals), the `net/http` client in
  `isMemberBootstrapped`.** Translation is tried first. If goose or the semantics fails (e.g.
  `crypto/internal/fips140` build tags, `net.Resolver`), I stop with the reason.
  Probe results (2026-11-23, goose `c95e922` on Go 1.27.3's library and etcd `edc800c6f`, in a
  scratch directory):
  - **`crypto/sha1`** translates completely with `-tags purego` (`Sum`, `digest.Write`,
    `checkSum`, `blockGeneric`, and `init`'s `crypto.RegisterHash`). Without `purego`, goose stops on
    the assembly `blockAVX2`/`blockSHANI` (`sha1block_amd64.go:15,18`). What remains are leaves with
    no Go body: `crypto/internal/boring/sig.StandardCrypto` (an assembly marker that does nothing),
    `crypto/fips140.isBypassed` (`go:linkname`), and `internal/godebug`'s linkname'd functions
    under `fips140.enabled`. `Sum` panics if `fips140only.Enforced()`, so a model of it returning
    false carries an environment premise (`GODEBUG` lacks `fips140=only`). `purego` also trusts
    that the assembly computes `blockGeneric`'s function. The alternative is one trusted `sha1.Sum`,
    like the existing `sha256.Sum256`. **Owner's choice, before stage 2.**
  - `encoding/binary.BigEndian`, `sort.Strings`: translated in Perennial already.
    `strings.Join`: trusted there already.
  - **`netutil.URLStringsEqual`** (12 functions) translates. With IP-literal hosts and numeric ports
    it reaches `url.Parse`, `URL.String`, `net.SplitHostPort`/`ParseIP`/`IP.*`, and no resolver.
    Perennial-side gaps: the `internal/bytealg` assembly
    (`IndexByteString`/`IndexString`/`CountString`), `netip`'s package `init` calling `unique.Make`
    (the runtime's weak interning table), `strings.Builder.String` (`unsafe.String`),
    `strings.IndexRune` (a label goose rejects, `strings.go:157`), `url.badSetPath` (linkname),
    `godebug.Setting.Value`.
  - **`isMemberBootstrapped`.** With one member it makes no HTTP request: `getRemotePeerURLs`
    skips the local member, so it allocates a client and returns false. That part translates now.
    With several members it calls `Client.Get` per peer, which translates (after un-skipping
    `DefaultTransport`, `NoBody`, `ErrSchemeMismatch`, `ErrUseLastResponse`), with `RoundTrip`
    and the body reads as the network boundary. `json.Unmarshal` into `[]*Member` runs on any
    response (the status is not checked), and that is reflection again.
- **S4, build capacity.** A full build is about 49 GB; the disk had 22 GB free on 2026-11-23, and
  `bootstrap`'s cone is most of the server. Each stage's check is a target-limited `lake build`
  under `/shared/tmp/build-slot.sh`.
