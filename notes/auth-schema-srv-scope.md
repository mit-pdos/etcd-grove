# Discharging `authSchemaSrv` (D22's part): Scope (2026-11-16)

Stage `auth-schema-srv` (branch `auth-schema-srv`, worktree `/shared/etcd-grove-authschema`, off lean
61053b1f3c), requested by the user via etcd-grove-02. Goal: prove `authSchemaSrv`
(`Proof/go_etcd_io/etcd/server/v3/etcdserver/AuthSrv.lean:99`), the named hypothesis `hD22` of
`etcd_auth_safe`, `etcd_auth3_safe`, `etcd_authN_safe`, from etcd's `storage/schema` auth code over the
backend's proved specs, and drop the hypothesis. This run: the Scope only, no Lean.

**Headline: `authSchemaSrv` is false (a refutation, HARD STOP).** Its read contract promises each read
transaction one recorded auth state; Go lets a read see a step's puts without its deletes (§2, R1; Go
test fails at the fork pin). The three closed theorems are vacuous until the text is restated. The
proved `auth.authStore.CheckPassword.spec` is false of Go for the same reason. Nothing below can start
before Q1 is decided.

## 1. What the premise says, clause by clause

`authSchemaSrv` (persistent): for any auth names `γa` and real backend `d` (`mvcc.KBReal`), given
`ablOn abl d.be lg` (schema's `*authBackend` over `d`), the auth buckets in the table and empty, the
backend's `isBackend` (any `W`, `Pk`), an open share `qo` and the realization's `authOpenQ`, the auth
reader slots (`authRdSlots`), the hook unset (`plHook d.γB func.nil`), the client's idle part of the
auth buckets (`rbOwnIn d.γB authBkts r`), the succession right, the lock's half of the history at
`bootState` (`authLockI`) and half the published index (`authPubQ ½ 0`), a fancy update gives, for
fresh backend names `γc` (and some `R P f Pre Q Post`):

| # | clause | Go code it is about | Go functions (translation state) |
|---|---|---|---|
| C1 | `authBackendOk (authBkIface abl) R (.on γa) γc` (`auth/InvAuth.lean:637`): `ReadTx()` returns a read tx whose `RLock` gives a held token `Hs st` of a recorded state (plain, with `authCur γc q`), of a state ≥ a published lower bound, or (with `authWTok γc ∗ authHistHalf hs`) of `hs`'s last; reads under `Hs st` are `st`'s (`authTxReads`/`authReaderOk`: `UnsafeReadAuthEnabled/Revision`, `UnsafeGetUser/Role`, `UnsafeGetAllUsers`); `RUnlock` gives `R` back | `auth.go` `ReadTx`, `authReadTx.*`; `auth_users.go`/`auth_roles.go` `authReadTx.UnsafeGet*`, `unsafeGet*`; backend `readTx.RLock/UnsafeRange/UnsafeForEach/RUnlock` | schema: all translated with bodies (`Code/.../schema.toml`); **proved** (theorems): `authBackend.ReadTx`, `authReadTx.{RLock,RUnlock,UnsafeReadAuthEnabled,UnsafeReadAuthRevision,UnsafeGetUser,UnsafeGetRole}`, `unsafeGetUser/Role`, `unsafeReadAuthEnabled/Revision`, `authBackend.GetUser/GetRole`, `NewAuthBackend`, all over the intermediate contracts `schema.authBE`/`authRTx`/`authReader` (`etcdserver/InvAuthBackend.lean`), which nothing derives from the backend yet; **no spec**: `authReadTx.UnsafeGetAllUsers`, `unsafeGetAllUsers`, `authBackend.GetAllUsers`; backend `baseReadTx.UnsafeForEach` translated, no spec |
| C2 | `authCur γc 1` | ghost (the backend's currency) | - |
| C3 | `authWBackendOkR (authBkIface abl) (.on γa) P f (authWTok γc) (wbTok d.γB)` (`InvAuth.lean:1559`): `BatchTx()` returns a tx meeting `authBatchTxLkR` (`:1404`: `Lock` from the hook contract and `T` gives `Lk st Post ∗ authLockI st`; reads; `UnsafePutUser` (sorted roles, name `1..maxKeySize`, UTF-8 roles), `UnsafeDeleteUser`, `UnsafePutRole`, `UnsafeDeleteRole`, `UnsafeSaveAuthEnabled`, `UnsafeSaveAuthRevision`; `Unlock` with `authLockI st` and two `Wb` gives `X ∗ T`; `UnsafeGetUser/Role` owned); `ForceCommit` (`T ∗ Wb`); `authBackendReads` (`GetUser`, `GetRole`, `GetAllUsers` via a read tx at the latest state with `T ∗ authOwn`; `GetAllRoles` a batch, two `Wb`) | `auth.go` `BatchTx`, `ForceCommit`, `authBatchTx.*`; `auth_users.go`, `auth_roles.go` | translated with bodies; **no spec** for any `authBatchTx.*`, `authBackend.{BatchTx,ForceCommit,GetAllUsers,GetAllRoles}`, `unsafeGetAll*`; backend: `batchTxBuffered.{LockInsideApply,Unlock,Commit,UnsafePut,UnsafeDelete,UnsafeRange}`, `backend.{BatchTx,ForceCommit}` proved; `batchTx.UnsafeForEach`/`unsafeForEach` translated, **no spec**; protobuf: `proto.UnmarshalUser`/`UnmarshalRole` axioms (exist, reached by no auth collection today), **no `proto.Marshal` spec for `authpb.User`/`Role`**; `binary.BigEndian.PutUint64` spec exists |
| C4 | `authWAtHook γa d γc`: C3 at every schema auth backend on `d.be`, at any frozen hook `f' ≠ nil` (`plHookRO`) | as C3, after `SetTxPostLockInsideApplyHook` | as C3 |
| C5 | `authBkLend γa γc d`: with `T` and the history's half, an abstract `RL` agreeing with the batch lock's `rbOwn d.γB r` that the auth buckets hold the latest state (`authBucketsAt`) | ghost (the snapshot window's observation) | - |
| C6 | `CreateAuthBuckets` triple `{T ∗ Wb} … {T}` | `auth.go` `CreateAuthBuckets`: `LockOutsideApply`, three `UnsafeCreateBucket`, deferred `Unlock` | translated; no spec; backend `LockOutsideApply`, `UnsafeCreateBucket`, `Unlock` proved |
| C7 | `authWTok γc ∗ authPubTok γa` | ghost | - |
| C8 | `authBkLife γa γc (bOpen d.γB authOpenQ)` (`auth/BkNames.lean:172`): retire, release, publish | ghost over the realization's invariant | - |
| C9 | `srvApi.csContractA P f Pre Q Post` and `Post -∗ bOpen qo ∗ plHook func.nil` | `NewAuthStore`'s `tx.Lock()` (`LockInsideApply` with the hook unset) | backend `LockInsideApply` proved |
| C10 | `authRdN` copies of the ticket `R` | ghost over `authRdSlots` (`backend.rdAuth`, `rdTok`s) | - |
| C11 | `authSchemaSnap γa R` (`etcdserver/AuthSnapKit.lean:68`): C1, C2, C3, C4, C5, C7 (write token), C8 again for every later backend a snapshot install opens, from `authBucketsAt st r` and `authLockI st` | the same code on the new backend | as above |

`authSchemaBoot` (`auth/Boot.lean:120`) is C1-C3 and C6 in the auth package's vocabulary, a premise of
the exported `auth.newAuthStore_boot` (E2e; `etcdserver/Results.lean:2035`), which no closed theorem
uses (the server goes through `authSchemaSrv` and `newAuthStore_on`). It is not the same work: it is
a non-persistent wand under a basic update (`|==>`), and the realization needs invariants (a fancy
update), so it cannot be discharged as stated (Q8).

**Trust base today.** The auth collections (`etc/tcb-collections/{authkv,auth3,authN}.txt`) reach no
`schema` auth axiom: every schema auth function is behind the hypothesis. `auth.NewAuthStore.wp_proof`
(the off-mode axiom) is not reached by them. So the discharge **removes no axiom**; it removes the
hypothesis (C1-C11, about 60 lines of trusted text plus `authSchemaSnap`, `authBkLend`, `authWAtHook`,
`authBkLife`) and **adds** reached axioms: `proto.UnmarshalUser`/`UnmarshalRole` (existing), the
Marshal specs (new, Q3), one bbolt key-value axiom for `ForEach` (Q7), and whatever Q2 leaves trusted.
(Not run: `etc/tcb-report.py --roots auth` needs an up-to-date build, which this worktree's moved build
is not; the collections' baselines say the same.)

## 2. Provable from the code over existing specs?

**R1 (refutation, Go-level): C1's plain and lower-bound `RLock` clauses are false.**
`batchTxBuffered.Unlock` (`server/storage/backend/batch_tx.go:328-357`) writes the session's puts back
under `readTx.Lock()`, releases it, then commits because a delete is pending (`commit` re-takes the
lock). A reader in between sees the read buffer (the step's puts) over bbolt's old snapshot (the
step's deletes not applied). `UserDelete(u)` = delete `authUsers[u]` + put `auth[authRevision]`: the
reader sees revision `r+1` with `u` present, no recorded state. Go test
`nonissues/etcd-auth-readtx-delete-window-mixed-state/zz_authschema_window_test.go` (the auth store's
real `UserAdd`/`UserDelete`; the reads of `CheckPassword`'s closure) fails at the fork pin 6e8f0c004,
go1.27.3, on the first delete, three runs of three. A program over the contract (writer: the store's
`UserDelete`; reader: `RLock`, `UnsafeGetUser`, `UnsafeReadAuthRevision`, panic if the user is present
at an odd revision) has a provable no-panic triple and panics in Go. The lower-bound clause fails the
same way (a reader with bound `i` during step `i+1`'s window). The latest clause (with `T`) is true:
no auth batch is open, the last `Unlock` returned after its commit. The Go behavior has no wrong result
in etcd (`Authenticate` re-reads the user at apply): nonissue
`nonissues/etcd-auth-readtx-delete-window-mixed-state.md`. Recorded:
`notes/auth-schema-srv-refuted.md`, "Second refutation".

What is true (the fix's basis): **per bucket** a read is one recorded state, the step's before or after.
No admin step deletes and puts in the same auth bucket (`UserDelete`: delete in `authUsers`, put in
`auth`; `RoleDelete`: delete in `authRoles`, puts in `authUsers` and `auth`; the rest put only), deletes
force a commit at `Unlock` (so a put-only bucket's buffer over the last commit is its new contents, a
delete-only bucket's its old). `SpecPlan`'s auth API already states readers per view ("at which recorded
state each view it read was", `SpecPlan/Spec/go_etcd_io/etcd/server/v3/auth/Api.lean:29`). Only one
reader reads two buckets: `CheckPassword` (user + revision). Its proved spec
(`Spec/.../auth/authStore__CheckPassword.lean`, `passwordChecked`: "the revision of a recorded state
that has the user") is false of Go and must weaken; its users (85 mentions of `CheckPassword.spec`/`hCP`
across `Proof/`, the server's `Authenticate` path and the auth chains) follow.

**The other gaps (no falsity found):**

- **G1, the read model over the tracked hook buckets.** On the server every auth bucket is a hook
  bucket (`KBReal.P`: `HB n = (n ≠ key)`), and the backend relates readers' views to the writer's
  contents only off the hook buckets (`agreeOff P.HB`, `vData`, `thinV`). `readTx.RLock` gives `∃ rv,
  rtHeld … rv` with nothing tying `rv`'s auth buckets to `rbOwnIn`: C1 is not derivable (nor is panic
  freedom of a read: `proto.Unmarshal` needs the bytes to be encodings). This is the backend-auth-split
  plan's "option (a)" (`notes/backend-auth-split-plan.md`, "Later stage", survey estimate 2.5-10k
  lines). With R1 it must also model the window: per tracked bucket, a readers' copy that the write-back
  moves for put buckets and the commit for delete buckets (or per-bucket "before or after the session").
- **G2, `UnsafeForEach`.** `GetAllUsers` (read tx; `UserList`) and `authBatchTx.UnsafeGetAllUsers` (batch;
  `RoleDelete`) need backend specs of `baseReadTx.UnsafeForEach`, `batchTx.UnsafeForEach`, `unsafeForEach`;
  these need bbolt's `Bucket.ForEach` over the backend's bbolt key-value contract (axioms
  `bbolt.*_kv`), which has `Seek_kv`/`Next_kv` but no `First_kv` (bbolt's `ForEach` is `c.First()` then
  `Next()`).
- **G3, protobuf `Marshal` of `authpb.User`/`Role`** (`UnsafePutUser`/`UnsafePutRole`): no spec. And
  follow-up **(a)**: `ownUser`'s `Options` (`userOptsIs`) and `ownRole`'s permissions (`ownPermS`) are
  `↦□` with their `sizeCache`, which protobuf-go's `Marshal` stores (atomically) in every nested
  message: a Marshal spec over today's predicates would claim a write that does not happen. Fixing (a)
  restates `userOptsIs`/`ownPermS`/`ownPermW` (trusted: `UnmarshalUser`/`UnmarshalRole` and the request
  decode axioms mention them).
- **G4, the per-batch put count** (the re-review's m2, `notes/decisions.md`, auth-schema-fix): the
  backend's `UnsafePut`/`UnsafeDelete`/`UnsafeCreateBucket` need `pend + 1 < 2^58` and `Unlock`
  `pend + hookMax < 2^58`; `authBatchTxLkR` allows unboundedly many puts per batch (`RoleDelete` puts one
  per user holding the role). The contract needs a budget at `Lock` (internal statement change, every
  auth store proof that holds `Lk`).
- **G5, the realization.** An invariant per backend `γc`: the idle auth part `rbOwnIn d.γB authBkts r`,
  `authLockI st` and the buckets' relation to `st` (at boot: `bootState` over empty buckets, which
  `authBucketsAt` does not cover since the revision key is absent; afterwards `authBucketsAt`), or `T`
  out (a batch open: the part is in `Lk`); the `bOpen` share lent to concurrent `RLock`s (each holding a
  part of `authCur`, so the release waits for none: a halving borrow protocol); the tickets `R` redeemed
  for `rdTok`s of `authRdSlots`; the lend (C5: `rbOwnIn_agree` against `rbOwn`); the lifecycle (C8:
  ghost); `Lock`/`Unlock` through `LockInsideApply`/`Unlock`'s first disjunct (no non-hook write
  pending, `thinV` kept: auth writes only hook buckets; auth would be the first proved writer of tracked
  hook buckets in a session: lease and membership writers are axioms) and `Unlock`'s `st.cnt.hw = false`.
  All provable over the backend's specs once G1, G4 hold.
- **`unsafeGetAllRoles`'s `[0x00, 0xff)` range** (F3, `roleListed`) and **UTF-8 roles** (F4) are already
  in the contract's text; the batch `UnsafeRange` spec gives `cursorRange` of the writer's contents,
  which is what F3 needs. No gap.

## 3. Plan (after Q1; each stage its own Draft/Freeze where it touches trusted or exported text)

| stage | content | Lean lines (est.) | trust base |
|---|---|---|---|
| A0 | **Restate the read contract** per Q1 (recommended: per-bucket recorded states, as SpecPlan's per-view form): `authReadTxOk`'s `Hs` over three states, `authReaderOk`'s reads each at its bucket's; `CheckPassword.spec`'s `passwordChecked` weakened; its users re-proved; the axiom review (`axiom` skill) of the restated `authSchemaSrv` | 400-900 | trusted text restated (hypothesis); ledger entry |
| A1 | G1: the backend read model over tracked hook buckets, with the window (Q2) | 3000-6000 (survey 2.5-10k) | none if proved; +1 backend law if kept trusted |
| A2 | G2: `unsafeForEach`, `batchTx.UnsafeForEach`, `baseReadTx.UnsafeForEach` specs and proofs; bbolt `Cursor.First_kv` (Q7) and bbolt `Bucket.ForEach` proved over it | 500-900 | +1 bbolt kv axiom |
| A3 | G3 + follow-up (a): `proto.MarshalUser`/`MarshalRole` trust-boundary specs mirroring `UnmarshalUser`/`Role` (Q3); `sizeCache` out of `↦□` in `userOptsIs`/`ownPermS`/`ownPermW` (Q4), callers adapted | 300-600 | +2 axioms, 2-3 trusted restatements |
| A4 | G4: the put budget in `authBatchTxLk(R)` (Q6), the auth store's admin proofs re-threaded | 400-800 | none (internal) |
| A5 | schema's write side: `authBatchTx.*` (12 methods), `authBackend.{BatchTx,ForceCommit,CreateAuthBuckets,GetAllUsers,GetAllRoles}`, `unsafeGetAll*`, `authReadTx.UnsafeGetAllUsers` | 1200-2000 | none |
| A6 | G5: the realization, C1-C11 at boot (`⊢ authSchemaSrv`), `authSchemaSnap` from the same per-backend lemma | 1500-2500 | removes the hypothesis |
| A7 | link: `hD22` dropped from `etcd_auth_safe`, `etcd_auth3_safe`, `etcd_authN_safe` and their `Main`/`Adequacy`/`MainLinked` chains (`authkv_startServer`, `etcd_auth3.wp_startMember`, `etcd_authN.wp_StartMemberAuth`, ...); collections and baseline updated | 150-300 | **closed statements change** (premise removed): to the user |

Total: about 7.5-14k lines with A1 proved; 4.5-8k with A1 trusted as one backend law (Q2).
Checkpoints: after A0 (statement stop), after A1's Draft, after A3's Freeze (trusted texts), before A7
(closed statements).

**Follow-up (b)** (the client send's `wireLen` holding `userOptsAt`): independent of this work (client
side); a separate small stage (Q5).

**Risks.** (1) A1's size and reach: it changes the backend's internal invariants (`sessWf`, every batch
operation, write-back, commit, the hook window, `Unlock`) and may change `rbOwn`'s representation, which
`backend.backend.Snapshot.wp_proof` (an axiom) mentions: a trusted restatement. (2) A0 ripples into the
auth store's reader specs and the server's `Authenticate` chain (`passwordChecked`), possibly into the
client model's freshness (`permittedSince`). (3) The window may matter beyond auth: any backend client
whose read contract promises one snapshot over hook buckets written with deletes (membership's
`MustReadMembersFromBackend`, an axiom; the lessor's reads) should be checked against R1 (Q9). (4) The
realization's `bOpen` borrow and the `Unlock` first-disjunct obligations are new for a proved
hook-bucket writer. (5) Memory: the auth chains' modules are large (the 64G cap; no bare `iframe` over
`authRdN` replicate lists).

## 4. Open questions (each with a recommendation)

- **Q1 (the refutation's fix).** (a) Per-bucket read states: `RLock` gives a state per auth bucket, each
  recorded (and ≥ the lower bound); single-bucket readers unchanged in meaning; `CheckPassword` returns
  the user at `s1` and the revision of `s2`, both recorded, `s1 ≤ s2` (the server's `Authenticate` OCC
  then argues with the apply-time re-read). (b) A fork change keeping `readTx` locked from write-back
  through the commit when a delete is pending (no etcd bug: against the fork's "fixes only" rule).
  (c) Record the half-applied state in the history (the writer would append an unreal state; the
  model's verdicts would be relative to it). **Recommend (a)**: it is what Go does, it is SpecPlan's
  per-view form, and it keeps the latest-state clause as is.
- **Q2 (A1 proved or trusted).** **Recommend proving it**, as its own staged sub-plan (Scope first),
  and doing A2-A6 over its statement meanwhile (as a local hypothesis in the realization's proof, not in
  any closed statement); the closed statements change once, at A7, when nothing is left trusted but the
  A2/A3 axioms.
- **Q3 (Marshal).** New axioms `proto.MarshalUser`/`MarshalRole` mirroring `UnmarshalUser`/`Role` over
  `userEncode`/`roleEncode` (**recommended**: small, the decode side's pattern), or register
  `authpb.User`/`Role` with the per-type models (`MarshalPb`/`UnmarshalPb`) and define the encodings
  from them (removes the opaque encodings and both Unmarshal axioms, more work; later).
- **Q4 (follow-up (a)).** **Recommend** fixing it in A3: `sizeCache` out of the read-only part of the
  nested messages (an owned or invariant-held cell), since the Marshal spec needs it.
- **Q5 (follow-up (b)).** **Recommend** a separate stage (the send predicate pinned to `userOptsIs o
  false (some [])`); not on this path.
- **Q6 (G4).** A put budget counted at `Lock` in `Lk` (**recommended**; the store bounds its puts per step
  by the users' count, which `authSmall` bounds) vs a time receipt per put.
- **Q7 (G2).** **Recommend** one bbolt kv axiom `Cursor.First_kv` (the twin of `Seek_kv`) and bbolt's
  `ForEach` proved over it, rather than a `Bucket.ForEach_kv` axiom.
- **Q8 (`authSchemaBoot`).** **Recommend deleting** it with the superseded exported
  `auth.newAuthStore_boot` (an exported-result removal: the user's), rather than restating it with a
  fancy update.
- **Q9 (R1 elsewhere).** **Recommend** a short check, outside this stage, of the other trusted readers of
  hook buckets written with deletes (membership's, the lessor's) against the window.
