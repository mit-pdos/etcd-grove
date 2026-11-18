# auth-schema-srv: handoff

## START HERE (2026-11-17, A6.2 C1-C5 written; targeted build pending/ see log)

- Branch `auth-schema-srv`, worktree `/shared/etcd-grove-authschema`; pin c6b39d4f8: `--packages=/shared/tmp/manifest-c6b.json`
  everywhere (`.lake/package-overrides.json` = that manifest). lean merged at f256fa496e (04b1fa5134).
- Decisions: questions.md "A6.2 second review" (GO for C1, MINORs folded) and "A6.2 C1-C5" (forms: invariant in the token,
  not `isBackend`; M1 by a clear claimed `γ.rbk` flag + `tkI := idle ∨ cw`; `newPostKP` unchanged, tokens beside it).
- Done (commits 9d…→a9fe8620fc): `InvBackend` (`rbClaimU/C/One/Inv`, `rbClaimN`, `rbClaimToks`, `rbPartF` ¼, `rbRd` q/2,
  uniform `rbrOne` ¼, `rbrSide` without `rbc`, `rbSide` holds the inv); `TrackedLemmas` (writes/flag clears over the inv,
  helpers); `ClaimedLemmas` (`rbOwnIn_claim` lock-free, token laws, stepR, `rbPartR_idle`); `NewAlloc` allocation;
  `newPostK` + `newPostK_pool`; `authRdSlots := rdAuth ∗ rbClaimToks authBkts`; boot (`BootBackend`, `boot_storage(R)`,
  NewServer(R)) and snapshot (`SnapApplyWalk`) threading; soundness note §6; forbidden laws in `bStopView`/`rbOwnInR`.
- Checked: lean-check of InvBackend, TrackedLemmas, ClaimedLemmas, InvBatch, NewAlloc, Unlock, RdPool, UnsafePut,
  unsafeCommit, newBackend, InvCommit: 0 errors. Targeted build (backend/etcdserver/mvccrand/mvccfull Links):
  `/shared/tmp/auth-schema-srv/c1-build2.log`.
- Next: fix the build's errors; C5 (`etc/gen-interface.py etc/api/backend.txt`, api-check, tcb `--check`: no axiom/sorry
  change expected); then A6 proper (realization invariant using `rbOwnIn_claim` in the update, write side, auth read
  contract); A7 HARD STOP (old → new statements: `authRdSlots`, `newPostK`, `rbPartF` fraction, `authSchemaSrv` tickets).
- Pitfalls: (0)-(10) of History "A6.1b STOP"; (11) `if` instances: `rbEls`/`rbClaimToks` use `Classical.propDecidable`;
  state helpers with a generic `S` (see `mapIf_one`) or `dsimp only` + explicit `@ite`; (12) after `cases hcl : Cl n`
  apply `rbClaimOne_U/C γ n _ rfl`, not `… (Cl n) hcl`; (13) build slots can be busy for >30 min.

## History

### A6.2 Scope STOP (2026-11-17, superseded)


- Branch `auth-schema-srv`, worktree `/shared/etcd-grove-authschema`; Perennial pin c6b39d4f8:
  `--packages=/shared/tmp/manifest-c6b.json` everywhere (`.lake/package-overrides.json` = that manifest). Scope
  `notes/auth-schema-srv-scope.md` §3 (A6, A7); decisions `questions.md` (untracked; "A6.2 decided").
- Done: A1-A5, A6.1a, the Held index, A6.1b, the lent family (History); (b) (8acf5658a9, ACCEPTED: `authSchemaSrv`'s
  tickets `authRdN` → `authRdN - 1`, for the A7 report; `authSchemaSnap` unchanged).
- **A6.2 Scope (this commit): `notes/auth-schema-srv-a6-claim-scope.md`**: a lock-free claim law `rbOwnIn_claim`
  (`isBackend ∗ rbOwnIn ={⊤}=∗ rbOwnInR ∗ rbRd ½`) over a new sealed invariant `rbClaimInv` in `isBackend` holding
  per tracked bucket shares of `rbk` (½), `rbr` (¼), `rbc` (whole, with its authority) and the link `f = false → v =
  bktOf c`; `rbPartF` (so `rbPart`/`rbOwnIn`/`rbOwn` and the lock's `rbSide`) scaled ½ → ¼ uniformly (Snapshot's
  observation hands the lock's share as an `rbOwn`); `rbRd q` = element `q/2`. 1000-2100 lines, backend only.
- Review (`/shared/tmp/auth-schema-srv/a6-claim-review.md`): B1 (second claim not refutable; `Close` hands the lock's
  share out) → §R.1 the per-bucket claim token (in `newPostK`, carried with `authRdSlots`); M1 → §R.2 the claimed
  flag cleared at `Unlock`'s end with the claim marker's; MINOR 1 already restated (§R.3).
- **STOP**: a short second review before any Lean (decided by etcd-grove-03).
- Next, after the review: C1-C5 of the Scope §5 (probe `wb_core`/`unsafeCommit` first), then A6 as planned
  (realization invariant, write side, auth-level read contract), then A7 HARD STOP.
- Pitfalls: as in History "A6.1b STOP" (0)-(10).


### A6.2 STOP (2026-11-17, superseded)


- Branch `auth-schema-srv`, worktree `/shared/etcd-grove-authschema`; Perennial pin c6b39d4f8:
  `--packages=/shared/tmp/manifest-c6b.json` everywhere (`.lake/package-overrides.json` = that manifest). Scope
  `notes/auth-schema-srv-scope.md` §3 (A6, A7); decisions `questions.md` (untracked; "A6.1b decided", "A6.2 STOP").
- Done: A1-A5, A6.1a, the Held index, A6.1b and the lent family (History; ACCEPTED). **(b)** (this commit):
  `authSchemaSrv` hands out `authRdN - 1` tickets (AuthSrv.lean; ledger "the auth realization's premise hands out one
  reader ticket fewer"); supply checked, no consumer short. Server `Link.lean` regenerated: unchanged (it already
  names A5/A6.1 proofs); built (`/shared/tmp/auth-schema-srv/a6-link1.log`).
- **STOP (blocker, questions.md "A6.2 STOP"):** readers before the realization's first claim. The realization's
  update returns `authBackendOk` (readers usable at once: `authCur γc 1`, `T`, the tickets all handed out), but a
  reader can only learn what it reads in a claimed bucket (`rtHeldF_rbRd`); the claim (`batchLocked_claim`) needs
  the batch lock, which a ghost update does not have; the idle unclaimed part (`rbOwnIn`) has no readers' law (A1
  decision 1 (a)). Same on every snapshot backend (`Recover`'s `T`-read comes before any batch `Lock`).
- Next, after the decision: the per-backend realization invariant (sketch in History, "A6.1b STOP"), the write side,
  the auth-level read contract; then A7 HARD STOP.
- Pitfalls: as in History "A6.1b STOP" (0)-(10).


### A6.1b STOP (2026-11-17, superseded)


- Branch `auth-schema-srv`, worktree `/shared/etcd-grove-authschema`; Perennial pin c6b39d4f8:
  `--packages=/shared/tmp/manifest-c6b.json` everywhere (`.lake/package-overrides.json` = that manifest). Scope
  `notes/auth-schema-srv-scope.md` §3 (A6, A7); decisions `questions.md` (untracked; "A6.1a decided", "A6.1b").
- Done: A1-A5 (History); A6.1a (b3ea959bf1, ACCEPTED); **the Held index** (952283bbfb, APPROVED): `Held : Loc →
  AuthData → IProp`, `GetUser`/`GetRole` take the caller's `Φ` as `GetAllUsers` (the stronger posts, done);
  **A6.1b** (a5cb6ded57) in `etcdserver/AuthRealRead.lean`: `heldR γ P b Y x D` (the token), `heldR_rdCap`
  (`rdB` → `rdCap`, a quarter of bbolt's tx lent), `heldR_point` ×3, `heldR_forEach`, `heldR_reader`,
  `authBE_real` (generic over the caller's ghost steps `Racq`/`Robs`/`Rrel`), `auth_isBucket` ×3; **the lent family**
  (this commit): `authRTx rt R L Held`/`authBE bi R L Held`, `L : ι → IProp` lent to `RLock` and given back (the
  realization borrows its open share against the caller's `authCur γc q`, or `T`); schema's six read specs take `L i`.
  Targeted build of the 7 modules green (`/shared/tmp/auth-schema-srv/held-build5.log`).
- **STOP (finding, questions.md "A6.1b"):** `authBackendReads`' read-transaction clauses (`GetUser`, `GetRole`,
  `GetAllUsers`: `{{T ∗ authOwn M hs}}`) take no reader ticket; schema's code runs `ReadTx().RLock()`, which needs
  an `rdTok`; the realization's only slots (`authRdSlots` = `authRdN` `rdTok`s) all back the premise's `authRdN`
  tickets `R`, any of which may be in use: the realization cannot supply the slot. Options (a)/(b) in questions.md.
- Next, after the decision: (1) the realization invariant per backend `γc` (design: questions.md "A6.1b", the
  sketch below); (2) the write side from A5's callee triples (claimed parts `rbOwnInR`/`rbRd`, `Unlock.spec`'s
  accessor at mask ⊤, receipts bound writes < receiptBound ≤ 2^48); (3) the auth-level read contract from schema's
  specs + post-processing (rtHeldF_rbRd at any time while held); then A7 HARD STOP.
- Realization sketch: `inv` per `γc` holding: `rbRd γB n ½ m_n` for the three auth buckets with each `m_n` the
  encoding of a recorded state (`authBucketsAre`-per-bucket), its index ≥ the published index (the realization's
  `authPubQ` quarter); `authWTok γc` when a batch is open (else the idle facts: every bucket = `authLockI`'s state);
  the `bOpen authOpenQ` vault, lent per `RLock` against `authCur γc q` (release needs `authCur 1`: none lent) or
  against `T`; the tickets ↔ `rdTok` exchange; the lifecycle (retired/released flags).
- Pitfalls: (0)-(7) as before (History, A5). (8) a spec binder `{ι : Type}` IS named by `intro` (`intro … Held ι L i`)
  but must NOT be passed explicitly when applying the spec (`hRT abe bi lg R Held L`). (9) the triple inside
  `authBE`'s `□ (…)`: `iintro !> %Φ !> - HΦ` (two `!>`); inside `authRTx`'s `□ (∀ i, …)`: `iintro !> %i !> %Ψ …`.
  (10) `wp_apply` of an Iris-hypothesis triple can fail silently into `sorry` under `--fast`: use
  `iapply H $$ %args %Ψ [pre] [post]`, then `inext`.


### A6.1a STOP (2026-11-17, superseded)

- Branch `auth-schema-srv`, worktree `/shared/etcd-grove-authschema`; Perennial pin c6b39d4f8:
  `--packages=/shared/tmp/manifest-c6b.json` everywhere (`.lake/package-overrides.json` = that manifest). Scope
  `notes/auth-schema-srv-scope.md` §3 (A6, A7); decisions `questions.md` (untracked; "A5 done", "A6.1a").
- Done: A1-A4 (History); A5 (5cc3a07e4b, ACCEPTED by etcd-grove-03: callee triples, `authForEachSpec`, `GetAllUsers`'
  `Φ`); **A6.1a (this commit)**: `backend.readTx.UnsafeForEach` (the promotion wrapper, spec + proof, linked in the
  backend's `Link`); `etcdserver/AuthRealRead.lean`: `rtForEach_perm` (a read transaction's walk is a permutation of
  `bktEnts (rvBkt P rv bi.name)`: table bucket, `rv.2.Wf`), `rtForEach_mem`, `sorted_mem_iff`, `rvAuth P rv` (the
  auth buckets a reader at `rv` reads). Targeted build: `/shared/tmp/auth-schema-srv/a6-build1.log`.
- **Finding (internal contract, form to apply next, questions.md "A6.1a")**: `schema.authRTx rt R Held` with `Held :
  AuthData → IProp` is NOT realizable by the real `readTx`: `authReader rt (Held D) D` promises persistently that a
  returned slice is readable under any `Held D` (`rdCap`/`pointValsA`), but a slice is bbolt's transaction's bytes
  (`rdB rtx`), valid only in its own read session, and `Held D` does not determine the session (two sessions can read
  the same `D`). Fix: index the token by the session's bbolt transaction, `Held : Loc → AuthData → IProp` (`RLock`'s
  post `∃ x D`, `RUnlock` `∀ x D`, `GetAllUsers`' `Φ` premise `∀ x D`); 12 files (`InvAuthBackend` and the six
  `authBackend.{ReadTx,GetUser,GetRole,GetAllUsers}`/`authReadTx.{RLock,RUnlock}` specs and proofs), mechanical.
- Next, in order: (1) the `Held` index above; (2) A6.1b in `AuthRealRead.lean`: `rdCap` from `rdB` under `Held x D :=
  ∃ rv, ⌜rvAuth P rv = D ∧ rv.2.Wf⌝ ∗ rtHeld γ P b x rv ∗ Y rv` (`rtHeldF_lend'` at `rfrac.half = ½·½ + ½·½`,
  `rdB_acc`, `rtHeldF_return`); `authPointSpec` ×3 (`readTx.UnsafeRange` at `rtHeld_eq`, `rtRange_single`,
  `kvsOutRd_single`/`_nil`; auth `isBucket` lemmas from `schemaInit` as `mvcc.meta_isBucket`, conjuncts 10-12);
  `authForEachSpec` (backend `I i := Ic (take i es)`, `E := False`, `List.take_succ`, `rtForEach_perm`); `authBE_real`
  generic in the caller's ghost steps (`R ={⊤}=∗ rdTok ∗ bOpen qo ∗ C`; after `readTx.RLock` an observation
  `rtHeld ∗ bOpen qo ∗ C ={⊤}=∗ rtHeld ∗ Y rv ∗ ⌜authWf (rvAuth P rv)⌝`; `RUnlock`: `rdTok ∗ Y rv ={⊤}=∗ R`);
  (3) the realization invariant per backend `γc` (claimed `rbRd` halves of the three buckets with their recorded
  states, `authLockI`, the `bOpen authOpenQ` vault with deposits of `authCur`, the tickets ↔ `rdTok` exchange, the
  lifecycle), the write side from A5's callee triples, `GetUser`/`GetRole` stronger posts in place; then A7 HARD STOP.
- Pitfalls: (0)-(6) of A5 (History) still apply. (7) `backend.bktEnts_sorted` and other backend lemmas sit in sections
  with `hG`/`package_sem` instance variables: a client file needs the same `variable` block to use them.



### A5 done (2026-11-17, superseded)


- Branch `auth-schema-srv`, worktree `/shared/etcd-grove-authschema`; Perennial pin c6b39d4f8:
  `--packages=/shared/tmp/manifest-c6b.json` everywhere (`.lake/package-overrides.json` = that manifest). Scope
  `notes/auth-schema-srv-scope.md` §3 (A2-A7); decisions `questions.md` (untracked; "A5 done").
- Done: A1 (52d85a42f6 … 6fe91f236f); A2 (72c59c8aff, f546a2dbb9); A3 (7a843bfc54); A4 (846a7fedd9, ACCEPTED).
- **A5 (5cc3a07e4b, this commit; lean merged 22235f7e13)**: full build green (`/shared/tmp/auth-schema-srv/a5-build1.log`); tcb +2 (MarshalUser/Role; baseline 900, server collection; auth collections unchanged); bounds 391 = baseline; axiom-tok ok. schema's write side and walks, 22 functions specified and proved
  (`Spec|Proof/go_etcd_io/etcd/server/v3/storage/schema/{authBatchTx__*,authBackend__{BatchTx,ForceCommit,
  CreateAuthBuckets,GetAllUsers,GetAllRoles},authReadTx__UnsafeGetAllUsers,unsafeGetAll{Users,Roles}}.lean`), over
  callee triples of the backend transaction (A6 instantiates them); `InvAuthBackend`: `rdCap`, `authForEachSpec`
  (in `authReader`), `authRolesRange`/`rolesRangeEnts`, `usersOutD`/`rolesOutD`, `abtF`; linked in the server's
  `Link` (MarshalUser/MarshalRole now reached).
- Next: A6, the realization (`⊢ authSchemaSrv`, `authSchemaSnap` from one per-backend lemma): derive `authBE`/
  `authRTx`/`authReader` for the real backend (readTx per bucket, `rbOwnInR`/claimed parts), instantiate A5's callee
  triples from `batchTxBuffered.*` with the claimed parts (`rbPutR`), `Unlock.spec`'s accessor, the receipts
  (`receipt_add_one_lt`: writes < receiptBound ≤ 2^48), strengthen `GetUser`/`GetRole` with the `Φ` premise as
  `GetAllUsers` (questions.md "A5 done"); then A7 HARD STOP.
- Pitfalls: (0) a hypothesis holding a triple on an abstract interface (`methods t.ty m t.v`) breaks `wp_start`'s
  `rw [method_unfold]` (it unifies with that occurrence: "MethodUnfold t.ty"): `wp_start_folded as …`, then
  `rw [MethodUnfold.method_unfold (t := go.GoType.PointerType <T>.ty) (m := go!"M")]`, `wp_call`; in a visitor
  subgoal `iclear` such a hypothesis first. (1) `wp_if_destruct`/`wp_apply` run `wp_auto`, which drops a resolution's
  receipt: `wp_apply +noauto`. (2) `imod` of a `|==>` only while the goal is a WP (not after the last step of a loop
  body: before `wp_store`). (3) `generalize … at *` once gave a kernel error with `word`: use `obtain ⟨es, hes⟩ : ∃
  es, … = es := ⟨_, rfl⟩; rw [hes]`. (4) a hand-written `if m = n` picks `instDecidableEqString`: write
  `@ite _ (m = n) (Classical.propDecidable _) …`. (5) keep `.lake/package-overrides.json`; `ls .lake/packages` = Qq,
  batteries, iris. (6) lean-check of a server file rebuilds its imports outside a slot: prefer the slot build.

### A4 done (2026-11-17, superseded)

- Branch `auth-schema-srv`, worktree `/shared/etcd-grove-authschema`; Perennial pin c6b39d4f8:
  `--packages=/shared/tmp/manifest-c6b.json` everywhere (`.lake/package-overrides.json` = that manifest). Scope
  `notes/auth-schema-srv-scope.md` §3 (A2-A7); decisions `questions.md` (untracked; read "A4 STOP").
- Done: A1 (52d85a42f6 … 6fe91f236f); A2 (72c59c8aff, f546a2dbb9); A3 (7a843bfc54, forms ACCEPTED by etcd-grove-03).
- **A4 (this commit)**: Route R (approved by etcd-grove-03): the six writes of `authBatchTxLk(R)` take `⧗ 1`; the
  store's proofs take it with `wp_take_receipt` (questions.md "A4 done"); axiom-tok entries for A2's ForEach axioms.
  Full build ok (`/shared/tmp/auth-schema-srv/a4-build1.log`); tcb --check matches (894/4); axiom-tok ok; bounds 391 =
  baseline; no interface changed.
- Next: A5 (schema's write side: `authBatchTx.*` over the backend's claimed parts `rbPutR`/kinds and `Unlock`'s
  accessor, `authBackend.{BatchTx,ForceCommit,CreateAuthBuckets,GetAllUsers,GetAllRoles}`, `unsafeGetAll*`,
  `authReadTx.UnsafeGetAllUsers`; A1 scope §9), then A6 (the realization: bounds a session's writes by the `⧗` it
  holds, `receipt_add_one_lt`); A7 HARD STOP.
- Pitfalls: (0) `wp_if_destruct`/`wp_apply` run `wp_auto`, which drops a resolution's receipt: `wp_apply +noauto`,
  or take the receipt at an earlier resolution. (1) `wp_join` cases end at the bare `R` (no update): to allocate an invariant in a case, make `R` an
  update `iprop(|={⊤}=> …)` and `imod` it in the continuation (`authStore__UserAdd*.lean`). (2) after `iunfold
  ownPermS`, name the field cells `#PermType, #Key, #RangeEnd`. (3) `BigSepL2.bigSepL_fupd E` is the list fupd lemma.
  (4) a hand-written `if m = n` picks `instDecidableEqString`: write `@ite _ (m = n) (Classical.propDecidable _) …`.
  (5) keep `.lake/package-overrides.json`; `ls .lake/packages` = Qq, batteries, iris. (6) `etc/gen-interface.py
  --layout` builds every package module: build first. (7) lean-check of a server file rebuilds its imports outside a
  slot (EtcdServer__UserAdd: 450 s): prefer the slot build for many importers.


### A4 STOP (2026-11-17, superseded)


- Branch `auth-schema-srv`, worktree `/shared/etcd-grove-authschema`; Perennial pin c6b39d4f8:
  `--packages=/shared/tmp/manifest-c6b.json` everywhere (`.lake/package-overrides.json` = that manifest). Scope
  `notes/auth-schema-srv-scope.md` §3 (A2-A7); decisions `questions.md` (untracked; read "A4 STOP").
- Done: A1 (52d85a42f6 … 6fe91f236f); A2 (72c59c8aff, f546a2dbb9); A3 (7a843bfc54, forms ACCEPTED by etcd-grove-03).
- A4: no Lean yet. The users-count route needs the fuel's base `b ≤ 2^61` (Fuel.lean `fuelOk`) tightened to
  `b ≤ 2^55`; b is the installed image's log length, bounded by raft's `readyFits` (`receiptBound + bootLen ≤ 2^61`)
  through the snapshot path, so tightening changes exported statements (raft `readyFits_intro`, `etcdstart.Alloc*`'s
  `Hrb2`, ...): STOPPED, questions.md "A4 STOP" has the chain. Alternative R (recommended): every write of the
  `authBatchTxLk(R)` contract costs `⧗ 1` (the store takes one at a Go step per loop iteration,
  `wp_go_step_receipt'`); the realization bounds a session's writes by the receipts it holds
  (`receipt_add_one_lt`: < receiptBound ≤ 2^48), so `pend0 + writes + hookMax < 2^57 + 2^48 + 2^16 < 2^58`.
- Next: the coordinator's choice (R, or the tightening with its exported changes); then A4, A5, A6; A7 HARD STOP.
- Pitfalls: (1) `wp_join` cases end at the bare `R` (no update): to allocate an invariant in a case, make `R` an
  update `iprop(|={⊤}=> …)` and `imod` it in the continuation (`authStore__UserAdd*.lean`). (2) after `iunfold
  ownPermS`, name the field cells `#PermType, #Key, #RangeEnd`. (3) `BigSepL2.bigSepL_fupd E` is the list fupd lemma.
  (4) a hand-written `if m = n` picks `instDecidableEqString`: write `@ite _ (m = n) (Classical.propDecidable _) …`.
  (5) keep `.lake/package-overrides.json`; `ls .lake/packages` = Qq, batteries, iris. (6) `etc/gen-interface.py
  --layout` builds every package module: build first. (7) lean-check of a server file rebuilds its imports outside a
  slot (EtcdServer__UserAdd: 450 s): prefer the slot build for many importers.

### A3 done (2026-11-17, superseded)

- Branch `auth-schema-srv`, worktree `/shared/etcd-grove-authschema`; Perennial pin c6b39d4f8:
  `--packages=/shared/tmp/manifest-c6b.json` everywhere (`.lake/package-overrides.json` = that manifest). Scope
  `notes/auth-schema-srv-scope.md` §3 (A2-A7); decisions `questions.md` (untracked).
- Done: A1 (52d85a42f6 … 6fe91f236f); A2 (72c59c8aff, f546a2dbb9); **A3 (this commit)**: Draft
  `notes/auth-schema-srv-a3-draft.md` applied with the attack's MINORs (`notes/axiom-review/auth-a3-marshal.md`):
  `Buckets.lean` (`pbSizeCacheN`, the three predicates per field, `permSizeCache_alloc`, `ownPermS_freeze`,
  `ownPermW_freeze`, `userOptsIs_freeze`, persist lemmas → `|={E}=>`), axiom files `Proof/.../proto/Marshal{User,Role}.lean`,
  `MarshalIRR` docstring, callers (auth store, `EtcdServer.UserAdd`, schema `GetRole`, `InvAuthBackend`, client
  `PerTypeAuth`/`authClient.{UserAdd,RoleGrantPermission}`); ledger entry; full build green
  (`/shared/tmp/auth-schema-srv/a3-build1.log`); `tcb-report --check` matches unchanged (894: the two new axioms
  are reached by no root until A5); no interface changed.
- Next: A4, the put budget in `authBatchTxLk(R)` (Q6, decision 2). **Open point to settle first**: `RoleDelete` puts
  one user per holder of the role, the backend needs `pend + 1 < 2^58`, and `authSmall` bounds the users only through
  the revision (≤ k + b + 1, b ≤ 2^61): the budget needs a users-count bound below 2^58 (e.g. a users-count field in
  `authSmall`, ≤ revision, with a tighter base), or a budget not derived from the state. Then A5, A6; A7 HARD STOP.
- Pitfalls: (1) `wp_join` cases end at the bare `R` (no update): to allocate an invariant in a case, make `R` an
  update `iprop(|={⊤}=> …)` and `imod` it in the continuation (`authStore__UserAdd*.lean`). (2) the per-field
  predicates: after `iunfold ownPermS`, name the field cells `#PermType, #Key, #RangeEnd` (wp_load finds them).
  (3) `BigSepL2.bigSepL_fupd E` is the list fupd lemma (odd namespace). (4) a hand-written `if m = n` picks
  `instDecidableEqString`: write `@ite _ (m = n) (Classical.propDecidable _) …`. (5) Stray Perennial clone: keep
  `.lake/package-overrides.json`; `ls .lake/packages` = Qq, batteries, iris. (6) `etc/gen-interface.py --layout`
  builds every package module: build first. (7) lean-check of a server file rebuilds its imports outside a slot
  (EtcdServer__UserAdd: 450 s): prefer the slot build for many importers.

### A3 Draft written (2026-11-17, superseded)

- Branch `auth-schema-srv`, worktree `/shared/etcd-grove-authschema`; Perennial pin c6b39d4f8:
  `--packages=/shared/tmp/manifest-c6b.json` everywhere (`.lake/package-overrides.json` = that manifest). Scope
  `notes/auth-schema-srv-scope.md` §3 (A2-A7); decisions `questions.md` (untracked).
- Done: A1 (52d85a42f6 … 6fe91f236f); A2 (72c59c8aff, f546a2dbb9; forms ACCEPTED by etcd-grove-03, promotion
  wrappers and an `rtForEach`↔`rvBkt` law deferred to A5); **A3 Draft (this commit)**:
  `notes/auth-schema-srv-a3-draft.md` (exact texts §2, meaning moves §3, Go evidence §4, family check §5,
  findings §6, decisions §7); specs `Spec/google_golang_org/protobuf/proto/Marshal{User,Role}.lean` (NOT axioms:
  no `Proof/` file); restated predicates elaborated in `Scratch/A3Preds.lean` (untracked); Go tests
  `examples/authpbmarshal/marshal_test.go` (10, pass with `-race`, `GOTOOLCHAIN=go1.27.3`).
- Waiting on: an independent attack of §2 (axiom skill) and etcd-grove-03's decisions §7.
- Next after the go (A3 Freeze): §2.2 into `Buckets.lean` (+ `pbSizeCacheN`), constructors to `inv_alloc`
  (`PerTypeAuth`, `RoleGrantPermission`'s `newPerm`, `ownPermX_persist`/`ownRoleX_persist` → fupd), readers to
  per-field loads, axiom files, MarshalIRR docstring (§2.4), tcb +2 at A5, interfaces. Then A4, A5.
- Pitfalls: (1) a hand-written `if m = n` picks `instDecidableEqString`, the laws' `if S n` (open Classical)
  `Classical.propDecidable`: write `@ite _ (m = n) (Classical.propDecidable _) …`. (2) `unfold` does not
  beta-reduce `(fun n => S n ∨ S' n) n`: `dsimp only`. (3) A theorem's default argument (`trkHalf_eq … I`) is
  filled with the default when omitted: pass it. (4) Macros: frame patterns as ``$(frameH `H)``. (5) Stray
  Perennial clone: keep `.lake/package-overrides.json`; `ls .lake/packages` = Qq, batteries, iris. (6)
  `etc/gen-interface.py --layout` builds every package module: build first. (7) simp normalizes
  `decide (a ∉ l)` to `!decide (a ∈ l)` inside Iris hyps. (8) Go tests: reading unexported fields with
  `reflect`+`unsafe` under `-race` needs `unsafe.Pointer(v.UnsafeAddr())` in one expression (checkptr).

### A2 done (2026-11-17, superseded)

- Branch `auth-schema-srv`, worktree `/shared/etcd-grove-authschema`; Perennial pin c6b39d4f8:
  `--packages=/shared/tmp/manifest-c6b.json` everywhere (`.lake/package-overrides.json` = that manifest). Scope
  `notes/auth-schema-srv-scope.md` §3 (A2-A7); decisions `questions.md` (untracked); A2 Draft
  `notes/auth-schema-srv-a2-draft.md`.
- Done: A1 (52d85a42f6 … 6fe91f236f); A2 axioms (72c59c8aff, attacked: survive); lean 3cd4b72599 merged (1dbe00041f);
  **A2 backend side (this commit)**: `FeSide`/`feOwn` (InvBackend: the walked transaction, read or write),
  `rtForEach` (Model2: bbolt's entries whose keys the buffer lacks, then the buffer's); specs+proofs
  `unsafeForEach` (one spec, `sd : FeSide`), `batchTx.UnsafeForEach`, `baseReadTx.UnsafeForEach`; linked
  (`etc/link-lean-first-backend.txt`); full build ok (`/shared/tmp/auth-schema-srv/a2-build2.log`); tcb baseline
  +2 exactly (`bbolt.Bucket.ForEach_kvr.wp_proof`, `ForEach_kvw.wp_proof`); backend interfaces + layout baseline.
- Not done (on demand, A5): `readTx`/`concurrentReadTx`/`batchTxBuffered` reach `UnsafeForEach` by Go method
  promotion (no translated wrapper); a law `rtForEach` ~ `rvBkt` (each key once) when the realization needs it.
- Next: A3 — write its Draft (Marshal axioms of `authpb.User`/`Role` mirroring the Unmarshal ones, `sizeCache` out
  of `↦□`, precedent restart1/Requests.lean) and STOP at its new trusted texts with Go evidence for attack.
- Pitfalls: (1) a hand-written `if m = n` picks `instDecidableEqString`, the laws' `if S n` (open Classical)
  `Classical.propDecidable`: write `@ite _ (m = n) (Classical.propDecidable _) …`. (2) `unfold` does not
  beta-reduce `(fun n => S n ∨ S' n) n`: `dsimp only`. (3) A theorem's default argument (`trkHalf_eq … I`) is
  filled with the default when omitted: pass it. (4) Macros: frame patterns as ``$(frameH `H)``. (5) Stray
  Perennial clone: keep `.lake/package-overrides.json`; `ls .lake/packages` = Qq, batteries, iris. (6)
  `etc/gen-interface.py --layout` builds every package module: build first. (7) simp normalizes
  `decide (a ∉ l)` to `!decide (a ∈ l)` inside Iris hyps: state filters in the `!decide` form; an iris hyp
  `iframe` will not match may still `iexact`. (8) Call an Iris-context spec with `wp_apply Hf $$ %a %b … [$H]`.

### A2 axioms (2026-11-17, superseded)

- Branch `auth-schema-srv`, worktree `/shared/etcd-grove-authschema`; Perennial pin c6b39d4f8:
  `--packages=/shared/tmp/manifest-c6b.json` everywhere. Scope `notes/auth-schema-srv-scope.md` §3 (A2-A7);
  decisions `questions.md` (untracked; **A1 decided by etcd-grove-03**); soundness `notes/auth-schema-srv-a1-soundness.md`.
- Done: A1.1-A1.9 (52d85a42f6 … 23e2504247); A1.10 (6fe91f236f): the coordinator's A1 decisions: one spec
  (`Unlock.spec` the claimed statement, `Unlock.wp_proof`; old text the corollary `Unlock.spec_free`, `UnlockBare.lean`;
  `UnlockClaimed.lean` gone); `trkSide_mode` private (`trkSide_mode_up`, `trkSide_mode_win` public); `rbPartR_idle`
  takes `tkI`; soundness §4.2/§5 updated. Full build ok (log `/shared/tmp/auth-schema-srv/a110-build1.log`), tcb
  baseline unchanged, interfaces regenerated.
- A2: (B) chosen by the user; attacked (SURVIVES, `notes/axiom-review/bbolt-foreach.md`), MINORs applied;
  axioms `bbolt.Bucket.ForEach_kvr.wp_proof`/`ForEach_kvw.wp_proof` added (72c59c8aff), reached by no root yet
  (the tcb baseline moves, +2, when the backend Link reaches them: rerun `etc/tcb-report.py --check --update`).
- Next, A2's backend side (Draft §4), specs as their `UnsafeRange` siblings:
  `unsafeForEach` (tx, bucket, visitor; read or write transaction: one spec, the transaction's side as a
  parameter, e.g. a disjunction of `txLive q ∗ rtxSnap D ∗ rtxStats` / `ownWTxG … S`, entries `bktEnts (bktOf D|S n)`,
  the visitor's spec as the axioms'); `batchTx.UnsafeForEach` (over `btW γ t st`, entries `bktEnts (bktOf st.S
  bi.name)`, as `batchTx.UnsafeRange`); `baseReadTx.UnsafeForEach` (over `baseRd`: buffer `ForEach` for the dups
  (`txReadBuffer.ForEach.spec`, `visitorSpec`), a `map[string]struct{}`, `unsafeForEach` under `txMu`, then the
  buffer's `ForEach`; the visitor sees bbolt's entries whose keys are not in the buffer, in order, then the
  buffer's (`bkOf rv.2.bks bi.id`), its bytes `rdB rtx`); then `readTx`/`concurrentReadTx` wrappers if the auth
  readers need them. Then A3 (its own Draft first, a stop). Merge lean (3cd4b72599 or later) before the next full
  build.
- Pitfalls: (1) a hand-written `if m = n` picks `instDecidableEqString`, the laws' `if S n` (open Classical)
  `Classical.propDecidable`: write `@ite _ (m = n) (Classical.propDecidable _) …`. (2) `unfold` does not
  beta-reduce `(fun n => S n ∨ S' n) n`: `dsimp only`. (3) A theorem's default argument (`trkHalf_eq … I`) is
  filled with the default when omitted: pass it. (4) Macros: frame patterns as ``$(frameH `H)``. (5) Stray
  Perennial clone: keep `.lake/package-overrides.json`; `ls .lake/packages` = Qq, batteries, iris. (6)
  `etc/gen-interface.py --layout` builds every package module (`AuthSplitDraft` too): build it first.


### A1.9 (2026-11-17, superseded)


- Branch `auth-schema-srv`, worktree `/shared/etcd-grove-authschema`; Perennial pin c6b39d4f8:
  `--packages=/shared/tmp/manifest-c6b.json` everywhere. A1 Scope `notes/auth-schema-srv-a1-scope.md`; decisions and
  forms `questions.md` (untracked; **A1.5 decided**, **A1.6-A1.9**); soundness `notes/auth-schema-srv-a1-soundness.md`
  (§4.1 discharged, §5 the claim).
- Done: A1.1-A1.5 (52d85a42f6 … 149ad8bdd5); A1.6-A1.8 496f8061dd (`rbSide … I`, `trkSide`'s `I = tkI P st`; idle
  steps at `Unlock`'s end; `batchLocked_claim`; claimed parts' split laws; `rbRd`/`rbrHalves` sealed); **A1.9 (this
  commit)**: full build ok (20455 jobs, log `/shared/tmp/auth-schema-srv/a19-build1.log`); `etc/tcb-report.py --check`
  matches the baseline (892 axioms, 4 sorries); interfaces regenerated (`ClaimedLemmas`, `TrkModel`, `UnlockClaimed`
  new); layout baseline + `Unlock.wp_proofC`; `etc/import-all.txt`: `ClaimedLemmas` sealed, allows for
  `ClaimedLemmas`/`ReadLemmas`; api-check 0 errors, import-all-check ok.
- Next: the coordinator's go after the A1 report; then A2-A7 (`notes/auth-schema-srv-scope.md` §3); before landing:
  merge lean, `etc/gates.sh` via land.sh (coordinator).
- Pitfalls: (1) a hand-written `if m = n` picks `instDecidableEqString`, the laws' `if S n` (open Classical)
  `Classical.propDecidable`: write `@ite _ (m = n) (Classical.propDecidable _) …`. (2) `unfold` does not
  beta-reduce `(fun n => S n ∨ S' n) n`: `dsimp only`. (3) A theorem's default argument (`trkHalf_eq … I`) is
  filled with the default when omitted: pass it. (4) Macros: frame patterns as ``$(frameH `H)``. (5) Stray
  Perennial clone: keep `.lake/package-overrides.json`; `ls .lake/packages` = Qq, batteries, iris.

### A1.6-A1.8 (2026-11-17, superseded)

- Branch `auth-schema-srv`, worktree `/shared/etcd-grove-authschema`; Perennial pin c6b39d4f8:
  `--packages=/shared/tmp/manifest-c6b.json` everywhere. A1 Scope `notes/auth-schema-srv-a1-scope.md`; decisions and
  forms `questions.md` (untracked; read **A1.5 decided** and **A1.6-A1.9**); soundness
  `notes/auth-schema-srv-a1-soundness.md` (§4.1 discharged, §5 the claim).
- Done: A1.1 52d85a42f6; A1.2a c0ae7d8a3e; A1.2b 0e825c0590; A1.3 b573c5d64e; A1.4 3e072b3ca8; A1.5 149ad8bdd5
  (accepted by etcd-grove-03); **A1.6-A1.8 (this commit)**: `rbSide … I` with `trkSide`'s `I = tkI P st` (flag
  clear ⇒ kind idle); idle steps moved to `Unlock`'s end (MAJOR 1); `batchLocked_claim` + claimed parts' split
  laws (`ClaimedLemmas.lean`, end); `rbRd`/`rbrHalves` sealed; `ClaimedLemmas`/`UnlockClaimed` importable.
  Checked with lean-check (TrackedLemmas, ClaimedLemmas, InvBatch, InvCommit, NewAlloc, ReadLemmas, unsafeCommit,
  Unlock: 0 errors). No full build yet.
- Next, A1.9: full build (`/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-c6b.json build`, retry on
  exit 143), `LAKE_OPTS=… etc/tcb-report.py --check` (no axiom/sorry change expected), `etc/gen-interface.py
  etc/api/backend.txt` (+ `--layout --update`: `Unlock.wp_proofC` a new layout entry), `etc/api-check.py
  etc/api/backend.txt --check`, `etc/import-all-check.py`; commit; report A1's end to etcd-grove-03.
- Then A2-A7 (`notes/auth-schema-srv-scope.md` §3).
- Pitfalls: (1) a hand-written `if m = n` picks `instDecidableEqString`, the laws' `if S n` (open Classical)
  `Classical.propDecidable`: write `@ite _ (m = n) (Classical.propDecidable _) …`. (2) `unfold` does not
  beta-reduce `(fun n => S n ∨ S' n) n`: `dsimp only`. (3) A default argument of a theorem (`trkHalf_eq … I`) is
  filled with the default when omitted: pass it. (4) Macros: frame patterns as ``$(frameH `H)``. (5) Stray
  Perennial clone: keep `.lake/package-overrides.json`; `ls .lake/packages` = Qq, batteries, iris.

### A1.5 (2026-11-17, superseded)

- Branch `auth-schema-srv`, worktree `/shared/etcd-grove-authschema`; Perennial pin c6b39d4f8:
  `--packages=/shared/tmp/manifest-c6b.json` everywhere. A1 Scope `notes/auth-schema-srv-a1-scope.md`; decisions and
  forms `questions.md` (read **A1.5** first); soundness `notes/auth-schema-srv-a1-soundness.md` (complete, §4 the
  obligations; review of A1.4: `/shared/tmp/auth-schema-srv/a1-soundness-review.md`).
- Done: A1.1 52d85a42f6; A1.2a c0ae7d8a3e; A1.2b 0e825c0590; A1.3 b573c5d64e; A1.4 3e072b3ca8; **A1.5 (this commit)**:
  `ClaimedLemmas.lean` (`rbAcc`, `unlockOk`, `trkSide_updR`, `trkSide_mode`, `rbPartR_idle` private, `batchGhostAt_clr`,
  `batchLocked_claimed`/`_cwOk`/`_rbPartR_RB`); `UnlockClaimed.lean` (`Unlock.specC`); `Unlock.wp_proofC`, and
  `Unlock.wp_proof` its corollary; mode on `batchLockedW`/`batchGhostW`; `commit`/`unsafeCommit` specs take `c Sc Rr`;
  `wbSt` resets `cw` on buckets left idle. Built (targeted, log `/shared/tmp/auth-schema-srv/a15-build1.log`): backend
  `Link`, `OnPreCommitUnsafe`, `CindexBackend`, `lessor.initAndRecover`, mvcc `BackendBridge`. No full build;
  interfaces not regenerated (A1.9).
- Waiting on: etcd-grove-03's review of the A1.5 forms (questions.md A1.5) and the soundness argument.
- Next after the go: A1.6 (lock-free commits keep `γ.rbr`: mostly done by A1.5's commit change), A1.7 the claim law
  **with** the invariant "flag false ⇒ tk idle" in `rbrOne` and `unlock_idle`/`unlock_idleR` moved to `Unlock`'s end
  (soundness §4.1, open item), A1.8 callers (rename `specC` → `spec`?), A1.9 interfaces/gates (add `ClaimedLemmas`,
  `UnlockClaimed` to `etc/api/backend.txt`; `Unlock.wp_proofC` is a new layout entry; seal `rbrHalves`?).
- Pitfalls: (1) `ihave H := lemma $$ [A B]` opens a subgoal for the premise FIRST: use `$$ [$A $B]`. (2) In
  `bu_commit` the commit pre's tail after `iframe` is `commitReq ∗ ⌜…⌝ ∗ Rr` (X already gone). (3) `.rfl` converts
  `batchPhys`/`batchGhostAt` between `st` and `st.clrCw` (no definition reads `cw` but `rbrSide`/`rbrOne`/`cwOk`/
  `trkKept`). (4) `rw` with a higher-order `?Φ k` pattern fails: pass the family explicitly. (5) Stray Perennial
  clone: keep `.lake/package-overrides.json`; `ls .lake/packages` = Qq, batteries, iris. Builds: `/shared/tmp/build-slot.sh
  lake --packages=/shared/tmp/manifest-c6b.json build <targets>`; lean-check with `LAKE_OPTS=--packages=…`, `-q`, `--stop`
  before builds.

### A1.4 (2026-11-17, superseded)

- Branch `auth-schema-srv`, worktree `/shared/etcd-grove-authschema`; Perennial pin c6b39d4f8:
  `--packages=/shared/tmp/manifest-c6b.json` everywhere. A1 Scope `notes/auth-schema-srv-a1-scope.md`; decisions and
  forms `questions.md` (A1.1, A1.2a, A1.2b, **A1.4**: read A1.4 first).
- Done: A1.1 52d85a42f6; A1.2a c0ae7d8a3e; A1.2b 0e825c0590; A1.3 b573c5d64e; **A1.4 (this commit)**: `BSess.cw`;
  the mode `c` (trailing default `false`) on `batchLocked`…`rbrSide`, `cwOk`; sealed claimed parts
  `rbPartRF`/`rbPartR`/`rbOwnInR` (half a `γ.rbc` element); `rbPut … k` (`k = true`: `rbPutR`); `rbrOne`'s claimed
  branch `tk idle ∨ cw` with the `γ.rbk` half as `rbPart`; the five write specs `∀ (c k) {_hkc : k ≤ c}`;
  `trkKept` keeps `cw` (ledger addendum). Built (targeted): backend `Link`, mvcc `BackendBridge`/`NewStoreSessReal`/
  `BackendRecsSnap`/`NewStoreRCallers`, `InvHooks`, `OnPreCommitUnsafe`, `CindexBackend`, `lessor.initAndRecover`,
  and the 31 importers naming the write specs/`batchLocked`/`hookStep` (`/shared/tmp/auth-schema-srv/a14-targets.txt`,
  log `a14-build4.log`). No full build; interfaces not regenerated (A1.9).
- Next, A1.5: `Unlock`'s accessor (Scope D5): mode-`c` `Unlock.spec` with the claimed set `Sc`, premise
  `∀ n, st.cw n → n ∈ Sc`, the client's halves `rbRd γ n ½ _` reached by `Rr ={⊤}=∗ …` at the write-back
  (`rtRes_wb_close*`'s update wand, built today by `trkSide_upd`) and at the commit (`rtRes_cm_close`, in
  `unsafeCommit`); `Unlock.spec_old` the `Sc = ∅`, `c = false` corollary. Design points already fixed: `cw` kept by
  the write-back for `del` buckets, reset for buckets that become idle (decide in `wbSt`); the commit runs the hook in
  the client-facing mode with `cw` non-empty (allowed: `cnt.hw = true`), the hook keeps `cw` (`trkKept`); replace
  `rbrSide_step`/`trkSide_upd`'s "`cw` empty" premises by the accessor. Then the HARD STOP: complete
  `notes/auth-schema-srv-a1-soundness.md` (draft written; §4.1, the claim law's invariant vs the axioms returning
  `rbOwnIn`, is the point to attack) and report.
- Pitfalls: (1) `simp only [↓reduceIte]` does not reduce `if false = true`: `rbPut`'s new `if k` needs
  `Bool.false_eq_true` where an `RB = true` branch is simplified. (2) A Lean arrow after a spec's trailing binders
  becomes an open goal under `wp_apply` (`forallMetaTelescope` + `wp_apply_side` decides only arithmetic): hence
  `{_hkc : k ≤ c}`; a caller that does not frame `rbPut` must pass `false false`. (3) `hookStep` 13 conjuncts, the last
  `trkKept` (3 now: W, tk, cw); `bgOk` 10; `freeOk` 6. (4) Stray Perennial clone: keep `.lake/package-overrides.json`
  (copy of the c6b manifest); `ls .lake/packages` = Qq, batteries, iris. Builds: `/shared/tmp/build-slot.sh lake
  --packages=/shared/tmp/manifest-c6b.json build <targets>`; lean-check with `LAKE_OPTS=--packages=…`, `-q`, `--stop`
  before builds.


### A1.2b/A1.3 (2026-11-17, superseded)


- Branch `auth-schema-srv`, worktree `/shared/etcd-grove-authschema`; lean 9702d5707e merged. Perennial pin c6b39d4f8:
  `--packages=/shared/tmp/manifest-c6b.json` everywhere. A1 Scope `notes/auth-schema-srv-a1-scope.md`; decisions
  `questions.md` ("A1 Scope decided", forms "A1.1", "A1.2a", "A1.2b": read A1.2b's design gap first).
- Done: A1.1 (52d85a42f6); A1.2a (c0ae7d8a3e); A1.2b (this commit): `BNames.rbr`/`rbc`; `rbrHalves` in `clnPart`
  and `rtCm`; `rbrOne`/`rbrSide` (sealed) inside `trkSide` (replaces `trkHalf` in `batchGhostAt`/`W`); laws in
  `TrackedLemmas.lean` (end): `rbr_alloc`, `rbrSide_init`, `rbrHalves_frac`, `rbrSide_congr`, `rbrSide_write`
  (claimed bucket excluded: `rbr_claimed_excl`), `rbrSide_step`, `trkSide_congr`, `trkSide_upd`; read-side steps take
  the update wand; `batchGhost_step*` take the kinds of the other buckets (`hK`). Built: backend `Link`,
  `BackendBridge`, `OnPreCommitUnsafe`, `CindexBackend`, `lessor.initAndRecover`, `MustUnsafeGetAllLeases`. No full
  build yet; interfaces (`etc/gen-interface.py etc/api/backend.txt`) not regenerated (do at A1.9).
- A1.3 (next commit): `rbRd γ n q v` (`InvBackend`: `⌜n ∈ rbD⌝ ∗` half-element of `γ.rbr`), in `ReadLemmas`:
  `rbrHalves_agree`, **`rtHeldF_rbRd`** (the readers' law, D4), `rbRd_frac`, `rbRd_agree`. Built `ReadLemmas`.
- Next, in order: A1.4 claimed parts `rbPartR`/`rbOwnInR`
  (sealed: half of `γ.rbc`'s element `some (r n, F)`), `BSess.cw` (A1.2b gap), writes through either part; A1.5
  `Unlock` accessor (wand into `rtRes_wb_close*`/`rtRes_cm_close` built from `trkSide` + client halves), STOP with
  the soundness argument (decision 5).
- Pitfalls: (1) **the stray Perennial clone's cause**: `lake serve`'s workers run `lake setup-file` without
  `--packages`, so `etc/lean-check.py` cloned and built Perennial into `.lake/packages/perennial`. Fixed here by
  `.lake/package-overrides.json` (a copy of `/shared/tmp/manifest-c6b.json`; Lake reads it on every invocation):
  keep it; check `ls .lake/packages` (Qq, batteries, iris only). (2) `hookStep` 13 conjuncts, `bgOk` 10
  (`Hbg.2.2.2.2.2.2.2.2.2.2.1` is `trkOk`), `freeOk` 6. (3) `iframe` does not see `(commitSt …).S` as `st'.S`:
  convert with `(show … ⊢ … from .rfl)`. Builds: `/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-c6b.json
  build <targets>`; lean-check with `LAKE_OPTS=--packages=…`, `-q`, `--stop` before builds.


### A1.2a (2026-11-17, superseded)


- Branch `auth-schema-srv`, worktree `/shared/etcd-grove-authschema`; lean 9702d5707e merged (2f92623f49; Perennial
  pin c6b39d4f8: use `--packages=/shared/tmp/manifest-c6b.json` everywhere). A1 Scope
  `notes/auth-schema-srv-a1-scope.md`; decisions `questions.md` ("A1 Scope decided", forms "A1.1", "A1.2a").
- Done: A1.1 (52d85a42f6, `TrkModel.lean`); A1.2a (c0ae7d8a3e): `RbK`/`TkMap`/`tkSet`/`tkWb`/`wEmpty`/`kOk`/
  `trkOk`/`trkKept` in `Model2.lean`, `BSess.tk`, `trkOk` in `bgOk`, kinds idle in `freeOk`, `hookStep` keeps
  `trkKept` (ledger 2026-11-17), commit specs take "kinds idle or del"; backend `Link`, `InvHooks`,
  `OnPreCommitUnsafe`, `CindexBackend`, `BackendBridge`, `lessor.initAndRecover`, `BootBackend`, `InvApply`,
  `InvBoot`, `MustUnsafeGetAllLeases` build. No full build yet.
- Next, A1.2b (design fixed, not started): BNames `rbr` (ghost map name ↦ `BktData`, the readers' contents
  `rvBkt P rv n` of each name of `rbD`) and `rbc` (ghost map name ↦ `Bool`, claimed). The `rbr` authority (`∃ M`,
  full) and the `rbc` authority on the **batch lock side** (every `rv` change, write-back and commit, holds the batch
  lock). Element halves: `readTx.mu`'s ½ split by `q` (add `[∗map] n ∈ rbD, elem γ.rbr n (q/2) (rvBkt P rv n)` to
  `clnPart`, which takes `rv`; 19 uses), the other ½ on the lock side for an unclaimed bucket (`elem γ.rbc n 1
  false ∗ elem γ.rbr n ½ (rvBkt P (st.C, st.R) n)`) or the client's (`rbRd γ n q v := elem γ.rbr n q v ∗ elem γ.rbc
  n □ true`). Where the lock side goes: a new conjunct of `batchGhostAt` (many `%Hok⟩` patterns) or inside
  `trkHalf` given `(C, R)` (fewer sites): decide by counting. Allocation in `NewAlloc.lean` beside `rbEls_alloc`
  (line ~535). Then A1.3 (readers' law from `clnPart`'s halves), A1.4 (claimed parts `rbPartR`/`rbOwnInR`,
  sealed), A1.5 (`Unlock` accessor; update the halves in `ReadSide`'s `rtRes_wb_close*`/`rtRes_cm_close`), STOP
  at A1.5 with the soundness argument (decision 5).
- Pitfalls: a stray Perennial clone appears in `.lake/packages` (twice now; moved to
  `/shared/tmp/auth-schema-srv/perennial-stray*`): check `ls .lake/packages` before building (only Qq, batteries,
  iris links). `hookStep` has 13 conjuncts (the last `trkKept`), `bgOk` 10 (the last `w ≤ ver ∧ trkOk ∧ free→idle`:
  `Hbg.2.2.2.2.2.2.2.2.2.2.1` is `trkOk`), `freeOk` 6 (`.2.2.2.2.1` is `hw`). Builds via `/shared/tmp/build-slot.sh
  lake --packages=/shared/tmp/manifest-c6b.json build ...`; edit scripts in `/shared/tmp/auth-schema-srv/scripts/`.

### A0 land stop (2026-11-17)

- Branch `auth-schema-srv`, worktree `/shared/etcd-grove-authschema`. Session row in `/shared/etcd-grove-sessions.md`.
  Decisions: `questions.md` (Q1 (a), Q2-Q9; the A0 items, accepted).
- Done: Scope (b4528c167d); A0, the soundness repair (73ca90894e; accepted by the coordinator); lean 1612a1143a
  (k8s 7f-6 D) merged (2913cbf0a7: STATUS Last-updated ten newest, 7f-5a-P and kvreconfN moved to status-history;
  ledger both sides). Full build ok; `etc/gates.sh` all passed (tcb 877/4 = baseline, 65 collections, axiom-tok,
  bounds 390, mode 453, interfaces, links current), log `/shared/tmp/auth-schema-srv/gates-merge.log`.
- Now: the coordinator runs `etc/land.sh`. No commits to this branch until it says the land finished.
- Next, after the land: A1's own Scope (the backend read model over tracked hook buckets, with the window: per
  bucket, put buckets after, delete buckets before; over the backend's `RdSt` window flag and `dls`, per the Q9
  audit), then stop; then A2-A6, A7 (closed statements, to the user). Scope §3.
- Go tests: copy the test files into `server/storage/schema` of the clone `/shared/tmp/auth-schema-srv/etcd`
  (fork pin 6e8f0c004); `cd server; PATH=/usr/local/go/bin:$PATH TMPDIR=/shared/tmp systemd-run --scope -q -p
  MemoryMax=32G env GOWORK=off GOTOOLCHAIN=go1.27.3 go test ./storage/schema/ -run TestAuthSchemaRead -count=1 -v`.
- Pitfalls: `Model.lean` already has an `AuthView` (isOpPermitted's four views): the bucket view is `BkView`.
  `iexact` does not see through `(fun st => Hs (BkView.uni st)) st` vs `Hs (BkView.uni st)` or
  `(BkView.uni st).atUsers`: `dsimp only [BkView.uni]` first. Builds: `/shared/tmp/build-slot.sh lake
  --packages=/shared/tmp/manifest-e9e.json build ...`; `LAKE_OPTS=--packages=/shared/tmp/manifest-e9e.json` for
  `etc/lean-check.py` (it printed nothing on a module whose import failed to build: build first). The worktree's
  `.lake/packages` had a stray Perennial clone (at e9e6351d9); moved to
  `/shared/tmp/auth-schema-srv/perennial-stray-from-worktree` so gates link PERENNIAL_CHECKOUT.

### Scope (2026-11-16, HARD STOP, refutation)

- Branch `auth-schema-srv`, worktree `/shared/etcd-grove-authschema` (lean 8448906500 merged, fast-forward;
  the Scope commit on top). Session row in `/shared/etcd-grove-sessions.md` ("auth-schema-srv agent of
  etcd-grove-02").
- Done (notes only, no Lean): the Scope `notes/auth-schema-srv-scope.md`; the refutation R1 recorded
  (`notes/auth-schema-srv-refuted.md`, "Second refutation"; nonissue
  `nonissues/etcd-auth-readtx-delete-window-mixed-state.md` with its Go test; STATUS section "Refuted
  hypothesis" and Last-updated entry).
- R1 in one line: `authReadTxOk`'s one-state `RLock` is false (Unlock writes puts back, releases
  `readTx`, then commits the delete), so `authSchemaSrv` is false and the three auth closed theorems are
  vacuous; `CheckPassword.spec` too.
- Waiting on: etcd-grove-02 / the user, Scope §4 Q1-Q9 (Q1 the fix: per-bucket read states recommended;
  Q2 the backend read model proved as its own sub-plan; Q3 Marshal axioms; Q4 `sizeCache` fix; Q8
  delete `authSchemaBoot`/`newAuthStore_boot`).
- Next, in order, once Q1 is decided: A0 (restate the read contract and `CheckPassword.spec`, axiom
  review; statement stop), then A1's own Scope (the backend read model over tracked hook buckets),
  A2-A6 over A1's statement, A7 (drop `hD22`: closed statements, to the user). Scope §3.
- Go test: copy `nonissues/etcd-auth-readtx-delete-window-mixed-state/zz_authschema_window_test.go` into
  `server/storage/schema` of an etcd clone at the fork pin 6e8f0c004 (a clone is at
  `/shared/tmp/auth-schema-srv/etcd`); run under `systemd-run --scope -q -p MemoryMax=32G` with
  `GOWORK=off GOTOOLCHAIN=go1.27.3 go test ./storage/schema/ -run TestAuthSchemaReadWindowMixedState -count=1 -v`.
  It fails on the first `UserDelete` (3/3 runs).
- Pitfalls: the worktree's `.lake/build` was moved in and is not current: `etc/tcb-report.py` refuses until
  a build (`/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-e9e.json build ...`); the auth
  collections show no schema auth axiom anyway (all behind the hypothesis). `notes/status-history.md` is
  append-only: merge lean before touching it.
