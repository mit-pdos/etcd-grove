# Review of the compactor pilot's boundary specs (branch `compactor-pilot`, 814240a12b)

Independent review against `notes/spec-first-plan.md` "Phase 1b". I did not read the "Step 2b"
paragraph of the pilot plan. Go is quoted at the pin: `.lake/go-src/etcd/...`, and clockwork v0.5.0
(present in `~/go/pkg/mod`). Paths are relative to `/shared/etcd-grove-cp`. **No bug in the Go
code beyond what `issues/` already records** (the tiny periodic retention; negative retentions are
etcd-io/etcd#22396, cited in that issue).

## Ranking, most to least in need of revision

1. `EtcdServer.Compact.spec`: several requirement failures (sufficiency for both callers, an
   unneeded premise, probably unprovable as it stands).
2. `compactableOk` / `revGetterOk`, the environment contracts: requirement failures that block
   `Run`'s proofs and the server's glue.
3. The clock axioms and `perPermit`: true, but `perPermit` as stated is vacuous, and the version
   that means something cannot be proved from these axioms.
4. `v3compactor.New.spec`: sound. One premise is stronger than the code needs (it comes from the
   clock), plus coupling.
5. `clockwork.NewRealClock.spec`: true of clockwork v0.5.0. Its weaknesses are all `clockOk`'s.
6. `compactorOk`, `revPermit`, `compactReqIs`, `revLb`, `modePermit`, `CompactEnv`: good. Only
   preferences.

---

## 1. `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__Compact.lean`

**Good, keep:** the resource pair it gives back (`srvLeadTimeReader s ∗ E.RD`) is what makes it
usable as the compactor's `R`. It uses the same pre vocabulary as `processInternalRaftRequestOnce`
and `Put`. `idCred` is persistent (`idutil/Defs.lean:265`), so the compactor can call it repeatedly.

**F1.1 (requirement: sufficiency, the compactor).** The post says nothing about `(resp, err)`.
- Both `Run`s do `if err == nil || errors.Is(err, mvcc.ErrCompacted)` (`periodic.go:143`,
  `revision.go:93`).
- `errors.Is.spec` (`Spec/errors/Is.lean:43`) needs `errorIsTree S M target ∗ ⌜S err⌝`. Nothing in
  the chain `Compact.spec` → `compactableOk` → `Run` supplies it.
- `processInternalRaftRequestOnce` already gives `applyErrIs err` on failure, and `applyErrIs`
  (`apply/Base.lean:124`) carries exactly the error-tree fact `errors.Is` needs.
- **Restate:** post `srvLeadTimeReader s ∗ E.RD ∗ ((⌜err = nil ∧ resp ≠ null⌝ ∗ …) ∨ (⌜resp = null ∧ err ≠ nil⌝ ∗ applyErrIs err))`.

**F1.2 (requirement: sufficiency, the gRPC caller).** `kvServer.Compact` reaches the server
through `v3rpc.compactOk` (`api/v3rpc/InvAuthAdmin.lean:154`), a premise of
`kvServer.Compact.spec`. Whoever links v3rpc to the server must discharge `compactOk` from this
spec, and cannot:
- `compactOk` takes any request: any revision, and `Physical` may be true. This spec demands
  `compactReqIs p r` (Physical false) and `revLb E.γ.idx r`, which a client cannot supply.
- `compactOk` promises, on success, `resp ≠ null`, `Header ↦□ h`, `hdrW h`, `hdrRevIn`; on failure,
  `srvErrIs err`; and in both cases the client's `Q` from `Pin`. This post gives none of these.
- It takes `adminRes E.authMode ai`. This spec is auth-off only (F1.4).

The pilot plan puts client compactions out of the *workload*, but `compactOk` is an existing
caller of the same Go method.
- **Restate** on `Put.spec`'s pattern: any `r` and `physical`. The physical branch
  (`v3_server.go:404-415`) waits on `Physc` and calls `s.be.ForceCommit()` under `bemu.RLock`, so
  it needs a `srvBemuReader`-style resource in the pre.
- Post: `appliedHdr`-style header facts, the error disjunct above, and the client's update through
  a compaction form of `reqPropOk`.
- At minimum, if the gRPC side stays out of scope, record in `notes/` that this spec does not
  discharge `v3rpc.compactOk`, and why.

**F1.3 (requirement: no unneeded premise, plus sufficiency for `NewServer`).**
`revLb E.γ.idx r` is not needed by the code.
- A compaction at a future revision is applied as `ErrFutureRev` (mvcc `store.Compact`), which is
  harmless.
- The premise also breaks `NewServer`'s glue in revision mode with a negative retention. etcd
  accepts that: `parseCompactionRetention` (`embed/etcd.go:928-945`) sends `"-5ns"` to
  `time.ParseDuration`, giving retention −5. `Revision.Run` then compacts at `Rev()+5`
  (`revision.go:81`). `revPermit γi (-5) r` gives `revLb (r-5)`, not `revLb r`, so the server cannot
  turn `modePermit` into `Compact`'s pre.
- The premise is there to carry C1 into the model for C3, which is legitimate ("a stronger result
  needs it"). But hard-coding `revLb` couples `Compact` to one permit.
- **Restate:** take the permit as a parameter the server's KV invariant accepts (for example
  `Pc r` for a `Pc` fixed when `NewServer` registers the compactor; the compactor's `P` must imply
  it), with `revLb` as one instance. Or drop it, and let the model's compaction step take effect
  only at `r ≤` the current revision (which is what mvcc does).
- If `revLb` stays, `NewServer` needs a premise `mode = revision → 0 ≤ retention` that the
  configuration does not guarantee. Record it in `issues/etcd-compactor-periodic-tiny-retention.md`'s
  sibling list, or in a new issue (#22396 would fix it upstream).

**F1.4 (requirement: sufficiency for an auth-on server).**
- The pre is over `isServerReq` (= `isServerReqM false`, `ReqOn.lean:275`).
- The compactor runs whatever the auth mode is, and the server proofs now have `specM`/`specOn`
  variants (`processInternalRaftRequestOnce.specM`, `Put.specOn`).
- With auth on, the server cannot establish `isServerReq` (it needs `waitInvM true`,
  `kvInvM true`). *Uncertain:* whether any current `NewServer` instance runs with auth on.
- **Restate:** `Compact.specM (on : Bool)` over `isServerReqM on`, as `processInternalRaftRequestOnce`
  does.

**F1.5 (requirement: probably not provable as stated; uncertain).**
- `Compact` ends with `resp.Header.Revision = s.kv.Rev()` (`v3_server.go:429`). `store.Rev.spec`
  (`storage/mvcc/store__Rev.lean`) needs `storeReaderC s γ` (exclusive reader slots of `mu` and
  `revMu`, and a `γ.tk` token) and `ownToks γ.revs m`.
- Nothing in this pre (`isServerReq`, `srvLeadTimeReader`, `E.RD`) gives access to `s.kv` or such a
  slot. I found no request-side proof that calls `s.kv.Rev()`.
- `Compact` also calls `traceutil.Tracer.Start`, `EnsureTrace` and `LogIfLong` (otel). Their specs
  are callee work, not a spec defect.
- **Restate:** add the kv reader resource to the pre and give it back in the post (it then becomes
  part of the compactor's `R`). Or show that an `isServerReq` field already provides it.

**F1.6 (requirement: sufficiency, `NewServer`; known open item 3 of the plan).**
- `isServerReq` exists only from `Start`, but the compactor's goroutine can call `Compact` from
  `NewServer` on.
- The `R` threading in `compactableOk` is the right hook: let the server's `R` include a
  "started-or-wait" resource. Leave this open until the glue is written.

**F1.7 (preference: post no stronger than needed).** Once F1.1/F1.2 are done, the compactor needs
only "R back ∗ err nil or an error tree". Keep the rich post for the gRPC caller and derive the
compactor's from it in the glue.

---

## 2. `compactableOk`, `revGetterOk` (`api/v3compactor/Defs.lean:84,100`)

**Good, keep:**
- Persistent contracts on interface values, with the permit `P` as the C1 obligation. This is a
  clean split: C1 is exactly what `Run` proves at each call.
- Threading the per-goroutine resource `R`, and quantifying over any context.
- `compactReqIs` handing over the fresh request.

**F2.1 (requirement: sufficiency, `Run`'s proofs).** `compactableOk`'s post is
`WP … {{ fun _ => R }}`.
- Go destructures `_, err := pc.c.Compact(…)` and tests `err`.
- With an arbitrary result value, the proof cannot show the result is a pair, and has no fact for
  `errors.Is` (F1.1).
- **Restate:**
  `WP … {{ v, ∃ (resp : Loc) (err : GoInterface), ⌜v = PairV #resp #err⌝ ∗ R ∗ (⌜err = nil⌝ ∨ errTreeOk err) }}`.
  `errTreeOk` is the first conjunct of `apply.applyErrIs`, which is a fact about Go errors, not
  about the server. Per CLAUDE.md "There is no Proof/Lib", it belongs in Perennial (propose it
  there) or `Spec/errors`; until then, take it from `apply.Base`.
- Also check that the tree's `S` covers `mvcc.ErrCompacted` as a pointer target, which
  `errors.Is.spec` requires. `apply`'s dispatch already does this for the same target
  (`DispatchKVL.lean:287`).

**F2.2 (requirement: sufficiency, the server's glue).** `revGetterOk` demands
`□ {{ True }} rg.Rev() {{ v, revLb γi v }}`, a resource-free persistent triple.
- `srv.kv` is a `*watchableStore`; its promoted `Rev` is `store.Rev`, whose spec needs exclusive
  `storeReaderC` slots (a non-atomic `RLock`, so they cannot sit in an invariant across the call).
- The server cannot meet the contract as stated.
- **Restate:**
  `revGetterOk γi rg Rg := ∃ ri, ⌜rg = ok ri⌝ ∗ □ {{ Rg }} Rev() {{ v, Rg ∗ ⌜1 ≤ sint.Z v⌝ ∗ revLb γi v }}`,
  with `Rg` given to `Run` alongside `R` (or a single `R` covering both, carried in `CompactEnv`).
- *Uncertain:* whether the reader slot and `γi` survive a snapshot restore. `watchableStore.Restore`
  re-issues reader tokens at `γ.st.withPhys p'`, and the D22 epochs re-key the backend. If they do
  not survive, `Rg` must be a resource the server re-validates (an invariant-backed handle).

**F2.3 (requirement: sufficiency for C1's `0 < r` in periodic mode).**
- `revLb γi v` is `∃ log, idxCert ∗ ⌜v ≤ |log| - 1⌝`. It holds for any `v ≤ 0`, so `revGetterOk`
  allows `Rev()` to return `-5`, or `0` after a positive sample.
- `Periodic.Run` excludes `0` only as `rev == lastRevision` with `lastRevision` initially `0`
  (`periodic.go:127`). A sample `-5`, or `0` after a success at `7`, would be compacted.
  `perPermit`'s `0 < r` is then unprovable. (Revision mode tests `rev <= 0` explicitly,
  `revision.go:82`, so it is fine.)
- **Restate:** the post includes `⌜1 ≤ sint.Z v⌝`. The real store meets it: it starts at revision
  1, the log certified from `[[],[]] ++ …`, length ≥ 2. `store.Rev.spec` gives `v = |log| - 1` with
  `log₀ <+: log`, so the server proves it from a certificate of length ≥ 2.
- Alternatively, give monotonicity (`v ≥` the previous result), which the C1 draft also lists
  ("revisions never decrease") and the permits dropped.

**F2.4 (preference: coupling / implementation independence).**
- `revLb` unfolds to `mvcc.idxCert`/`mvcc.IdxNames`/`mvcc.Log`, so v3compactor imports
  `mvcc.InvIndex` and its API changes whenever mvcc's certificate does.
- The compactor uses `revLb` only abstractly: persistent, downward closed in `r`, produced by `Rev`.
- **Restate:** make `Lb : Int → IProp GF` a field of `CompactEnv`, with the laws persistent and
  `Lb n ⊢ Lb m` for `m ≤ n`. `NewServer` instantiates it with mvcc's `revLb`, and
  `EtcdServer.Compact`'s pre names mvcc's directly.

---

## 3. The clock: `Proof/github_com/jonboulle/clockwork/Defs.lean` and the periodic permit

**Truth (the trust boundary).** I find no axiom false of clockwork v0.5.0's real clock.
- `NewRealClock` returns `&realClock{}`; `After` is `time.After`; `Now` is `time.Now`
  (`clockwork.go:27-43`).
- Go's timer records `when = nanotime() + d`, read inside the call, so the reading is at least
  every earlier reading. It fires only at `nanotime() ≥ when` (an overflowing `when` saturates, so
  it never fires: consistent with an unbounded `T + d`).
- The channel is never closed and carries values only after firing, which matches
  `isChanBag … (fun _ => clockLb (T+d))`. A bag lets anyone holding `clockLb (T+d)` send, which is
  harmless.
- `stampAt` needs `□ P` held at the call, and is persistent with `stampAt_elim` only for persistent
  `P`.
- **Consistency:** a model exists (`clockLb := True`, `stampAt γ P T := <pers> P`) satisfying every
  axiom, so they cannot prove `False`. A stamp of something not held is not derivable.
- Hence, also: **the axioms say nothing about time at all.** In that model every time bound holds
  trivially, so the time content of C1 lives only in the docstrings' reading of `clockLb`/`stampAt`.
  That is acceptable for a trust boundary, but it should be said in the docstring: the clock part
  of C1 is meaningful only under the intended reading, and no Lean result can consume it.

**F3.1 (requirement: sufficiency, `Periodic.Run`'s proof of the full-window permit).**
`clockOk`'s `After` does not relate its reading `T` to what is already known.
- The intended semantics needs "the reading at the call is ≥ every `clockLb n` held".
- The full-window bound needs a chain:
  - `After_j`'s channel gives `clockLb (T_j + retry)`;
  - then `T_{j+1} ≥ T_j + retry` is needed, which nothing gives (the model above takes `T` arbitrary);
  - so `clockLb (T_first + K)` cannot be derived.
- **Restate** (true of the real clock):
  `∀ d P n, □ P -∗ clockLb n -∗ {{True}} After(d) {{ ch γ, ∃ T, ⌜n ≤ T⌝ ∗ stampAt γc (□P) T ∗ isChanBag γ ch (fun _ => clockLb (T + d)) }}`.
  Or a separate law that the stamp's `T` dominates the lower bounds the caller held.

**F3.2 (requirement: C1/C3 sufficiency; the permit is vacuous).**
`perPermit γi K r = 0 < r ∗ ((∃ T, stampAt (revLb r) T ∗ clockLb (T+K)) ∨ revLb γi r)` (`Defs.lean:119`).
- Every sample comes from `Rev()`, which gives `revLb r` persistently, so `Run` can always take the
  second disjunct. As stated, the permit is equivalent to `0 < r ∗ revLb r`.
- The first disjunct is never needed. Combined with F3.1 it cannot be proved anyway, so the
  "C1 periodic" statement guarantees nothing about time. C3 ("σ.compacted ≤ the revision C1
  allows") would inherit that.
- The honest bounds, from the code:
  - The window's oldest sample `revs[0] = s_{max(1, k-ret+1)}` at iteration `k`, and `min(k, ret)`
    `After`s of `retry` have fired since it was taken (each `After_j` follows sample `j`).
  - A compaction at the run's first sample `s_1` (window not yet full) therefore has age at least
    `retry`, not merely `revLb`. The author's scheduling-delay observation holds: age ≥ `retry`, not
    ≥ `period`.
- **Restate:**
  `perPermit γi period r := 0 < r ∗ ∃ T, stampAt (revLb γi r) T ∗ (clockLb (T + period) ∨ clockLb (T + retryOf period))`,
  which simplifies to `… ∗ clockLb (T + retryOf period)` unless the first case is marked.
- If C3 wants "≥ period except for the run's first sample", the exception needs a name: a
  persistent ghost `firstSample γrun r` the run allocates. A bare `revLb` disjunct does not express
  it.
- If the time content cannot be consumed by any Lean result (see "Truth" above), consider dropping
  it from `compactableOk`'s `P` (the server needs only `revLb`) and exporting C1-periodic as a
  separate stated property of `Run`. Fewer names would cross into the server (abstraction,
  coupling).

**F3.3 (preference: post stronger and simpler).** `periodK = (retentions - 1) · retry`
(`Defs.lean:64`) is one `retry` short.
- At iteration `k ≥ ret` the oldest sample is `s_{k-ret+1}`, and `ret` `After`s (not `ret - 1`)
  have fired since it.
- `ret · retry = (⌊period/retry⌋ + 1) · retry > period`, so with F3.1 `Run` can prove
  `clockLb (T + period)`. That is the documented guarantee ("`pc.revs[0]` is always the rev at
  `pc.period` ago", `periodic.go:112`).
- **Restate:** use `period` itself and drop `periodK` and `retentionsOf` from the exported
  statement (fewer helpers, implementation independent). `retryOf` stays only if the first-sample
  bound is kept.

**F3.4 (requirement: no unneeded premise, mild).** `⌜0 ≤ sint.Z d⌝` in `After` (`clock Defs.lean:82`).
- `time.After` accepts a negative `d` (it fires at once). The premise is what forces
  `New.spec`'s `10 ≤ ret`, which is stronger than the code's `ret ≤ -10 ∨ 10 ≤ ret` (the issue's
  statement, which `New` does not panic on).
- It excludes `"-1h"` periodic configurations, which etcd accepts today (#22396 would reject them).
- **Restate:** no premise on `d`, and `clockLb (T + max d 0)`.
- If `New`'s premise is then relaxed, `retryOf`/`retentionsOf` must use Go's truncating division
  (`Int.tdiv`): Lean's `/` on `Int` differs for negative periods. With today's `10 ≤ period`
  they agree.

**F3.5 (preference: implementation independence).** `isPeriodic`/`isRevision` and `perPermit`
hard-code `clockwork.realClock`. `newPeriodic`/`newRevision` take any clock (etcd's tests pass fake
clocks). Parameterize the internal predicates by `γc`, and have `New` instantiate `realClock`.

---

## 4. `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3compactor/New.lean`

**Good, keep:**
- The post `∃ RunTok, compactorOk cp RunTok E.R ∗ RunTok` hides both objects and their fields
  behind an existential token: abstract, implementation independent, and faithful (Run once,
  Pause/Resume/Stop shared).
- The error disjunct is exactly the code's (an unknown mode).
- `modePermit` selecting C1 by mode matches `New`'s switch (`compactor.go:63-71`), including
  `int64(retention)` for revision mode.
- Nil `lg` is accepted.

**F4.1 (requirement: no unneeded premise).** `mode = periodic → 10 ≤ ret`: see F3.4. The code needs
only `ret ≤ -10 ∨ 10 ≤ ret`. The extra strength comes from `clockOk`, and it excludes configurations
`NewServer` must accept if C2 is really "for any accepted retention".

**F4.2 (requirement, inherited).** `New.spec` is the place the server meets F2.2 (`revGetterOk`
needs a resource) and F1.3 (revision mode with a negative retention cannot reach `Compact`'s
`revLb` pre). Fix them in `Defs`/`Compact`; `New` then only grows a resource field.

**F4.3 (preference: coupling).** `CompactEnv.γi : mvcc.IdxNames` (F2.4).

**F4.4 (preference, naming; affects the server's reading).** `v3compactor.compactorOk cp RunTok R`
and the server's `compactorOk c` (`InvRun.lean:273`: nil, or Pause/Resume) share a name in sibling
namespaces.
- The server's contract is the right minimal view.
- Add the lemma `v3compactor.compactorOk cp T R ⊢ etcdserver.compactorOk cp` next to the server's
  definition, and rename the server's to `srvCompactorOk` to avoid confusion.
- The server's `Cleanup` (`server.go:959`, `Stop`) is not verified today. `compactorOk`'s `Stop`
  is already sufficient for it.

**F4.5 (preference, note).** `R` is kept by the goroutine forever, even after `Stop` (which does not
wait). If `E.RD` is a counted pool (`AuthSrv.lean:80`, `replicate actualMaxReaders RD`), the server
loses one slot for good. That is fine, but the glue should state it. *Uncertain:* whether shutdown
proofs need all slots back.

---

## 5. `Spec/github_com/jonboulle/clockwork/NewRealClock.lean`

**Good:** small, and true (`&realClock{}`, methods as above). The trust lives in `clockOk`, where it
can be reviewed in one place.

There are no findings of its own: F3.1 and F3.4 change `clockOk`, and this spec follows. Its
docstring should state the vacuity remark from section 3, "Truth".

---

## 6. The rest of the exported vocabulary (`Defs.lean`)

- **`compactorOk`** (`:201`): persistent, with `Run` consuming a token and the server's `R`.
  Pause/Resume/Stop are `{{True}}`, which is faithful to their concurrent use from the raft ready
  handler (`server.go:762-785`) and to `Stop` from `Cleanup`. Good.
- **`revPermit`** (`:114`): true, provable, and meaningful.
  - The overflow case of `Rev() - retention` wraps to a negative and is skipped by `rev <= 0`
    (`revision.go:82`): `v ∈ [0, 2^63)`, and `v - ret ≥ 2^63` wraps below 0. So `r + ret = v` when
    the call is made.
  - Its only problem is the interaction with `Compact`'s `revLb r` at `ret < 0` (F1.3).
- **`compactReqIs`** (`:94`): exactly what the compactor builds (`&pb.CompactionRequest{Revision: rev}`,
  Physical false), owned and handed over. Good.
- **`revLb`** (`:76`): the right shape, but couple it via `CompactEnv` (F2.4) and pair it with
  `1 ≤ v` (F2.3).
- **`modePermit`**: fine.
- **`CompactEnv`**: fine. It should grow `Lb` and the getter's resource (F2.2, F2.4).
- Internal (`isPeriodic`/`isRevision`): only F3.5 affects the exported specs.

## Summary of proposed restatements (by priority)

1. `compactableOk` post: the pair shape, `R` back, and `err = nil ∨ errTreeOk err` (F2.1).
   `EtcdServer.Compact` post gives the same, plus the header and response facts the gRPC
   `compactOk` needs (F1.1, F1.2).
2. `revGetterOk` with a resource `Rg` and `1 ≤ v` (F2.2, F2.3). `Compact`'s pre with the kv reader
   resource (F1.5).
3. `Compact`'s `revLb r` replaced by a server-chosen permit, or dropped (F1.3). `Compact.specM on`
   (F1.4).
4. `clockOk.After`: the reading `T` dominates the caller's `clockLb`, and no `0 ≤ d` (F3.1, F3.4).
   `perPermit` with `period` for a full window and `retryOf period` for the first sample, or the
   time part moved out of `compactableOk`'s `P` into a separate C1 statement (F3.2, F3.3).
5. Relax `New`'s premise to `ret ≤ -10 ∨ 10 ≤ ret` once F3.4 is done (F4.1). Decouple from mvcc
   (F2.4). Add the server-view lemma and rename it (F4.4).
