# Track LA of the `origin/lean` → `mvcc-api` merge: lease's and auth's specs and proofs (2026-11-06)

All ten conflicted files resolved and staged; no markers left in `{Proof,Spec}/.../server/v3/{lease,auth}/`.
Nothing built (no `lake build`, no `lean-check`).

## Per file

- `Proof/.../lease/LessorBackend.lean` (1 hunk): **lean's** `lessorBackend lp P f T Ln R Rb` (the lent part
  `Ln` lends `le.b`, given back by `Grant`/`Checkpoint`) in place of ours' lens in `R`. Both are lenses
  over the same field and both are sound; lean's is kept because lean's server (`SnapRO.lessorApplyOk`,
  `LessorDerive`, `Results`) is written against it, and it keeps the lent field apart from the open
  share `LockInsideApply` takes. Ours' `leaseBatchTx`/`leaseBackend` (over `srvApi.csContractA` at
  `⌜f = #g⌝`) unchanged. Header and docstring updated (the `Ln` story; `csContractA` in the header).
- `Spec/.../lease/lessor__Grant.lean` (1 hunk): **lean's statement** (`Ln`, `leaseEver γl U`, the mode
  disjunct `lessorModeIs γl true ∨ ⌜id ∉ U⌝`, `leaseLiveFrom`, `leaseReqIs`, post `R ∗ Ln`) **with ours'**
  `f : GoFunc`, `lessorBackend lp P #f …`, `csContractA P f`; ours' `open`s kept, so lean's new names are
  qualified `lease.`. Docstring: lean's, plus a sentence for the strict-M1 contract.
- `Spec/.../lease/lessor__Checkpoint.lean` (1 hunk): same combination (`f : GoFunc`, `#f`, `T Ln R`,
  `srvApi.csContractA`, `Ln` in the pre; the post's `R ∗ Ln` was lean's, auto-merged).
- `Spec/.../lease/lessor__Revoke.lean` (2 hunks): **ours'** statement (API: `mvccDeleter`, `mvccBackend`,
  `hookIs`, `csContractA`, `auBegin`/`auEnd`, `γl := mvccLeases γ`) plus lean's `lease.lessorRevocable γl`
  (lease-grant D2; persistent, so not in the post). Docstring: ours' plus one sentence for D2.
- `Spec/.../lease/NewLessor.lean` (1 docstring hunk): **lean's** (the `Ln` wording). The file is now
  identical to lean's: lean's `mono`/`lessorModeIs`, `leaseEver γl []`, `lessorStopTok` (auto-merged);
  ours never restated `NewLessor` over the API (still `d : mvcc.KBReal`, `lessorApplyOk lp` from the
  server's `SnapRO`), so there was no mvcc restatement to keep.
- `Spec/.../auth/authStore__Recover.lean` (1 hunk): **lean's** (HS-6/R-D2: no write contract at all,
  `authOwnPM`, `γc₀ γc`, `recoverIn/Fit/Out`), so ours' `f : GoFunc` vanishes with it. Kept ours'
  `HeapGS HasLC.hasLC` variable (the proof file, auto-merged, is at `hasLC` too; generic would also do).
- `Proof/.../lease/lessor__Grant.lean` (1 hunk): lean's (`le.b` read through `Ln`); ours' `iunfold
  srvApi.csContractA` lines auto-merged.
- `Proof/.../lease/lessor__Checkpoint.lean` (2 hunks): lean's `Ln` threading with ours' `iunfold
  srvApi.csContractA`.
- `Proof/.../lease/lessor__Revoke.lean` (2 hunks): ours' intro/`wp_start` with lean's `#Hrev` added;
  `hlast'` with lean's third component `T.delete id` over ours' `σ₀.log`. Lean's D2 history step
  (`lessorModeIs_pin`, `hist_append`'s new arguments, `obtain ⟨T, Hlast⟩`) auto-merged.
- `Proof/.../auth/NewAuthStoreOn.lean` (1 hunk): lean's `(γc : AuthBkNames)` with ours' `f : GoFunc`;
  the rest (ours' `csContractA`, `hasLC`; lean's currency) auto-merged.
- Also touched: `Proof/.../lease/RangeDeleter.lean` (not conflicted): a `MERGE-TODO(rdAt)` on `rdAt`.

## MERGE-TODOs

- `RangeDeleter.lean`, `rdAt` (`MERGE-TODO(rdAt)`): `rdAt γl s` is over mvcc internals
  (`isWatchableStore`, `rdIs`), which still exist, so it still compiles. It is to be replaced by the
  API's `∃ rd, lease.rdOwn (mvccLeases γ) rd ∗ mvcc.api.mvccDeleter rd γ` (the API's `New` already
  posts exactly that, `Api.lean:893`), and the module deleted once its users are restated. Not
  deleted now: lean's server files import it.

## Spec changes (client specs, old → new)

- `lease.lessor.Grant.spec`: ours `… (f : GoFunc) (T R) … lessorBackend lp P #f T R Rb ∗ … ∗ T ∗ R ∗ Rb rb
  ∗ leaseGranted γl id` / post `R ∗ (…)` → `… (f : GoFunc) (T Ln R) … (U : List w64), lessorBackend lp P #f T
  Ln R Rb ∗ … ∗ T ∗ Ln ∗ R ∗ Rb rb ∗ leaseGranted γl id ∗ leaseEver γl U ∗ (lessorModeIs γl true ∨ ⌜id ∉
  U⌝)` / post `R ∗ Ln ∗ (… ∗ leaseEver γl U ∨ … ∗ leaseLiveFrom γl 0 id l ∗ … ∗ leaseEver γl (U ++ [id]) ∗
  leaseReqIs γl id ttl)`. (= lean's, with `f : GoFunc`/`#f`/`csContractA`.)
- `lease.lessor.Checkpoint.spec`: ours `(T R)`, `lessorBackend lp P #f T R Rb`, pre `T ∗ R` → `(T Ln R)`,
  `lessorBackend lp P #f T Ln R Rb`, pre `T ∗ Ln ∗ R`, post `R ∗ Ln ∗ …`.
- `lease.lessor.Revoke.spec`: ours' + `lease.lessorRevocable γl` in the pre.
- `lease.lessorBackend`: ours' 6-argument `lp P f T R Rb` (lens in `R`) → lean's 7-argument
  `lp P f T Ln R Rb` (lens in `Ln`).
- `NewLessor.spec`, `lessor.Recover.spec`, `lessor.initAndRecover.spec`, `authStore.Recover.spec`: lean's.

## For the other tracks (what breaks, where)

- **`rdAt` users** (restate to `∃ rd, lease.rdOwn E.γ… rd ∗ mvccDeleter rd E.γ`; their argument `E.s`
  goes): `etcdserver/{AppliedOn:339, ApplyCmpArm:880, AuthCompRows:68,116, BuildLemmas:154,315,
  InvApplier:822-829, InvBuild:272, InvStart:218, M2StorageDraft:121, Results:1003, ServerOn:321,
  SnapApplyAuthM:138, SnapApplyDefs:245, SnapApplyKV:86,115, SnapApplyWalk:608,672-673, StartOn:63}`,
  `etcdserver/apply/{Chain:1643-1664, Contracts:51 (import),353, LessorDerive:171,202,223}`.
- **`lessorBackend` users, now lean's shape**: `etcdserver/SnapRO.lean:142` (already `lp Pk #f (wbTok
  d.γB) RW (apply.bkRT d)`, i.e. `T := wbTok`, `Ln := RW`, `R := bkRT d`: ours' `R := bkRT d ∗ RW` must
  not be re-applied; `isApplyLessor`'s `Grant`/`Checkpoint` give `Ln` back, as on lean),
  `etcdserver/apply/LessorDerive.lean:272` and `Results.lean:1206` (lean's text over `mvcc.storeWT`/
  `storeRT`: restate `T`/`R` to `backend.wbTok`/`apply.bkRT`), and the tester
  `examples/mvccrand/WriterLease.lean:157` (`lessorBackend lp True #f T R …` → put `lessorBeOn` in `Ln`:
  `lessorBackend lp True #f T Ln R …`).
- **`lessor.Grant` callers** now owe `leaseEver γl U ∗ (lessorModeIs γl true ∨ ⌜id ∉ U⌝)` (lean's server
  has it; the tester `examples/mvccrand/writer__grant.lean` does not: it needs `leaseEver` from
  `NewLessor`'s post, and a mode). **`lessor.Revoke` callers** owe `lessorRevocable γl`: lean's apply chain
  carries it beside `rdAt` (`apply/Chain.lean:1643`, `Contracts.lean:353`); the tester's
  `writer__revoke.lean:239` needs it from `NewLessor` at `mono = false`.
- **Snapshot walk (track SN)**: `lessor.Recover.spec` (lean's) takes `rdOwn γl rd0` and gives `rdOwn γl rd`
  for the new closure `rd`; nothing gives `mvccDeleter rd γ` for it. `mvccDeleter` is an exported
  definition (`Api.lean:386`, body visible), so the walk can build it inline from `KV.Write.contract`
  at the KV's dynamic type, `isMvcc kv γ` (persistent by `persistent.law`) and the closure's body (read
  `s.kv`, `traceutil.TODO()`, `kv.Write(trace)`). If an API law is preferred (additive; not added):

  ```
  /-- A closure that calls the store's `Write` on a fresh trace is its deleter. -/
  abbrev mvccDeleter_of_write.law : Prop :=
    ∀ (ty : go.GoType) (v : val) (γ : MvccName) (rd : GoFunc),
      KV.Write.contract (GF := GF) ty v → rd ≠ func.nil →
      pkgInit ∗ isMvcc (interface.mkOk ty v) γ ∗
      □ (∀ Φ, (∀ (trace : Loc) (te : Bool), ⌜trace ≠ null⌝ -∗ traceutil.ownTrace trace te -∗
            WP (App (Val #(methods ty go!"Write" v)) (Val #trace)) {{ Φ }}) -∗
          WP (App (Val #rd) (Val #())) {{ Φ }})
      ⊢ mvccDeleter rd γ
  ```
  (provable from `KV.Write.contract` by framing; no change to the API's other statements).

## API weaknesses

None found: everything the lessor needs of mvcc (`Revoke`) is in the API; the deleter after `Restore`
is buildable from the exported `mvccDeleter` body, the law above only a convenience.
