# mvccfull Probe: the writer's restart and restore chains (2026-11-09)

The Probe of stage F1 (`notes/mvccfull-proof-plan.md`) on the writer's riskiest bodies: `runner.restart`
(the incarnation swap) and `runner.restore` (the builder to `Restore` handoff). What was proved, what
changed and why, what is left.

## Proved

- `runner.restart` (both members, `runner__restart.lean`), over the specs of `stopReaders`,
  `endEpoch`, `shut`, `open`, `startEpoch`, `startReaders` and the laws below. The shares lent to the
  readers and streams are gathered back (`WriterShares.lean`: `shares_join`, from `lentOk`), the
  incarnation retired (`inc_retire`), its contents split (`memberState_split`), the writer's halves
  agreeing with the invariant's (so the closed state is `σOf ks ops v.ops` and the bounds `v.b`), and
  after `open` the same shares lent again at the new incarnation (`shares_split`), so `writerOwn`'s
  `q`, `qs` are unchanged and the other member's parts untouched.
- `Writer.lean`'s laws: `memberState_split`, `inc_retire`, `inc_census`, `inc_stop_image`, `inc_alloc`.
- `RestoreLemmas.lean`: `restore_au`, `Restore`'s update at the follower's incarnation invariant
  (the follower's readers and streams run throughout: the writer's live share opens the invariant,
  its halves pin the state and the bounds, the counters grow along the log prefix).
- `WriterShares.lean` (pure): `runM_hs_len`, `runM_hs_prefix`, `revAfter_mono` (so the restart needs
  none of the `sorry`'d `runM_mono`/`logOk_hist`).

## Changes (what, why, which statements)

1. **`Writer.lean` prefers `History.lean`'s `Pos.Countable` instances of `MvccState` and `Change`**
   (`attribute [local instance high]`). `Writer.lean` imports mvccrand's writer stack, which declares
   its own (equal bodies, distinct constants); `incW`/`memberCarry`'s ghost variables were elaborated
   with mvccrand's, `memberState`'s (Members.lean) with History's, so `ghostVar_agree`/`icombine` of
   the writer's half against the invariant's failed (they only matched up to unfolding). No statement's
   meaning changes; `incW`, `memberCarry`, `lessorW`, ... are re-elaborated (importers rebuilt; all of
   `runner__*` built). Better still: mvccrand's duplicates should go (a shared module of the two
   testers' instances).
2. **`lessorW` holds `lessorApplyOk lp`** (NewLessor's contract of the lessor on *any* backend), besides
   the contract on its current backend. `lessor.Recover` (in `restore`) moves the lessor to the
   snapshot's backend and gives no contract for it; `lessorW` for the follower after the restore needs
   `lessorBackend` at the new backend, which only `lessorApplyOk` (in `NewLessor.specR`'s post, so
   `open` has it) provides. Statements changed: `lessorW` (so `memCore`, `memW`, `writerOwn`), additive.
3. **`runner.restore.spec` takes `ops.length ≤ Ops` and `Ops < 2 ^ 38`** (both `write`'s premises,
   which calls it): the builder's file `buildPath (nb + 1)` is among `writerOwn`'s unused files only
   if `nb + 1 ≤ Ops`, the builder's grants have write-back tokens (`Ops ≤ k + b.ops`) only while
   `b.ops < ops.length ≤ Ops`, and the snapshot's backend's kept tokens (`Ops + 1`, for the follower's
   later grants and `SetTxPostLockInsideApplyHook`) fit in `wbInit` only for a bounded `Ops`.
4. **`[ReceiptBoundLe GF (2 ^ 38)]`, not `2 ^ 48`, in `open`, `newMember`, `restart`, `restore`,
   `write`.** `inc_open_backend`'s premise `receiptBound GF + k + 4 ≤ backend.wbInit` (`wbInit =
   2 ^ 40 - 1`, `k ≥ Ops`) cannot be met from `receiptBound ≤ 2 ^ 48`: `open` and `restore` were
   unprovable. `Run` has `2 ^ 38` (as mvccrand's); `New.specR`'s `2 ^ 48` follows
   (`ReceiptBoundLe.pow_succ`).
5. `etc/link-lean-first-mvccfull.txt`: `runner__restore` takes `mvccClosed_rest.law` (for
   `inc_open_backend`); `Link.lean` regenerated.

## `runner.restore`: where the proof is (`runner__restore.lean`, one `sorry` left)

Proved, in Go's order: `builds++`; `buildPath`; `newMember(2, …)` on the first unused builder file
(the history's lower bound `hist0`); the loop `for b.ops < l.ops { apply(b, log[b.ops], false) }`
(the log's slice and its persistent `opIs`, `leadPre false` from the leader's lower bound, the
builder's write-back tokens from `Ops ≤ k + b.ops`); the builder retired (`inc_retire`, its whole
token: no reader or stream ever had a share) and `shut`, its file the image of `σOf ks ops l.ops`
(`inc_stop_image` inside `shut`) with the live leases' records; the follower's `revHi`, `cmpHi`
raised to the builder's inside its incarnation (`bnd_acc`: the bounds hold at the follower's state,
`revAfter_mono`, `cmpAfter_mono`); `openBackend` on the builder's file at a fresh registration;
`inc_open_backend` at the image.

Left (the `sorry`), with what each step needs, all checked against the statements:

- `kv := f.kv`; `f.le.Recover(newbe, func…)`. `Recover`'s premises: the records are the builder's
  (`leaseRecsOk (rbData P D) (leasesAfter l.ops)`, through `rbPart` of the new backend); `mono = false`
  (`lessorRevocable`); `id ∈ U → id ∈ L` from `logOk_recover` (`v1.U ⊆ grantedAfter v1.ops`, in
  `memCore`); `reqOf := 3600`; the `leaseReqIs`-or-fresh list from `lessorW`'s `□ [∗list] U`
  (a list-membership split); `leaseGranted γl id` from the guard `True` (**unfolds `lease.leaseGranted`:
  a missing law of lease, `leaseGranted_of_guard`**); the new backend's `isBackend` (`bkKeep`), an open
  share (`bkKeep`'s half, lent), two write-back tokens (`inc_open_backend`'s). With `Lr := L`
  (`leaseRecsOk`'s `recs.map (·.1) = L`), `leaseOwn γl L ∅` comes back, which `Restore` takes.
  The closure's `mvccDeleter` (the `kv` cell persisted; `KV.Write`'s contract; the
  `TxnWrite → TxnDelete` conversion) is a lemma to write.
- `f.kv.Restore(newbe)`: `KV.Restore.contract` (through `shapes.law`), at `σ' := σOf ks ops l.ops`
  (`MvccReachable` from `logOk_hist`, pure, `sorry`'d; items from `logOk_leases`, pure, `sorry`'d), the
  storage from `inc_open_backend`, the hook share `plHook γB nil` (`f = nil`), the update
  **`restore_au` (proved)**. Post: the new backend's share, the old storage's rest, the leases'
  items.
- `SetTxPostLockInsideApplyHook(f.hook)`: `plHook γB nil` to `f.hook`, then `plHook_persist` gives
  `hookIs` (**unfolds `backend.plHook`/`plHookRO` against `storageHook`'s `etcdStorage_hookIs`, a
  definitional equation of mvcc's API: fine**); a write-back token from the new `bkKeep`'s `k`.
- the old backend's census (`bkCensus` of the old `bkKeep` with `Restore`'s `storageRest`) and
  `backend.Close`; the fields; `revLo`/`cmpLo` stores (`bnd_acc` again: `revLo := σ'.rev`,
  `cmpLo := σ'.crev`, which hold after `Restore`); the checks (`KV.Rev`, `KV.Read`, `FirstRev`,
  `End`); `checkLeases`; the counter; `writerOwn` at `nb + 1` (the follower's `lessorW` on the new
  backend from `lessorApplyOk`, change 2, with `plHookRO γB f`).

No step found a false statement beyond changes 2-4; the risky ones (the builder's image, the
bounds' window, `Restore`'s update at a live incarnation) are proved.

## Laws still `sorry` (Writer.lean) and why

- `inc_open_backend`: `mvccrand.rc_open`'s proof at an image (`etcdStorage_open.law` in place of
  `mvccImage_fresh.law`) and `bkCensus` in place of `rcCensus`: mechanical, no invariant risk.
- the pure model lemmas `logOk_once`, `logOk_hist`, `runM_mono`, `logOk_leases`, `logOk_recover`
  (no invariant risk; `runM_mono`'s parts are now `revAfter_mono`, `cmpAfter_mono`,
  `runM_hs_prefix`, proved in `WriterShares.lean`).

## Unfolds of other packages' definitions (each a missing law of that package)

- `apply.bkRT` (etcdserver's apply package) in `inc_census`: its open share `bOpen rdOpen`
  (`bkRT_open : bkRT B ⊢ bOpen B.γB rdOpen ∗ …`).
- `backend.bStopView` (backend's `InvStop`) in `inc_stop_image`: its `rbOwn (rbData P D)`, against
  the writer's `rbPart` (`bStopView_rbPart_agree`).
- `backend.rbOwn` (an abbreviation of `rbPart γ ⊤`) with `backend.rbPart_agree` (a backend lemma,
  used as is).

## Round 2 (2026-11-09, 23:06–23:55 UTC, about 50 minutes): `runner.restore` finished

**`runner.restore` is proved** (no `sorry` in `runner__restore.lean`; `lake build ...mvccfull.Link`
passes). After `inc_open_backend`, in Go's order:

- `lessor.Recover(newbe, closure)`: the closure's `mvccDeleter` proved inline (the captured `kv` cell
  persisted; `KV.Write`'s contract through `shapes.law`; the `TxnWrite → TxnDelete` conversion is a
  pure step); `Recover`'s premises from the builder's records (`leaseRecsOk`, `Lr := L'` exactly),
  `logOk_recover`, the guard `True` (`granted_list`), the `U`-or-fresh request list
  (`bigSepL_mem_or`), the new backend's `isBackend`, half of its open token (lent), two write-back
  tokens. `leaseEver` is split on `recs = []` around the call.
- `KV.Restore` through `restore_au` (proved last round): `MvccReachable` (`logOk_hist`), the items
  (`logOk_leases`), the hook share `plHook γB nil`, `storageReq` of `True` (`commitReq_true`); the
  bounds `b2` hold at the builder's state.
- `SetTxPostLockInsideApplyHook(f.hook)` (one of the kept tokens), the hook frozen (`plHook_persist`).
- The old backend's census (`bkCensus` with `Restore`'s `storageRest` and the old `bkRT`'s share),
  `backend.Close` at `dbCloseOk`.
- The fields; `append(nil, b.leases...)`; `revLo`/`cmpLo` stored at the restored state (`bnd_acc`).
- The checks: `KV.Rev`, `KV.Read`/`Txn.FirstRev`/`Txn.End` (`read_au`, new: a read's update at a live
  incarnation).
- The follower's `memCore` rebuilt on the new backend: `lessorW` with `lessorBackend` derived from
  `lessorApplyOk` (change 2), `U' = U ++ recs` (or `U`), `grantedAfter_mono`, `leaseRecsOk_insert`;
  `bkKeep` with `Ops` tokens; `checkLeases`; `restores.Add`; `writerOwn` at `nb + 1`.

New lemmas: `RestoreLemmas.lean` `read_au`, `bigSepL_mem_or`, `granted_list`; `WriterShares.lean`
`grantedAfter_mono`, `leaseRecsOk_insert`. Hypothesis added: `restore.wp_proof` takes
`mvccReaders_split.law` (`etc/link-lean-first-mvccfull.txt`, `Link.lean` regenerated).

**`inc_open_backend` is proved** too (`Writer.lean`): `mvccrand.rc_open` at an image, `bkCensus` in
place of `rcCensus`, `wbStock` (a copy of mvccrand's `rcStock`, whose statement carries mvccrand's
package assumptions as a section variable: a cleanup for mvccrand). Note: a census over
`List.replicate rdStockN` must keep `rdStockN` abstract (`n2 + 2`): rewriting with
`List.replicate_succ'` at the literal makes the kernel recurse.

No new spec or invariant problem in this round. Every law of the restart and restore chains is now
proved; what remains `sorry` in `Writer.lean` is the five pure model lemmas (`logOk_once`,
`logOk_hist`, `runM_mono`, `logOk_leases`, `logOk_recover`), and in the shared modules
`memberN_mask`, `memberInv_live`, `rdStock_split` (`Readers.lean`), plus the bodies of `shut`, `open`
and the others not in the Probe.

## The unfolds of other packages' definitions, and the law that would replace each

| Unfolded (owner) | Where | Law to add (statement) |
|---|---|---|
| `apply.bkRT` (`Proof/go_etcd_io/etcd/server/v3/etcdserver/apply/Contracts.lean`) | `inc_census`, `inc_open_backend`, `restore` (old backend's census) | `apply.bkRT_eq (B) : apply.bkRT B ⊣⊢ backend.rdTok B.γB B.P B.be ∗ backend.bOpen B.γB backend.rdOpen` |
| `backend.bStopView` (`Proof/go_etcd_io/etcd/server/v3/storage/backend/InvStop.lean`) | `inc_stop_image` | `backend.bStopView_rbPart_agree (γ P W Pk D S r) : bStopView γ P W Pk D ∗ rbPart γ S r ⊢ bStopView γ P W Pk D ∗ rbPart γ S r ∗ ⌜∀ n, S n → r.lookup n = (rbData P D).lookup n⌝` |
| `backend.rbOwn` (`InvBackend.lean`; with `rbPart_agree`) | `inc_stop_image` | subsumed by the line above |
| `lease.leaseGranted` (`Proof/go_etcd_io/etcd/server/v3/lease/InvLessor.lean`) | `granted_list` | `lease.leaseGranted_of_guard (γl GA id) : lessorGuard γl GA ∗ □ GA id ⊢ leaseGranted γl id` |
| `lessorApplyOk` (`Proof/go_etcd_io/etcd/server/v3/etcdserver/SnapRO.lean`) | `restore` (the lessor's contract on the new backend) | `lessorApplyOk_at (lp d W Pk f RW) : lessorApplyOk lp ∗ isBackend d.γB d.P W Pk d.be ∗ plHookRO d.γB f ∗ ⌜f ≠ func.nil⌝ ∗ rwLens RW (lessorBeOn lp d.be) ⊢ lessorBackend lp Pk #f (wbTok d.γB) RW (apply.bkRT d) (rbPart d.γB (· = "lease"))` |
| `rwLens` (`Proof/go_etcd_io/etcd/server/v3/etcdserver/InvRest.lean`) | `restore` | `rwLens_refl (X) : ⊢ rwLens X X` |
| `backend.wbTok` (`InvBackend.lean`) | `inc_open_backend`, `restore` | `backend.wbTok_toks (γ) : wbTok γ ⊣⊢ ownToks γ.wb 1` (or make it an `abbrev`) |
| `backend.newPostK`, `backend.bFresh`, `backend.newPostKP` (`backend`) | `inc_open_backend` (as `mvccrand.rc_open`) | `backend.newPostK_split` stating `newPostK`'s parts as `rc_open` destructs them, and `newPostKP_intro` its converse |
| `api.hookRun` at `nil` (`Spec/go_etcd_io/etcd/server/v3/storage/mvcc/Api.lean`, exported) | `restore` (`Restore`'s premise) | `api.hookRun_nil (P Pre Q) : hookRun P func.nil Pre Q ⊣⊢ (P ∗ Pre ={⊤}=∗ Q)` |
| `mvccDeleter` (`Api.lean`, exported) | `restore` (its persistence, its proof) | `instance mvccDeleter_persistent`; `mvccDeleter_intro` (the `⌜rd ≠ nil⌝` and the triple) |
