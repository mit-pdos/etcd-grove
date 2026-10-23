# Plan: duplicated and near-duplicated lemmas in the examples, the client and the cache

Status: audit done (2026-10-22, on `lean` `790c961cc8`); steps applied on branch `dedup`
(2026-10-22), see "Progress" below. Follows the clean-ups of 2026-10-21/22 (`notes/decisions.md`
D34-D36; `notes/STATUS.md`, "Clean-up: unused declarations removed, ...", "Clean-up: the watch
client's joins, ..."). The dead-declaration pass (`etc/dead-decls.py`) is **not** part of this
audit (section "Pending" below).

## Progress (branch `dedup`, 2026-10-22)

- **A, done.** Every exact duplicate merged into the file its users import: `isProgressNotify_events`
  in `cache/v3/InvStore.lean` (next to `RespModel`); `optsAt_nil` in `client/v3/InvOp.lean`;
  `deleteOp_txnOpOf` in `cache/v3/InvEtcdTxn.lean`; `readsAt_insert` in `concurrency/InvSTM.lean`;
  `cmpSetAt_cmpAt`, `cmpsSetAt_cmpsAt` in `leasing/InvLeaseEval.lean`; `validSortTarget_of_rangeCheck`
  in `v3rpc/CheckShape.lean`; `ptsto_w64_halves` gone for `ptsto_split_half`. `kvClientN_mask` and
  linkvtxn's masks wait for C4's Perennial lemma.
- **B, done.** `PutThenGet.lean`'s `client_put_own`, `client_get_own`, `putGetInv_alloc` inlined into
  their only users, `ClientPutGet.lean`'s `client_Put_own`, `client_Get_own`, `putGetInv_alloc_log`.
- **C7, done.** One proof, generic in the model: `watchkv/WatchFacts.lean`'s `chain_gen`,
  `prog_step_gen`, `resp_gen` over `wkSteps EM P R` (the model's steps are of watchkv logs whose puts
  give `R`); `wkSteps_srv` (from `wk_log`) and linkv3p's `wkSteps_hist` (from `hist_wk`) instantiate
  it, `resp_wk` and `resp_hist` are three-line corollaries. `chain_wk`, `prog_step_wk`, `chain_hist`,
  `prog_step_hist` gone. `cachekv`'s variant not attempted (as planned).
- **C5 (i), done.** The `op_simps` simp set (`client/v3/OpSimpAttr.lean`, tagged in `InvOp.lean` and,
  for `txnOpOf`, `cache/v3/InvEtcdTxn.lean`); the 130 simp lists that named the option models now
  say `op_simps`. **(ii), (iii) not applied:** the seven `*Txn_under` proofs differ in what each
  operation's `Under` needs (a key's prefix, `keyOp`'s or `opDeleteModel`'s fields, `ownerOp_under`),
  so a generic lemma saves little over the `refine`; the comparison pair needs a target-indexed field
  and positivity premise; the `MyKey` pairs need their (different) struct types abstracted. With
  `op_simps` the `_rev`/`_txnOpOf` pairs are one-line `simp`s each.
- **C8, checked, left.** `resOfL` and `kvsOfL` are not maps of each other: they read different
  fields of the generated `Output` struct; only their four length lemmas share a proof, and merging
  them would move the work to the call sites.
- **C1-C4, D, done** (branch `dedup-pin`). Perennial's `dedup-lemmas` landed (`f97c83add`, the pin
  since; `notes/perennial-changes.md`): C1's `typedPointsto_half_split`/`_half_combine`/
  `_half_fractional`, C2's `set_length_append_replicate(_pos)`, C3's `foldl_apply_take_succ`, C4's
  `mask_ndot_ne2`, D's list and `GoStringLt` lemmas. The local copies are deleted and their uses
  point at Perennial's; `opFold_take_succ`, `stmOptsFold_take_succ`, `cfgApply_take_succ` stay as
  one-liners (their folds are in specs' statements), as do `crl_set_repl'` and
  `set_append_replicate` (the `M - k` forms) and the `*_mask` names (one-liners now). Two more
  copies found on the way: raft's `ptsto_halves` (deleted) and the server's `mask_ndot_ne2` at
  `nroot` (a one-liner now); raft's `getElem?_snoc_cases` is a stronger statement and stays (the
  client names Perennial's explicitly). Found already upstream, and used now: `flatten_length` is
  Perennial's `join_same_len_length`, `prefix_snoc_cases` Lean's `List.prefix_concat_iff`,
  leasing's `Qp_half_add` Perennial's.
- **C6, E: not started**, each waiting on the decision the plan names (Perennial's `tokJoin` with owed
  tokens; where the kv model lives; common's parameters).

## Goal

No lemma proved twice, and no lemma in a file its users cannot import, across
`Proof/github_com/mit_pdos/etcd_grove/examples/`, `Proof/go_etcd_io/etcd/client/v3/` (with
`concurrency`, `leasing`, `experimental/recipes`) and `Proof/go_etcd_io/etcd/cache/v3/`, without
changing any result's statement (every `Results.lean` header byte-identical, the fingerprint of the
closed theorems unchanged) and without adding to the trust base (`etc/tcb-report.py --check`).
Facts about Perennial's or Lean's own definitions go to Perennial (CLAUDE.md, "Changes to
Perennial"; `notes/decisions.md`, "Proof/Lib: facts that belong to no Go package").

## How the findings were made

A script extracted every `theorem`/`lemma` statement under the roots above (7,078 declarations) and
compared them (a) textually identical up to binder names, (b) by `difflib` ratio ≥ 0.88, excluding
`Link.lean`, `Results.lean`, `*Linked.lean`, `Adequacy*.lean`, `PkgTable.lean`, `Init.lean` and the
`X.spec (GF := GF)` restatements; then each hit was read. A separate pass listed the pure lemmas
(no `IProp`, `⊢`, `∗`, `WP`) and the generic ones among them (no project noun). The witness part
was compared file by file (`diff` after renaming `RaftWitness.`/`kvwitness` to `kv`). The Go of
`examples/linkv3p` was diffed against `examples/common`.

## Findings

### A. Exact duplicates (identical statements; delete one, import the other)

| Lemma | Copies | Fix |
|---|---|---|
| `isProgressNotify_events` (`cache/v3/Cache__watchEvents.lean:61`) | `isProgressNotify_events'` (`examples/common/WatchBase.lean:130`; exported by `watchkv/WatchFacts.lean`, used by `linkv3p/WatchHist.lean`) | The lemma is about `RespModel` (`cache/v3/InvStore.lean:255`): move it to `InvStore.lean`, delete the primed copy and the `export` |
| `optsAt_nil` (`client/v3/concurrency/InvMutexLemmas.lean:384`) | `examples/linkvtxn/Client.lean:89` (linkvtxn does not import `concurrency`) | Move next to `optsAt` (`client/v3/InvOp.lean:379`), delete both |
| `kvClientN_mask` (`client/v3/InvServerKV.lean:240`) | `linkvN_mask`, `linkvInvN_mask` (`examples/linkvtxn/Inv.lean:309,315`): the same statement, so `linkvN` is `kvClientN`'s mask; see also D below | Prove from one Perennial lemma (D) |
| `ptsto_w64_halves` (`client/v3/WatchRecon.lean:78`) | `ptsto_split_half` (`client/v3/WatchRun.lean:499`) | Part of family C1 |
| `readsAt_insert` (`client/v3/concurrency/InvSTMMaps.lean:143`) | `readsAt_insert_rd` (`concurrency/InvSTMReads.lean:348`) | Delete one |
| `deleteOp_txnOpOf` (`client/v3/concurrency/Election__Resign.lean:27`) | `stm_deleteOp_txnOpOf` (`concurrency/InvSTMMaps.lean:21`) | Delete one; part of family C5 |
| `cmpsSetAt_cmpsAt` (`client/v3/leasing/InvLeasingTxnLemmas.lean:154`) | `cmpsSetAt_cmpsAt_c` (`leasing/InvLeasingCommitLemmas.lean:388`) | Delete one |
| `validSortTarget_of_rangeCheck` (`v3rpc/ServerKV.lean:425`) | primed copy (`v3rpc/CheckShape.lean:37`) | Server side, adjacent: delete one |

### B. Two put-then-get layers (`client/v3`)

`PutThenGet.lean`'s `client_put_own`/`client_get_own` (lines 208, 251) are used only by
`ClientPutGet.lean`'s `client_Put_own`/`client_Get_own` (lines 71, 99), which the examples use
(putget, putget3); likewise `putGetInv_alloc` (`PutThenGet.lean:97`) only by `putGetInv_alloc_log`
(`ClientPutGet.lean:64`). Fold each pair into one lemma (keep the capitalized names, the ones the
examples use). `putGetOk`, `kvOpStep_putKey`, `putAu_of_putGetInv`, `getAu_of_putGetInv` are
internal to `PutThenGet.lean` and stay. `kv_get_server` and `kv_get_server_r`
(`ServerKVGet.lean:256,465`) differ in their update premise (`kvRangeAu` vs `kvAnyAu`) and both are
used: keep.

### C. Families that are one lemma in disguise

- **C1. Points-to halves** (12 lemmas; Perennial has only `typedPointsto_frac_add`,
  `Golang/Theory/PostLifting.lean:201`): split `typedPointsto l v (own 1)` into two `half`s, or
  `own q` into two `q.half`s, or join two halves with agreement, specialised by value type
  (`w64`, `Loc`, `GoChan`): `ptsto_w64_halves`, `ptsto_loc_combine`, `ptsto_w64_split`
  (`client/v3/WatchRecon.lean:78,87,250`), `ptsto_split_half`, `ptsto_split_half_loc`
  (`WatchRun.lean:499,508`), `ptsto_halves` (`watchGRPCStream__serveSubstream.lean:177`),
  `loc_halves`, `chan_halves`, `loc_split`, `chan_split`
  (`leasing/InvLeasingSessionLemmas.lean:118,132,146,154`), `half_pointsto_fractional_loc`,
  `half_pointsto_fractional_chan` (`leasing/InvLeasingKV.lean:148,156`). Fix: in Perennial, next to
  `typedPointsto_frac_add`, a generic `typedPointsto_half_split` / `typedPointsto_half_combine`
  (with agreement) / `typedPointsto_half_fractional` over any `V`; then delete the twelve. Needs a
  Perennial branch and a pin bump (`notes/perennial-changes.md`).
- **C2. Set into a replicate padding** (5 copies of
  `(l ++ replicate k z).set l.length x = l ++ [x] ++ replicate (k-1) z`): `set_replicate`
  (`client/v3/OpTxn.lean:18`, `private`), `set_done_replicate`
  (`leasing/InvLeaseEvalLemmas.lean:37`), `crl_set_repl`, `crl_set_repl'`
  (`client/v3/lessor__closeRequireLeader.lean:44,49`), `set_append_replicate`
  (`concurrency/InvSTMReads.lean:85`). Fix: one lemma in Perennial's list facts; the `crl_*` and
  `set_append_replicate` forms (`M - k` with `k < M`) follow from it by `omega`.
- **C3. Apply a list of functions**: `opFold` (`client/v3/InvOp.lean:210`), `stmOptsFold`
  (`concurrency/InvSTM.lean:244`), `cfgApply` (`cache/v3/InvConfig.lean:40`) are all
  `gs.foldl (fun o g => g o) o`, each with its own `_take_succ` lemma (`opFold_take_succ`
  `InvOp.lean:415`, `stmOptsFold_take_succ` `InvSTM.lean:247`, `cfgApply_take_succ`
  `InvConfig.lean:43`). Fix: one polymorphic definition (Perennial, or `client/v3/InvOp.lean` if
  Perennial declines) with one `_take_succ`; the three become abbreviations or go.
- **C4. Namespace masks** (12 `*_mask` lemmas repeating the `ndot_ne_disjoint` proof): `wkN_mask`
  (`watchkv/Writes.lean`), `linkvN_mask`, `linkvInvN_mask`, `callN_mask`, `linkvE_mask`,
  `linkvE_mask'` (`linkvtxn/Inv.lean`), `wgsWg_mask` (`client/v3/InvWatchWg.lean:91`),
  `kvClientN_mask` (`InvServerKV.lean:240`), `leasingWg_mask`
  (`leasing/InvLeasingKVLemmas.lean:150`), `cacheWg_mask` (`cache/v3/InvCache.lean`, already
  through Perennial's `sync.wg_mask_ndot_ne`), `goAttach_mask`, `wg_wgi_mask` (server side).
  Perennial's `Std/Namespaces.lean` has `mask_ndot_ne'` (`↑(N.@x) ⊆ ⊤ \ ↑(N.@y)`) and
  `mask_diff_ndot2`; the client's form `↑(N.@x) ⊆ (⊤ \ ↑(N.@y)) \ ↑(N.@z)` is one more lemma there
  (`mask_ndot_ne2`), after which each `_mask` is a one-line application or goes.
- **C5. Option-model unfolding** (98 proofs are `simp [opXModel, opFold, withYM, …, OpFull.*Init,
  OpFull.newOp, OpModel.zero, txnOpOf]`; `grep -rn 'simp \[[^]]*opFold'`): 17 in
  `concurrency/InvMutexLemmas.lean`, 7 in `cache/v3/Cache__get.lean`, 6 in
  `recipes/InvRecipesLemmas.lean`, 5 in `recipes/InvDoubleBarrier.lean`, 4 each in
  `recipes/InvRecipesSeq.lean`, `InvRecipesQueue.lean`, `InvRWMutex.lean`,
  `leasing/leasingKV__deleteRangeRPC.lean`, the rest spread over leasing, concurrency, the cache
  and `linkvtxn/Client.lean`. About 60 are standalone `_fields`/`_rev`/`_under`/`_txnOpOf`/
  `_cmp_*` lemmas, several identical but for the op's name: `acquire_cmp_absent`/`_present`
  (`InvMutexLemmas.lean:242,248`) vs `version_cmp_absent`/`_present`
  (`InvRecipesLemmas.lean:52,59`); `lastCreateOp_rev` (`InvMutexLemmas.lean:136`) vs
  `lastRevOp_rev` (`InvRWMutex.lean:94`); `rwMyKey_new`/`rwMyKey_field` (`InvRWMutex.lean:287,279`)
  vs `dbMyKey_new`/`dbMyKey_field` (`InvDoubleBarrier.lean:245,237`); `putOp_txnOpOf`
  (`InvMutexLemmas.lean:213`), `leasePut_txnOpOf` (`InvLeasingGetLemmas.lean:191`, already an
  alias) and `putLeaseOp_txnOpOf` (`cache/v3/InvEtcdTxn.lean:197`); the seven `*Txn_under`
  (`campaignTxn_under`, `resignTxn_under`, `proclaimTxn_under`, `acquireTxn_under`,
  `newKeyTxn_under`, `deleteRevTxn_under`, `seqTxn_under`), each a `refine ⟨?_, ?_, ?_⟩` over the
  transaction's three lists. Fix, in order: (i) a registered simp set (`register_simp_attr
  op_simps` on the model definitions in `client/v3/InvOp.lean` and the `with*M` transformers) so
  each of the 98 is `simp [op_simps]`; (ii) a generic `TxnModel.under_of_keys` ("every op's key has
  prefix `pfx` → `Under pfx`") for the seven `_under`; (iii) generalise the `_cmp_absent/_present`
  pair over the comparison target and merge the `_rev`, `MyKey`, `putOp_txnOpOf` pairs.
- **C6. Thread-token wait groups**: `cacheWgInv` (`cache/v3/InvCache.lean:451`, with
  `wp_cacheWg_Add/AddOwed/AddRunning/Done/DoneOwed`, `cacheWg_ctr_bound/_owed`) and `leasingWgInv`
  (`leasing/InvLeasingKV.lean`, header: "as the cache's"; `wp_leasingWg_Done/DoneOwed`,
  `leasingWg_ctr_bound/_owed` in `InvLeasingKVLemmas.lean`, `InvLeasingNewLemmas.lean`) are the
  budget-and-owed variant of the join idiom the watch client moved to Perennial's `sync.tokJoin`
  on 2026-10-22 (`Proof/sync/WaitGroupTokJoin.lean`; `notes/STATUS.md`, "Perennial idioms"). The
  "owed" running tokens (goroutines announced without a deposited thread token, bounded by
  `*WgOwedMax`) are what `tokJoin` lacks. Fix: propose the owed extension to Perennial
  (`notes/perennial-changes.md`), then both move onto it, as the watch client did; until then,
  at least one copy of the `_ctr_bound` arithmetic. Larger than the rest: a design review first.
- **C7. Watch facts over two models**: `chain_wk`, `prog_step_wk`, `resp_wk`
  (`watchkv/WatchFacts.lean:55-221`, over `v3rpc.etcdModelOfServer E`) and `chain_hist`,
  `prog_step_hist`, `resp_hist` (`linkv3p/WatchHist.lean:113-270`, over
  `v3rpc.etcdModelOfHistory γr.raft γr.kv`) are about 130 lines of the same proof, each reducing to
  the pure `prog_wk` through "this model's step logs are watchkv logs" (`wk_log` at the server,
  `hist_wk` at the history). Fix: one version in `watchkv/WatchFacts.lean` parameterised by the
  model instance `EM` and a hypothesis `□ (∀ L, EM's step log L ={⊤}=∗ ⌜WkLog P L⌝)` (or by the
  `srvStep`/`histStep` unfolding, whichever is simpler), with `evFact`/`evFactH` as its `revAt`
  parameter (`common.evFactR` already takes it); the `_hist` three become instances. `cachekv`'s
  `step_ck`/`certChain_ck`/`log_ck` (`cachekv/CacheFacts.lean`) are a third variant over
  `certChain` with `CurI : Nat → Int → Prop` where the others have `Cur : Nat → w64 → Prop`; check
  whether it fits the same parameterisation after C7, not before.
- **C8. Linkvtxn's two list folds**: `resOfL`/`resOfL.go`/`resOfL_length`
  (`linkvtxn/resOf.lean`, `Abs.lean:1037`) and `kvsOfL`/`kvsOfL.go`/`kvsOfL_length`
  (`linkvtxn/kvsOf.lean`, `Abs.lean:1029`) have the same shape; see whether one is a `map` of the
  other.

### D. Generic list lemmas that belong to Perennial

Besides C2, the client proves these about `List` alone (Perennial material if Lean's `List` API
lacks them; check `List.getElem?_append`, `List.prefix_*`, `List.mem_take`, `List.getElem?_zip`
first): `zip_get_snd` (`client/v3/ServerKVGet.lean:216`), `getElem?_of_getLast?`
(`watchGRPCStream__serveSubstream.lean:43`), `nodup_not_mem_drop` (`WatchContent.lean:53`),
`all_congr_mem` (`ServerKVTxn.lean:157`), `getElem?_snoc_cases` (`WatchClientModel.lean:506`),
`prefix_snoc_eq` (`WatchRun.lean:533`), `crl_getElem_mid`, `crl_set_mid`, `crl_keep_mid`
(`lessor__closeRequireLeader.lean:28-39`), `filterMap_take_succ`, `map_take_succ`
(`concurrency/InvSTMMaps.lean:81,87`), `prefix_drop_cons`, `prefix_snoc_cases`, `prefix_snoc_drop`
(`cache/v3/InvWatcher.lean:447-466`), `demuxBEL_mem_take`, `demuxBEL_mem_drop`
(`cache/v3/demux__broadcastEventsLocked.lean:32,40`), `applyEventsLocked_mem_take`, `_split`,
`_take_succ`, `_drop_cons` (`cache/v3/store__applyEventsLocked.lean:155-176`),
`demuxUSL_take_subslice`, `demuxUSL_getLast_take` (`cache/v3/demux__updateStoreLocked.lean:25,109`),
`flatten_length`, `flatten_getElem?` (`examples/lintest/LinTheory.lean:95,104`), `getElem?_inj`
(`porcupine/ListLemmas.lean:58`), and the `w8`/`GoStringLt` facts of `client/v3/PrefixRange.lean:23-48`
(`goStringLt_cons_iff`, `goStringLt_nil_cons`, `goStringLt_not_nil`, `w8_eq_of_Z`, `w8_lt_ff`,
`w8_succ`; `GoStringLt` is Perennial's, CLAUDE.md names it). 102 pure lemmas mention `List`,
`w8` or `GoStringLt` with no project noun; the list above is the part with no project definition
at all.

### E. Structural copies (decide, don't just delete)

- **The witness part**: 26 files of `RaftWitness/Proof/.../examples/kvwitness/` are byte-identical
  to `Proof/.../examples/kv/`'s after renaming `RaftWitness.`/`kvwitness` to `kv`: `Alloc`,
  `Check`, `Gen`, `KV__Append`, `KV__Get`, `KV__Put`, `KV__Read`, `KV__RemoveMember`,
  `KV__TransferLeadership`, `KV__answer`, `LemmasOps`, `Main`, `Model`, `copyMap`, `decode`,
  `encode`, `fits`, `hashMap`, `hashString`, `quietLogger__*` (4), `tick`, `transfers__take`,
  `within`: 2,456 lines. CLAUDE.md makes the part's copies deliberate (its modules declare the same
  names and it never imports the main kv), but the pure files (`Model`, `Check`, `encode`/`decode`,
  `fits`, `hashString`, `copyMap`, `within`, `LemmasOps`: no Goose names) could live once in a
  neutral namespace both import, e.g. `Proof/.../examples/common/KVModel.lean` (`common` is already
  imported by both, D36). The `KV__*` method proofs stay copies (they are about each part's own
  translation).
- **linkv3p's Go** (`examples/linkv3p/linkv3p.go`): `startMember`, `newClient`, `writer` are
  `common.StartMember`, `NewClient`, `Writer` plus the keepalive enforcement policy, the client's
  keepalive options and a client list (`writer` picks a random client). Parameters of common's
  functions would remove them and their proofs (`linkv3p/startMember.lean`, 237 lines); a
  regeneration (`etc/goose.py --project linkv3p --project common`) and the two `Link.lean`s follow.
- **Per-example `Link.lean` repeats** (12 theorems in 2-4 examples: `zap.wp_NewNop`,
  `v3.wp_WithPrefix`, `v3.wp_WithRev`, `v3.wp_getPrefix`, `v3.wp_WithCreatedNotify`, ...): generated
  by `etc/gen-link.py` per example, by design. Leave.

### Not revisited

D35's decision not to merge the server-side `ServerKVGet/Put/Txn.lean` family (`kv_get_server`,
`kv_put_result`, `kv_txn_commit`, the `isEtcd*KVTodo_of_kv` four, each used by the recipes'
`KVOfServer.lean`) with the client `_any` results: their statements are about the recipes' and the
cache's contracts at the server's model.

## Order of work (each step a branch, `etc/gates.sh` before it lands)

1. **Perennial branch** (one, off `lean`): C1's half lemmas, C2's set-replicate, C4's
   `mask_ndot_ne2`, D's list lemmas that Lean lacks. Record in `notes/perennial-changes.md`; bump
   the pin when landed. Until then the local copies stay (CLAUDE.md: no local `Proof/Lib`).
2. **The misplaced and exact duplicates** (A, B): no Perennial dependency; about 15 lemmas.
3. **C7**, the watch facts: about 130 lines.
4. **C5**: the simp set, then the `_under` lemma, then the pairs.
5. **C3**, **C8**.
6. **C6** and **E**: each after a decision (Perennial's `tokJoin` extension; where the kv model
   lives; common's parameters).

After each step: `lake build`, `etc/tcb-report.py --check`, the fingerprint of the closed theorems
unchanged, `etc/dead-decls.py` for what the step made unused; then `notes/STATUS.md`.

## Pending

`etc/dead-decls.py --assume-built` over `client`, the examples and `cache` (run 2026-10-22 on
branch `dedup`, after its steps): nothing these steps left unused. What it lists predates them:
generated `wp_initialize'`/`get_isPkgInit_wf_inst`, derived `DecidableEq` instances, the type
abbreviations `watchkv.wkv`/`wev`/`wrec` and `cachekv.ckv`/`crec`/`ckKV` (unfolded at elaboration,
so unused in proof terms but used in the source), and about twenty lemmas (`client.sext_zero`,
`client.etcdReached_zero`, `client.grpcCfgOk_of_started`, `recipes.putKv_mem`/`_wf`, linkvtxn's
`absStore_nil`, `rangeWireOf_list`, `absVR_encVR`, `kvVR_eq`, `CfgEquiv.trans`, linkv's
`kvOpStep_put_sorted`, `kvOpStep_get`, `findKey_mem`, `absSt_init`, `PSet.Closed.perm`,
`EtcdModel.etcdReadAt_timeless`, `OpT.top`, `WatcherPub.trivial`, ...): a proof-cleanup pass's.

The scripts of the audit (statement extraction, exact and near-duplicate matching, the pure-lemma
listing) were session-scratch Python; they are easy to rewrite from the description above if a
re-run is wanted after the steps land.
