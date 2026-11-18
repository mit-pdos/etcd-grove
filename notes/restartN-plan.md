# restartN: plan (2026-11-15, for etcd-grove-81)

Goal (etcd-grove-81's brief, 2026-11-15): `etcd_restart3_safe` generalized to `k` members on the generic start
(`etcdstart.Members`), about fork `6e8f0c004` (A-g). Branch `restartN` (worktree `/shared/etcd-grove-restartN`, off
lean `73cffb21d3`). Decisions: `questions.md`.

## The theorem: `etcd_restartN_safe`, for `2 ≤ k ≤ 1000`

Recommended: **`2 ≤ k ≤ 1000`**, no parity premise; `k = 1` stays `etcd_restart1_safe` (a different program:
with one member there is no follower to stop, and no write can commit while it is down).
- `Main(k)` for `k < 2` returns at once (`Run` checks `k < 2` first), so the theorem would hold at `k = 1`
  trivially; the premise `2 ≤ k` keeps the statement honest about what it covers.
- `k = 2` is covered and true, but in a real run the Puts while member 1 is down cannot commit (no quorum
  of 2 with one member), so they time out and `Run` returns before its check. The theorem at `k = 2` is
  about runs that never reach the check (TestRun at `RESTARTN_MEMBERS=2`: "Run returned before its check").
  Alternative: `3 ≤ k`. Recommended `2 ≤ k` anyway (strictly stronger, no extra cost); the docstring says it.

## The program (`examples/etcd/restartN`, done: S1)

restart3's, with:
- the members `etcdstart.Members("restartN", k, 29000, 30000)` (member `i` named `restartN-i`, peer
  `127.0.0.1:(29000+i)`, client `127.0.0.1:(30000+i)`, not served);
- **its own start loop `startMembers`**, StartMembers' steps (the initial cluster's map, then per member in order:
  `BuildServer` at the token and `SnapCount = SnapCatchUp = 1`, the peer address listened on and served, `Start`),
  but each peer address served **through the member's `raftSwap`** (restart3's `newMember`), not by its raft
  handler directly. `etcdstart.StartMembers` cannot be used as is: it serves `s.RaftHandler()` on the listener for
  good, so the restarted incarnation could only be served by closing and re-listening the address, which needs
  the listener-close assumption (HS3) restart3 avoided (D-R3-4). Alternatives: (A) a new `etcdstart` function
  (`StartMembers` with swaps, the swap moved into `etcdstart`; rebuilds every example); (C) `StartMembers` always
  swapping (changes the programs of `etcd_putgetN_safe` and `etcd_txnlinfaultsN_safe`). Recommended: the local
  loop (no change to `etcdstart` or to a closed theorem's program).
- writes through member `0`; the member stopped is `k-1`, or `k-2` if `k > 2` and member `k-1` sees itself as
  leader (restart3: member 3, or 2 if 3 leads; member 1 writes);
- `stop(s, k)` waits for `AppliedIndex() >= k` (the `k` bootstrap entries; restart3's `NBoot = 3`);
- `N1 = 5`, `N2 = 20`, the check exactly restart3's (25 pairs at version 1, revision 26);
- token `restartN-1440`: the first `restartN-<i>` at which the 1000 members' ids have distinct, nonzero 16 low
  bits (`TestFindToken`); `TestMemberIDs` checks every `1 ≤ k ≤ 1000`.

Go test (`restartN_test.go`, `TestRun`): `k` random from {3, 5, 7}, `RESTARTN_MEMBERS` overrides; restart3's
counts, and in addition **requires** the snapshot catch-up (a merged snapshot sent and a snapshot installed after
the restart). 20/20 under the 32G cap, each run its own process (k=3: 8, k=5: 3, k=7: 9; 1.1-1.6 s;
`/shared/tmp/restartN/runs20.txt`).

## The proof (S2-S4)

`Proof/.../examples/etcd/restartN/`, namespace `etcd_restartN`; restart3's generic parts imported, not copied:
`restart/Swap.lean` (the swap's ghost state), `restart/KV.lean` (`r3Inv`, 25 puts); putgetN's `dirN`/`BootFacts`
(`putgetN/Defs.lean`).
- S2 (copies over restartN's Go names): `Base`, `Defs` (`members k`, `token`, `premises k N ids ps ctxs boot`,
  `swLock`/`swapOk`/`memberRec`), `Dir` (putgetN's directory facts at restartN's members), the specs and proofs of
  `build`, `newMember`/`restartMember`, `raftSwap`, `put`, `stop` (the bound `boot.length ≤ k`), `check`.
- S3: `startMembers` (StartMembers' two loops, per member `build` + `newMember`; post per member: its `memberUp`
  with the token lent out, its `memberRec`; the cluster's map), `Run` (`allocN`; the candidates' `memberBoot_cmp`/
  `memberBoot_restartFacts` taken before the start; the `if` with `stopCand` as restart3's, the stopped member
  looked up in both slices), `Main`.
- **HARD STOP (C4)** before linking: the statement and premises in plain words, against `etcd_restart3_safe` and
  `etcd_putgetN_safe`.
- S4 (after approval): `PkgTable`/`Init` (gen-init), `MainLinked`, `Adequacy` (`etcd_adequate_members`, putgetN's),
  `Results`, collection `etc/tcb-collections/restartN.txt` (expected: restart3's 530 plus putgetN's `FormatUint`),
  interfaces, bounds, gates.

## The premises (expected; the hard stop states them exactly)

restart3's, with the three ids replaced by putgetN's list `ids` (`Hlen : ids.length = k`, `BootFacts ids ps ctxs
boot`), and `premises k N ids ps ctxs boot`: `bootstrapContract` for every member's first start (putgetN's
`[∗list]`), **N1 (`bootPremiseR`, the restart contract) for the stop candidates only**, the last
`min 2 (k-1)` members (`k-2` and `k-1`; member `1` at `k = 2`), its text unchanged; `bootMarshal`;
`commonPremises`. `HAs`/`HDs` over the `k` peer addresses and data directories. No new kind of premise expected.

## Checkpoints
1. S1 done (Go, tests, translation): commit `6e059747da`.
2. HARD STOP before linking (statement).
