# txnlinfaultsN handoff (branch `txnlinfaultsN`, worktree /shared/etcd-grove-auth3)

Plan: `notes/txnlinfaultsN-plan.md`. Statement draft: `notes/txnlinfaultsN-draft.md`.

## Done
- Go: `examples/etcd/txnlinfaultsN` (`Main(k, clients, ops, sched)`, `startCluster`, `bridgeAddr`, `holdToken`;
  token `txnlinfaultsN-6255`); `TestMemberIDs` (every k ≤ 1000), `TestAddrs`, `TestMainRun` (random k from
  {1,3,5,7}, `TXNLINFAULTSN_MEMBERS`): 20/20 passed under the 32G cap (k=1: 1, k=3: 2, k=5: 11, k=7: 6; 5-42 s
  each; `/shared/tmp/txnlinfaultsN/runs20.txt`). Goose project `txnlinfaultsN` in `etc/goose.py`.
- `etcdstart.StartMembers(ms, token, snapCount, catchUp, lg)` (NewMember + Start per member); putgetN passes
  the no-snapshot constants; `StartMembers.wp_proof`, putgetN `Main.wp_proof` re-checked; etcdstart `Link.lean`
  regenerated (`etc/link-lean-first-common.txt`).
- Proof: `Base`, `Defs`, `Dir`, specs and proofs of `bridgeAddr`, `holdToken`, `startCluster`, `Main`
  (lake build of the modules green, kernel included).

- Decided by etcd-grove-81 (2026-11-15): the `StartMembers` snapshot parameters and bounds +6 accepted.
- Prepared (independent of the statement): `PkgTable`/`Init` (`etc/gen-init.py`, `--check` clean, built),
  `MainLinked.lean` (`etcd_txnlinfaultsN.wp_Main`, checked, 0 errors), the collection
  `etc/tcb-collections/txnlinfaultsN.txt` (untracked: roots only; commit with `Results.lean` and its baseline).

## Next, in order
1. HARD STOP (current): the statement is with the user (`notes/txnlinfaultsN-draft.md`); do not land.
2. Link (done: `PkgTable`/`Init`, `MainLinked`; left: `Adequacy`, `Results`, collection baseline): a `MainLinked.lean`
   (as putgetN's: `Main.wp_proof zap.NewNop.wp_proof (startCluster.wp_proof etcdstart.wp_Members
   etcdstart.wp_StartMembers etcdstart.wp_Serve etcdstart.wp_NewClients cluster3.wp_StartBridge
   bridgeAddr.wp_proof strconv... holdToken.wp_proof mvcc.api.mvccApi_names_nonempty_law_holds
   (fun dir ps h hl => rafthttp.bootCfg_of_le dir ps h (by unfold peersMax; omega))) cluster3.wp_Partitioner
   etcd_partition.wp_Check`), `Adequacy.lean` (partition's `linkvGF`-style GF; `etcd_adequate_members` with
   `ms = startAddrs k`, `Bs = bridges k`, `txnlinfaultsNAddrs_perm/_nodup/_lit`, `txnlinfaultsNDirs_perm/_nodup`;
   the program with `cluster3.schedLit steps`, as partition's), `Results.lean`, collection
   `etc/tcb-collections/txnlinfaultsN.txt` (expect partition's axioms plus putgetN's `FormatUint`), interfaces,
   bounds (+6, awaiting decision), STATUS entry, gates.

## Pitfalls
- `iframe` splits `[∗list]` over `l ++ [x]` in the goal and consumes the parts: build the snoc'd big-sep
  (`BigSepL.bigSepL_snoc.2`) as a hypothesis before `wp_for_post; iframe`.
- `obtain ⟨-, ..⟩ := Hj` on a loop invariant's pure fact inside a `wp_for` branch led to "unknown free
  variable" later; use projections (`Hj.2.1`) instead.
- `rename_i` after `wp_if_destruct` renames an instance (`HasExt idIssueExt`), not the branch condition; use
  `word` with `hkn` instead.
- A loop exit's goal is `Φ …` (no WP left): an `imod` (e.g. `ownSlice_persist`) fails there; `clusterUp` keeps
  the clients' slice owned and `Main` persists it.
- Error returns inside a loop body need `wp_for_post` before `iapply HΦ`.

## Build
`lake --packages=/shared/tmp/manifest-ddc.json build Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlinfaultsN.Main
Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlinfaultsN.startCluster` under
`systemd-run --scope -q -p MemoryMax=64G`; check files with
`LAKE_OPTS=--packages=/shared/tmp/manifest-ddc.json etc/lean-check.py`. Go: `cd examples; GOWORK=off
PATH=/usr/local/go/bin:$PATH go test ./etcd/txnlinfaultsN/`.
