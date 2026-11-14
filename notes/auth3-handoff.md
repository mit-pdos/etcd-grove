# auth3 handoff (a three-member etcd_auth_safe, A1)

Plan: `notes/auth3-scope.md` (decisions in its §6). Worktree `/shared/etcd-grove-auth3`, branch
`auth3-a1` (the Scope landed from `auth3-scope`: lean 7245799336). Coordinator etcd-grove-81; rules
`/shared/tmp/coord-81/common-rules.md`.

## Done
- Scope and the non-issue landed (lean 7245799336).
- S0 / CP0: (1) `alloc3On` composes three times (`lib/etcdstart/Alloc3On.lean`, built, no sorry);
  (2) a follower's apply of an `Authenticate` entry gets `tokPrefixOk` from the log: `kvInvOn`'s
  log invariant `plainLogOn` (`KVAuthModel.lean`, `plainEntryOn`: every logged admin entry is
  `adminKindOk`, whose `.authenticate` clause is `tokPrefixOk`), member-independent;
  (3) `Authenticate` does NOT give `authPubLb`: the server's answer (`authnAns`,
  `AuthnServedOn.lean`) and the client's `etcdAuthenticateSpec` carry only `tokIssued`, so A2's
  route (i) needs a server law too (Q2, for A2).
- S1 (A1), all built, no sorry:
  - Go: `examples/etcd/auth3/{auth3.go,auth3_test.go}` (tests pass, 32G cap, GOWORK=off);
    authkv's `Main` body after the start moved into the exported `auth.Run(s, addr, lg)`
    (`newUserClient` takes the address): the Go-level form of Q6 (a Lean lemma cannot be shared
    across packages' code). FLAGGED for CP1: authkv's Go program changed (behaviour-preserving).
  - Translation: `etc/goose.py` project `auth3`, `etc/gen-init.py` (auth3 Init/PkgTable).
  - Lean: `auth/Run.lean` (Spec + Proof, from `Main.wp_proof`), `auth/Main.lean` shortened,
    `Work`/`WorkCalls`/`newUserClient` take the address; `auth3/{Defs,startMember,Main,MainLinked,
    Adequacy,Results}.lean`; `etcd_auth3_safe`.
  - Gates touched: bounds and mode baselines raised (new specs with threadBound/receiptBound;
    auth3's startMember `specM true`), `etc/mode-allow.txt`, `etc/import-all.txt` (Alloc3On),
    `etc/api/etcdstart.txt` (+Alloc3On, interface generated), `etc/tcb-collections/auth3.txt`.

## Next, in order
1. CP1: STOP before landing; report the theorem, premises, trust base vs authkv/putget3.
2. After 81's go: STATUS entry, gates via land.sh.

## Build
`flock /shared/tmp/etcd-grove-build.lock systemd-run --scope -q -p MemoryMax=64G lake
--packages=/shared/tmp/manifest-ddc.json build`; land with `LAKE_PACKAGES=/shared/tmp/manifest-ddc.json
PERENNIAL_CHECKOUT=/shared/perennial-ddc0f0acc etc/land.sh` (unwrapped, GOWORK not exported).
