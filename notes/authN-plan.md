# authN: `etcd_authN_safe`, auth3 for every member count 1 ≤ k ≤ 1000 (plan, 2026-11-15)

For etcd-grove-81. The task: `etcd_auth3_safe` (`examples/etcd/auth3`) generalized to `k` members on the
generic start of putgetN/txnlinfaultsN (`etcdstart.Members`/`StartMembers`, `notes/clusterN-scope.md`),
`1 ≤ k ≤ 1000`. The user approves the statement at the HARD STOP before linking.

## Name and shape

- Theorem **`etcd_authN_safe`**; package `examples/etcd/authN`, Goose project `authN`, module path
  `…examples.etcd.authN`; `Main(k uint64) int`; the program `authN.initialize' #() ;; Main #(W64 k)`.
- Members `etcdstart.Members("authN", k, 29000, 30000)`: member `i` (from 0) is `authN-i`, peer
  `127.0.0.1:(29000+i)`, client `127.0.0.1:(30000+i)` (ranges no other example uses, so the examples'
  tests can run at once). Token `authN-1286`: the first `authN-<n>` whose first 1000 member ids have
  distinct, nonzero 16 low bits (a member's id depends only on its peer URL and the token, so the ids
  of `k` members are a prefix of the 1000's). `TestMemberIDs` checks every `k ≤ 1000`.
- Every member serves its gRPC API (as auth3's A2).

## The principals, by member index (0-based)

| who | auth3 (1-based) | authN | k = 1 | k = 2 | k ≥ 3 |
|---|---|---|---|---|---|
| set-up, root's history check | 1 | 0 | 0 | 0 | 0 |
| the client with no token (`anon`) | 1 | 0 | 0 | 0 | 0 |
| `u` (key range `[a, b)`), and `u`'s watch check | 2 | `1 mod k` | 0 | 1 | 1 |
| the client with a token no provider issued (`bad`) | 2 | `1 mod k` | 0 | 1 | 1 |
| `v` (no roles) | 3 | `2 mod k` | 0 | 0 | 2 |
| root's barrier read | every member | every member (a loop) | | | |

At `k = 3` this is auth3's assignment exactly. Members `3..k-1` serve and pass the barrier but no principal
uses them (as auth3, a principal's requests are checked at its member only). Alternative (not proposed):
spread more principals' clients over all members; it adds nothing the theorem can say per principal.

## Go

- `etcdstart` (`auth.go`): `StartMemberAuth` (auth3's `startMember` at any token and snapshot settings:
  authkv's configuration, the simple token provider, TTL 300) and `StartMembersAuth(ms, token, snapCount,
  catchUp, lg)` (StartMembers' two loops, each member started by `StartMemberAuth`). Generic, for
  auth-on-leases S4's k-member theorem later (which will add a lease mode to `memberBootOn`/`memberUpOn`).
- `authN`: `Main(k)`, `run(srvs, ms, lg)` (a serve loop, the set-up through member 0, a barrier loop, the
  principals as above, the checks), `barrier`/`newUserClient` (auth3's).
- Tests: `TestMemberIDs` (every `k ≤ 1000`), `TestMembers`, `TestMain` (one random odd `k` from
  {1, 3, 5, 7}, `AUTHN_MEMBERS` overrides, logged first), with auth3's refusal and watch checks; 20 runs
  under the 32G cap.

## Lean

- etcdstart (generic, reusable): `StartMemberAuth`/`StartMembersAuth` specs and proofs (`MembersAuthDefs`:
  `cfgOkOn`, `bootPremiseOn`, `memberPreOn` = `memberPre` with `memberBootOn`, `memberUpOn_tok`; post
  `threadTok -∗ ∃ γa, memberUpOn …`); `allocNOn` (`allocN` with
  `srvClusterBootOn_alloc`/`memberBootOn_of`, and `sameCluster` of every member's names with member 0's);
  `dirN` and its facts generalized from putgetN's `Dir.lean` into etcdstart (putgetN untouched: its
  exported statement names its own; a later cleanup).
- authN: `Defs` (`premises k N ids …` as putgetN's, at authkv's configuration), `run` (loops), `Main`,
  `MainLinked`, `Adequacy`, `Results`, generated `PkgTable`/`Init`, collection `authN.txt`.

## Checkpoints

1. CP1: Go and tests (20 runs), translation, etcdstart's auth start proved.
2. HARD STOP: the statement and premises in plain words vs `etcd_auth3_safe`, `Main.wp_proof` proved; before
   linking. Also a stop on any trusted text (none expected: `FormatUint` is already trusted, through putgetN).
