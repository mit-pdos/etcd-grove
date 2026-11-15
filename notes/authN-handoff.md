# authN handoff (branch `authN`, worktree /shared/etcd-grove-auth3)

Plan: `notes/authN-plan.md` (for etcd-grove-81; the user approves the statement at the HARD STOP before
linking). Rules: /shared/tmp/coord-81/common-rules.md.

## Done (branch `authN`, off lean 9e678b61e7)
- Go: `examples/lib/etcdstart/auth.go` (`StartMemberAuth`: auth3's `startMember` at any token and
  snapshot settings; `StartMembersAuth`: `StartMembers`' loops over it), `examples/etcd/authN`
  (`Main(k)`, `run`, `barrier`, `newUserClient`; token `authN-1286`, ports 29000+i / 30000+i);
  `TestMemberIDs` (every k <= 1000), `TestMembers`, `TestMainRun` (random k from {1,3,5,7},
  `AUTHN_MEMBERS`): 20 runs under 32G, `/shared/tmp/authN/runs20.txt`. Goose project `authN`;
  `common` retranslated.
- Lean, built (lake, kernel included), no sorry: etcdstart `MembersAuthDefs` (`cfgOkOn`, `bootPremiseOn`,
  `memberPreOn`, `memberUpOn_tok`), `StartMemberAuth` spec+proof, `StartMembersAuth` spec+proof,
  `AllocNOn` (`memberGOkOn`, `sameCluster_of_gOkOn`, `memberBootsOn_of`, `allocNOn`); authN `Base`,
  `Defs` (`members`, `token`, `startOf`, `memberAtMod`, `premises`; putgetN's `BootFacts`/`dirN` reused),
  `Spec/.../authN/Main.lean`.
- Drafts not yet in the tree: `/shared/tmp/authN/lean/Dir.lean` (authN's addresses; one `sorry` to replace
  in `authNAddrs_perm`, and `authNAddrs_nodup` must cover client/client too), `/shared/tmp/authN/lean/runSpec.lean`
  (run.spec sketch).

## Next, in order
1. (done) etcdstart's auth-on start.
2. authN: `Base`, `Defs` (premises over `members k`, bootPremiseOn; putgetN's `BootFacts`/`dirN` reused),
   `Dir` (authN's members' addresses: all peers and all clients; addresses' perm/nodup/lit), `run`
   (serve loop, set-up via member 0, barrier loop, principals at 0, 1 % k, 2 % k), `Main`.
3. HARD STOP: statement in plain words vs etcd_auth3_safe.
4. Link: MainLinked, Adequacy (`etcd_adequate_members` with all start bundles), Results, PkgTable/Init
   (`etc/gen-init.py`), etcdstart Link entries (`etc/link-lean-first-common.txt`, `etc/gen-link.py --common`),
   `etc/api/etcdstart.txt`, collection `etc/tcb-collections/authN.txt`, interfaces, bounds, gates.

## The run proof's design (suggested)
- Serve loop over `ms`: invariant = the thread token, the not-yet-served members' `threadTok -∗ ∃ γa,
  memberUpOn …` (StartMembersAuth's post, `[∗list] s; x ∈ ss; xs`), and, for the served prefix, a
  persistent per-member predicate bundling `serve_member`'s post (auth3 `run.lean`: E, γw, cid, mid, R and
  their facts) as `□ [∗list] j ↦ x`. Copy `serve_member` (auth3/run.lean) into authN or move it to a
  shared module (form decision).
- After `SetUp` through member 0: transfer its facts to every member with `sameCluster_of_gOkOn` (every
  member's names satisfy `memberGOkOn γ γk`, allocNOn's post) and auth3's `AuthFixed.lean` lemmas.
- Barrier loop: per member, `barrier`'s `∃ i, akAuthFixed …`, persistent, accumulated as a big-sep.
- Principals: members `0`, `1 % k`, `2 % k` (`memberAtMod`), looked up in the persistent big-seps; the
  `Work` loop as auth3's with those three members.

## Pitfalls
- See notes/putgetN-handoff.md and notes/txnlinfaultsN-handoff.md (loop invariants, `iframe` on snoc'd big-seps).
- Go tests: `cd examples; GOWORK=off PATH=/usr/local/go/bin:$PATH systemd-run --scope -q -p MemoryMax=32G go test ./etcd/authN/`
  (`AUTHN_MEMBERS=k` fixes k).

## Build
`systemd-run --scope -q -p MemoryMax=64G lake --packages=/shared/tmp/manifest-e9e.json build <targets>`;
check files with `LAKE_OPTS=--packages=/shared/tmp/manifest-e9e.json etc/lean-check.py`.
