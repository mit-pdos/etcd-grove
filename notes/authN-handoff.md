# authN handoff (branch `authN`, worktree /shared/etcd-grove-auth3)

Plan: `notes/authN-plan.md` (for etcd-grove-81; the user approves the statement at the HARD STOP before
linking). Rules: /shared/tmp/coord-81/common-rules.md.

## Done
(see the commits on `authN`)

## Next, in order
1. etcdstart: `MembersAuthDefs` (cfgOkOn, bootPremiseOn, memberPreOn, memberUpOn_tok), `StartMemberAuth`
   (spec + proof, from auth3's `startMember`), `StartMembersAuth` (spec + proof, from `StartMembers`),
   `AllocNOn` (memberGOkOn, memberBootsOn_of, allocNOn). Drafts were in /shared/tmp/authN/.
2. authN: `Base`, `Defs` (premises over `members k`, bootPremiseOn; putgetN's `BootFacts`/`dirN` reused),
   `Dir` (authN's members' addresses: all peers and all clients; addresses' perm/nodup/lit), `run`
   (serve loop, set-up via member 0, barrier loop, principals at 0, 1 % k, 2 % k), `Main`.
3. HARD STOP: statement in plain words vs etcd_auth3_safe.
4. Link: MainLinked, Adequacy (`etcd_adequate_members` with all start bundles), Results, PkgTable/Init
   (`etc/gen-init.py`), etcdstart Link entries (`etc/link-lean-first-common.txt`, `etc/gen-link.py --common`),
   `etc/api/etcdstart.txt`, collection `etc/tcb-collections/authN.txt`, interfaces, bounds, gates.

## Pitfalls
- See notes/putgetN-handoff.md and notes/txnlinfaultsN-handoff.md (loop invariants, `iframe` on snoc'd big-seps).
- Go tests: `cd examples; GOWORK=off PATH=/usr/local/go/bin:$PATH systemd-run --scope -q -p MemoryMax=32G go test ./etcd/authN/`
  (`AUTHN_MEMBERS=k` fixes k).

## Build
`systemd-run --scope -q -p MemoryMax=64G lake --packages=/shared/tmp/manifest-e9e.json build <targets>`;
check files with `LAKE_OPTS=--packages=/shared/tmp/manifest-e9e.json etc/lean-check.py`.
