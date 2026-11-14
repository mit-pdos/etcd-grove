# auth3 handoff (a three-member etcd_auth_safe, A1)

Plan: `notes/auth3-scope.md` (decisions in its §6). Worktree `/shared/etcd-grove-auth3`, branch
`auth3-scope`. Coordinator etcd-grove-81; rules `/shared/tmp/coord-81/common-rules.md`.

## Done
- Scope and the non-issue landing (notes only).

## Next, in order
1. S0 probe (scratch, unlinked): alloc3On composes three times; a follower's Authenticate apply
   gets the token prefix fact from the log; does Authenticate give `authPubLb` (for A2).
2. S1 (A1): Go driver `examples/etcd/auth3/` (own startMember, three members auth on, clients on
   member 1, NoSnap settings) + Go test; `etc/goose.py`; `lib/etcdstart/Alloc3On.lean`;
   authkv's Main body factored into a lemma (statement of etcd_auth_safe unchanged); auth3 Main,
   Adequacy, Results, collection `etc/tcb-collections/auth3.txt`.
3. CP1: STOP before landing the closed theorem.

## Build
`flock /shared/tmp/etcd-grove-build.lock systemd-run --scope -q -p MemoryMax=64G lake build
--packages=/shared/tmp/manifest-ddc.json`; land with `LAKE_PACKAGES=/shared/tmp/manifest-ddc.json
PERENNIAL_CHECKOUT=/shared/perennial-ddc0f0acc etc/land.sh` (unwrapped, GOWORK not exported).
