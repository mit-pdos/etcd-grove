# putgetN handoff (branch `putgetN`, worktree /shared/etcd-grove-auth3)

Plan: `notes/clusterN-scope.md` (decisions Q1-Q6 approved by the user 2026-11-15 via etcd-grove-81,
recorded in the worktree's `questions.md`).

## Done
- S1 Go: `examples/lib/etcdstart/members.go` (`Member`, `Members`, `StartMembers`),
  `examples/etcd/putgetN` (`Main(k)`, `Token = "putgetN-1405"`: at "putgetN" the id premise fails
  first at k = 214; TestMemberIDs checks every k <= 1000), TestPutGetN (random odd k, 20 runs passed,
  `/shared/tmp/putgetN/runs20.txt`); goose project `putgetN`.
- `Proof/.../lib/etcdstart/MembersDefs.lean` (vocabulary: `membersOf`, `iuOf`, `urlsN`, `MemberG`,
  `memberUp_tok`, decimal/loopback lemmas), `Members.lean` (proof), `StartMembers.lean` (proof; both
  loops), `AllocN.lean` (`allocN`), with their specs in `Spec/.../lib/etcdstart/`.

## Next, in order
1. putgetN package: `Base`, `Defs` (BootFacts over a list, `dirN`, premises as `[∗list] m; id ∈
   membersOf ..; ids`), `Spec/.../etcd/putgetN/Main.lean`, `Main.wp_proof` (allocN; split member 0's
   client right; build `xs := zip members gs`; `StartMembers`; `Serve` on member 0; putget3's tail).
2. HARD STOP: the statement of `etcd_putgetN_safe` in plain words, before linking.
3. Link: etcdstart `Link.lean` entries (`etc/link-lean-first-common.txt`, `etc/gen-link.py --common`),
   `MainLinked`, `Adequacy`, `Results`, `PkgTable`/`Init` (`etc/gen-init.py`: add putgetN to ROOTS and
   PROGRAMS; etcdstart's Init also changes: it imports strconv now), collection
   `etc/tcb-collections/putgetN.txt`, interfaces, gates.

## Pitfalls
- Every change to etcdstart's Go rebuilds its importers (all examples).
- `have` inside an IPM goal after `iframe` can fail with "unknown free variable": state pure facts
  before the IPM steps.
- `wp_for` chokes on a Go variable named `prefix`; two Go variables named `i` (the range loop's own
  counter) clash.

## Build
`lake --packages=/shared/tmp/manifest-ddc.json build <targets>` under
`systemd-run --scope -q -p MemoryMax=64G`; check files with
`LAKE_OPTS=--packages=/shared/tmp/manifest-ddc.json etc/lean-check.py`.
