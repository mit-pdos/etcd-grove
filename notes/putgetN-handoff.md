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

- putgetN package: `Base`, `Defs`, `Dir` (directory and address facts), `Spec/.../etcd/putgetN/Main.lean`,
  `Main.wp_proof` (checked, kernel included, 48 s). It takes the `rafthttp.bootCfg` law for up
  to 1000 members as a hypothesis `hbcfg` (to add to `rafthttp/Net.lean` at linking).
- The statement draft for review: `notes/putgetN-draft.md`.

## Next, in order
1. (done) Main.wp_proof.
2. HARD STOP: the statement of `etcd_putgetN_safe` in plain words, before linking (`notes/putgetN-draft.md`).
3. Link: the `rafthttp.bootCfg` law in `Net.lean` (rebuilds the server), etcdstart's API list
   (`etc/api/etcdstart.txt`: MembersDefs, AllocN, the Members/StartMembers specs), `etc/import-all.txt`
   (AllocN imports StartRes with `import all`, as Alloc3), etcdstart `Link.lean` entries (`etc/link-lean-first-common.txt`, `etc/gen-link.py --common`),
   `MainLinked`, `Adequacy`, `Results`, `PkgTable`/`Init` (`etc/gen-init.py`: add putgetN to ROOTS and
   PROGRAMS; etcdstart's Init also changes: it imports strconv now), collection
   `etc/tcb-collections/putgetN.txt`, interfaces, gates.

## Pitfalls
- Every change to etcdstart's Go rebuilds its importers (all examples).
- `have` inside an IPM goal after `iframe` can fail with "unknown free variable": state pure facts
  before the IPM steps.
- A projection of a literal pair left in a hypothesis (`(m0, g0).snd.ρ`, from rewriting a zip) made
  the kernel hit deep recursion on `Main.wp_proof` (maxRecDepth 8000 did not help in 11 min); restating
  the hypothesis at `g0.ρ` fixed it.
- `wp_for` chokes on a Go variable named `prefix`; two Go variables named `i` (the range loop's own
  counter) clash.

## Build
`lake --packages=/shared/tmp/manifest-ddc.json build <targets>` under
`systemd-run --scope -q -p MemoryMax=64G`; check files with
`LAKE_OPTS=--packages=/shared/tmp/manifest-ddc.json etc/lean-check.py`.

## State (2026-11-15, linked)
Linked and checked: full build (flock, 64G) green; `tcb-report.py --check` 870/4 unchanged; every collection
passes; `etc/tcb-collections/putgetN.txt` 640 axioms, identical to putget3's; gen-init and gen-interface
(etcdstart) regenerated, layout baseline updated; mode gate ok (447). Open: the bounds gate counts +6
(`spec-thread`/`spec-receipt` in putgetN and in etcdstart's `StartMembers.spec`, putget3's and
`StartMember.spec`'s pattern), awaiting etcd-grove-81's decision before land.sh.
