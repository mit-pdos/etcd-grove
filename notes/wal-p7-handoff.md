# P7 handoff (D6-T6, the snapshot directory's crash law) — START HERE

Branch `etcd-safe-p7`, worktree `/shared/etcd-grove-p7` (#50 P7, sub-issue #53). Base `211ef407a2`
(`etcd-safe-d6t6impl/2026-11-24`), lean `6c5b77f34a` merged (dist statements and `NewServer.specC` moved to
lean's `HEnv : EtcdVerifyOff`).

State (2026-11-25): design only. `notes/etcd-dist-d6.md` §T6 "round 4" lists what reading the crash machinery
found beyond round 3: the snapshot directory's inode across a crash (spine durability), free names durable at
the first start, a pending file removed before its sync, and the simplifications (no new bbolt law;
one `nameCrash` predicate; `Rm → Rm'` a plain wand). These touch trusted text (`snapDirInv`'s body,
`snapDirOwn`, three axioms' docstrings, the unproved `bootFs.touchMember.law`), so they wait for the lead's
go-ahead.

Pin: the etcd re-pin `e94f33b50` does not change `server/etcdserver/api/snap/` (only `storage/backend.go`'s
OpenSnapshotBackend directory sync, owned by `etcd-safe-main-pin`), so this branch stays on lean's pin.

After the merge, `etc/gen-init.py --check` reports 15 differences that lean itself does not have (lean: clean):
the base's D2 config adds a main-tree `examples/lib/remote` Init, which makes the Dsverify and `Net/` remote
initializers import it and declares `Net/`'s stale. Left as committed (not regenerated) for the lead: the two
trees' remote initializers declare the same names, so the generated result needs a decision.
