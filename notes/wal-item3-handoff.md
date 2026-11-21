# wal-item3 handoff

## START HERE (2026-11-21 b1) — sources written, NOT BUILT (disk full while seeding); next: seed, build, gates

- Worktree `/shared/etcd-grove-walitem3`, branch `wal-item3` off lean `3c8804f01f` (pin c44b74871:
  `--packages=/shared/tmp/manifest-c44.json`, `PERENNIAL_DIR=/shared/perennial-c44b74871`). Decisions: `questions.md`.
- **Blocker (b1):** seeding `.lake/build` from `/shared/etcd-grove-mergeorigin13` (37 GB, green full build
  `20261121-021709-3361594` at exactly 3c8804f01f) with 45 GB free hit "No space left on device" (other writers);
  the partial copy was deleted (39 GB free after). Needs the coordinator: more disk, or another seed.
- **Done (uncommitted → commit "wal-item3 (b1)"):** option (a), approved by the user 2026-11-20:
  `hsSchema` in `pbSchemaOf` + `pbSchemaOf_hardState` (`PbSchema.lean`; RaftNoAx copy regenerated);
  `RaftModel/PbHardState.lean` (`hsDecode` opaque, axioms `hsEncC_ok`, `pbHsC_reg`; `pbHsC`, `pbHsC_sat`);
  `RaftModel/LawsHsMarshal.lean` (`walRaftP_marshalHs`, `walSrvP_marshalHs` over `proto.MarshalPb.spec`);
  `etcdserver/RnNewStorageLinked.lean` (`walStorSpecs_holds`, `rnNewStorageOk_law_holds`); `rnNewStorageOk.law`
  (`WalApi.lean`); `newRaftNode.wp_proof` takes it; `#Hns : rnNewStorageOk` out of newRaftNode, NodeStart (2),
  NewServer, NewServerR, `commonPremises` (etcdstart, putget3), `OneMember.premises`, auth/leaseexpiry `premises`.
  `etc/link-lean-first-server.txt` (`=rnNewStorageOk_law_holds`), `etc/gen-link.py` (server EXTRA_IMPORTS).
  Go: `examples/stdlib/walpb/hardstate_test.go`, `hardstate_adv_test.go` (from the attack; all 4 pass),
  `examples/pbschema/descriptor_test.go` (HardState root), `etc/pbschema-check.py` (+2 negative tests, 10 WAL tests).
  Ledger: 2026-11-21 entry. noioerr: session 12, `noioerr-c-runs/run3-locks-blocking-b744596bd8.out`.
- **Attack (independent, read-only, axiom skill): no refutation** (`/shared/tmp/walitem3-attack/`; 3M adversarial
  decodes, D1/D2/Size/Marshal/Clone/MarshalAppend at HardState). Its fixes done: RaftNoAx copy, tests adopted,
  `hsEncC_ok` docstring scope. Left (pre-existing trusted text, not changed): `InvProto.lean` calls `PbEncC.enc` "an
  opaque per-type encoder" though `hsEnc`/`snapEnc` are transparent.
- **Next:** seed; `etc/lean-check.py` the new files (`PbHardState`, `LawsHsMarshal`, `RnNewStorageLinked`,
  `bootstrappedRaft__newRaftNode`); regenerate Links (`etc/gen-link.py --server` and the modes over it, with
  `--packages`); fix the importers of the changed premises (Mains, Adequacy, NewServer proofs: `Hns` names);
  full timed build; gates (tcb `--check --update`: +3 axioms `hsEncC_ok`, `pbHsC_reg`, opaque `hsDecode`;
  collections; interfaces; pbschema-check; tier; copy-part/gen-raft-tla --check); STATUS; land stop.
