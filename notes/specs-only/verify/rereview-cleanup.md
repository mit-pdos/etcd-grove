# Re-review: second-tier items for a cleanup pass (coordinator's list)

- A10 (R-A10-storage.md): N1 MvccStorage.lean realization text (lines 44-45, 49, 71-78) at mvccFpM m / keyDataOfM m;
  N2 backend__begin.lean header: statSlot_wtx exists (bbolt/Api.lean:542); N3 ReqSnapshotFresh's reopen needs a
  synced file (os.WriteFile does not fsync) and NewDefaultBackend has no spec; N4 confStateSave_hook margin: bytes
  not tied to the JSON encoding, no user reads them back.
- A5 (R-A5-raft-log-conf-pb.md): raftpb snippet ReqBootstrapBytes needs a context-length bound in its Assumes
  (Marshal's size premise); RaftPb.fmtErrorf admits every verb though the call sites use only %d and %+#v.
- A3 (R-A3-client-users.md): stale "pending" Changes lines (sent with N1 to client-users).
- A9 (R-A9-apply-txn-lease-auth.md): S2 ReqApplyWrite's Assumes should exclude an ignore-value/ignore-lease put
  of an absent key (model answers keyNotFound). (S1 → server-core, S3/S4 → lease-auth, sent with N1/N2.)
- A2 (R-A2-client-watch-lease.md): S-a..S-e (sent to client-core with N1).
- A8 (R-A8-server-boot-transport.md): S3 rafthttp `sendable` must state the entries are consecutive (msgappv2 full
  frame sets next = m.index + |entries|); S1, S2, S4, S5 per the report.
- CRASH-STORY PASS (first tier, A8 N1/N2/N4; one agent, after the other fixes settle): cross-generation laws for
  raft's raftState/nodeVacant, W0's etcdState/etcdLb/envUpd and 2f's srvNet/addresses so disk_crash can be
  realized; crashOutOfScope stated over the WAL's records (not an unconstrained opaque); diskIdle_crash with
  crashRest and a 4a crash law for a closed file at rest; the boot/stop crash windows (NewServer/bootstrap before
  Start, HardStop/Cleanup) and ReqCrashRecover's "at any point" claim.
