/-
**The storage-version monitor's write access to the backend** (D19i part 2, option (A) with
(i), 2026-10-18; `notes/decisions.md`, D19i). Lean-first (no Rocq counterpart).

`monitorStorageVersion` (`server.go`) is a trust-boundary contract (names-only): every
`monitorVersionInterval` or on `clusterVersionChanged` it compares the cluster version with the
storage version (`s.StorageVersion()`: `schema.DetectSchemaVersion` over `s.be.ReadTx()`) and, if
they differ, migrates the backend (`serverVersionAdapter.UpdateStorageVersion`): under `s.bemu`'s
read lock, `s.be.BatchTx()`, `LockOutsideApply`, `schema.UnsafeMigrate` (puts, or for a downgrade
deletes, `meta/storageVersion`, which since the fork's fix of
`issues/etcd-backend-duplicate-put-stale-read.md` may be put several times in one session) and
`Unlock`.

The model admits these writes (`srvSVRes`, D22 receiver epochs, S7b, 2026-10-23: of whatever backend
is current, which `applySnapshot` may swap between two sessions):

* a reader slot of `s.bemu` at its lock invariant over the current backend's ghost variable
  `E.γbe` (`srvBemuReaderAt`); in a session (under the read lock) `bemuP` gives the current
  backend `d`: `s.be` holds it, its contract (`srvBeRO`: `isBackend` at the store's late-bound
  writer resource and some hooks' resource `Pk`), and a part of `E.γbe` at `d`;
* from the write budget `srvWTPool E` (shared with the apply thread; `start` allocates it and
  gives it back), which agrees on `d` with that part: the read token of `d` with an open share
  (`mvcc.bkRTx`: `ReadTx`'s reads, and the open share `LockOutsideApply` needs), checked out for
  the session (a part of the session's share of `E.γbe` deposited in its place) and checked back
  in before `RUnlock`, and one write-back token of `d` per `Unlock` (`backend.wbTok`), for a time
  receipt of a step of that round (`srvWTPool_take_d`, as `apply` does: the pool's count is of
  all the receipts spent on it, whoever spends them);
* `meta` is a hook bucket and `storageVersion` not a hook's own key, so the session leaves the
  readers' view and the hook's keys as they were: `Unlock`'s `viewSame` branch gives the
  writer's resource and `Pk` back unchanged;
* a reader slot of `s.lgMu` (`s.Logger()`).

Until S7b the monitor held `s.be ↦□` (the backend for good) and the read token of the boot
backend for good, which `applySnapshot`'s swap refutes.

Not in it (as for the other monitors, `notes/audit.md`): the reads of `s.cluster` (the cluster
version, the downgrade info: the persistent `isServerReq` in the contract's precondition names
the cluster), of `s.clusterVersionChanged` and `s.stopping`, and of the WAL
(`s.r.storage.MinimalEtcdVersion()`, only for a downgrade's check).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvProposer
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplyAll
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BackendBridge

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **The storage-version monitor's resources but its write budget** (see the file header): a
reader slot of `s.bemu` at the current backend's ghost variable `E.γbe`, and one of `s.lgMu`. -/
def srvSVRes (s : Loc) (E : apply.AEnv GF) : IProp GF :=
  iprop(srvBemuReaderAt s E.γbe ∗ srvLgReader s)

end defs

end EtcdGrove
end Perennial
