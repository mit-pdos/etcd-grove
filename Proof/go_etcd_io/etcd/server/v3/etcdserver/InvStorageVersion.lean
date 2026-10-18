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

The model admits these writes (`srvSVRes`):

* `s.be` is the real backend `d.be` for good: `s.be ↦□` (`NewServer` keeps half of the field's
  points-to out of `s.bemu`'s lock invariant, which holds the other half, `bemuP`), and a reader
  slot of `s.bemu`;
* the backend's contract (`isBackend` at the store's late-bound writer resource and some hooks'
  resource `Pk`), and a read token with an open share (`mvcc.bkRTx`: `ReadTx`'s reads, and the
  open share `LockOutsideApply` needs);
* `meta` is a hook bucket and `storageVersion` not a hook's own key, so the session leaves the
  readers' view and the hook's keys as they were: `Unlock`'s `viewSame` branch gives the
  writer's resource and `Pk` back unchanged;
* each `Unlock` spends a write-back token (`backend.wbTok`, the store's `storeWT` for
  `E.γ.kb = some d`), which the monitor takes from the write budget it shares with the apply
  thread, `srvWTPool E.γ` (`start` allocates it and gives it back; not in `srvSVRes`, which
  `NewServer` makes), with a time receipt of a step of that round (`srvWTPool_take`, as `apply`
  does: the pool's count is of all the receipts spent on it, whoever spends them);
* a reader slot of `s.lgMu` (`s.Logger()`).

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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The real backend `be` as the server's `s.be` holds it. -/
abbrev srvBeIface (be : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #be

/-- **The storage-version monitor's resources but its write budget** (see the file header): the
server's backend for good, `s.bemu`'s and `s.lgMu`'s reader slots, and the backend's contract
with a read token and an open share, for the store's names `γ` (`γ.kb = some d`). -/
def srvSVRes (s : Loc) (γ : mvcc.StoreNames) : IProp GF :=
  iprop(∃ (d : mvcc.KBReal) (Pk : IProp GF),
    ⌜γ.kb = some d⌝ ∗
    srvBeAddr s ↦□ srvBeIface d.be ∗ srvBemuReader s ∗
    backend.isBackend d.γB d.P (mvcc.lateW d.gx) Pk d.be ∗ mvcc.bkRTx d.γB d.P d.be ∗
    srvLgReader s)

end defs

end EtcdGrove
end Perennial
