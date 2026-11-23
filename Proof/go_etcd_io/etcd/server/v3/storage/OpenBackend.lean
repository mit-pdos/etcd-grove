/-
Trust boundary: `storage.OpenBackend` (an axiom; see
`Spec/go_etcd_io/etcd/server/v3/storage/OpenBackend.lean`). D22 S-f, 2026-10-19;
`notes/decisions.md`, "D22 S-f carried out".
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.OpenBackend

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.Assumptions]

/-- **Trust boundary** (D22 S-f): `OpenBackend(cfg, hooks)` computes `cfg.BackendPath()`, starts a
goroutine that sends `newBackend(cfg, hooks)` on an unbuffered channel and waits for it (after
10 s, `time.After`'s timer, it logs and waits again), then logs on the configuration's logger.
`newBackend` (storage's) builds `backend.DefaultBackendConfig(cfg.Logger)` with the path, the
batch limit (`openLimit`) and interval, the mmap size (from `QuotaBackendBytes`), the free-list
type, `UnsafeNoFsync`, `Mlock`, the feature gate's `NonBlockingDefrag` and the hooks, and calls
`backend.New`, whose spec (proved, `Spec/.../storage/backend/New.lean`) gives `newPostK` or a panic
(bbolt's `Open` failed); under `dbOpensOk` and `openMmapOk cfg` it does not panic (2026-10-29: the
quota's mmap size, which the `axiom` skill found unconstrained, `notes/axiom-review/openbackend.md`,
then bounded by the address space, not bbolt's limit, 2026-10-30, `openbackend-post.md`,
`nonissues/etcd-quota-backend-bytes-mmap-panic.md`). (D22 receiver epochs, S8a, 2026-10-24:
the statement generalized with `New`'s, the creator's `K` for the fresh backend's payment rights;
the same argument, `New`'s proof allocates them in the batch lock's ghost step.) (2026-11-04, R2b-3c part 2, the user's approval) Why the post's
`bFile γ (backendPathOf cfg.DataDir')` holds: `newBackend` sets the backend configuration's path to
`cfg.BackendPath()` (`<DataDir>/member/snap/db`, `config.backendPathOf`), and `New`'s spec (proved)
gives `bFile γ` at its configuration's path. Why an axiom and not a proof: the
goroutine's panic cannot be excluded from `New`'s spec, and a goroutine must not panic
(`wp_fork`); the rest (the timer's `select`, `time.After` has a spec) is provable. What would
discharge it: `OpenBackend` and `newBackend` translated with their bodies, over a `New` whose
`Open` cannot fail under the environment premise (bbolt's `Open` of a file holding a database,
not locked by another process). (2026-11-06, branch `begin-tok`, `notes/begin-tok-plan.md`)
Under `[ThreadBoundLe GF (2 ^ 29)]`, which `New`'s spec takes (bbolt's `Open_kv`: each read
transaction holds a thread's token): `New` now also takes a `threadTok` and gives it back on
success, and the goroutine `OpenBackend` starts (`server/storage/backend.go:79`) pays it with its
own fork token, so the caller's triple is unchanged. **Sound in the strict sense** (S5, 2026-11-18; until then
not: from the abstract `srvFileHolds` it gave a backend over concrete file-extension state, which
no exclusive resource it consumed backed, S3e's item 5): its pre is the concrete `fileHolds` of
the backend path (the claim on the name in the tree's shared mode, with the file), exactly what
`backend.New`'s spec (proved, over bbolt's proved `Open`) takes, and its post exactly what `New`
gives for it (`newPostK`, `hooksAt`, `bFile`, and the claim on the name, `bPath γ.db`, `ownDB`
keeping the inode), so it creates no file-extension resource: everything concrete in its post is
`New`'s proved post of what it consumed. What it adds to `New` is only the goroutine and the
`select` (no resource), and the absence of `newBackend`'s panic, which `dbOpensOk` and
`openMmapOk cfg` exclude (`¬ dbOpenOk` is `False` since S3e: bbolt's `Open` has no error under
`theFs`'s `FsNoErrAll`). (#30, 2026-11-22) Under `[ReceiptBoundLe GF (2 ^ 60)]` as well, which
`New`'s spec takes (its post holds the receipt bound: the backend's buffered entries are paid by
receipts, `backend.bufRc`): without it, from S3e to this change, the axiom gave `New`'s post at receipt
bounds where `New`'s proof gives nothing, and so was false there (ledger 2026-11-22). -/
axiom storage.OpenBackend.wp_proof : storage.OpenBackend.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
