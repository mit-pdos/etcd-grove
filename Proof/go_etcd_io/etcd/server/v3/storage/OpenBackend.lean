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
`issues/etcd-quota-backend-bytes-mmap-panic.md`). (D22 receiver epochs, S8a, 2026-10-24:
the statement generalized with `New`'s, the creator's `K` for the fresh backend's payment rights;
the same argument, `New`'s proof allocates them in the batch lock's ghost step.) Why an axiom and not a proof: the
goroutine's panic cannot be excluded from `New`'s spec, and a goroutine must not panic
(`wp_fork`); the rest (the timer's `select`, `time.After` has a spec) is provable. What would
discharge it: `OpenBackend` and `newBackend` translated with their bodies, over a `New` whose
`Open` cannot fail under the environment premise (bbolt's `Open` of a file holding a database,
not locked by another process). -/
axiom storage.OpenBackend.wp_proof : storage.OpenBackend.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
