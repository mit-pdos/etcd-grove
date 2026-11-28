/-
`storage.OpenBackend(cfg, hooks)` (`server/storage/backend.go`; names only): the backend over the
database file at `cfg.BackendPath()`, opened by `newBackend(cfg, hooks)` (`backend.New` of the
configuration's backend settings) on a goroutine, the caller waiting for it (a log line if it
takes over 10 s). The trust boundary (D22 S-f, 2026-10-19; an axiom in
`Proof/go_etcd_io/etcd/server/v3/storage/OpenBackend.lean`: the goroutine can panic, see
`InvOpen.lean`'s `dbOpensOk`). Lean-first (no Rocq counterpart).

The pre: the file holding `D` (`fileHolds`, S5: the concrete claim on the name, what `backend.New` takes; until then the abstract `srvFileHolds`) and `openPre` (`InvOpen.lean`; since 2026-10-29 with
`openMmapOk cfg`, a quota whose mmap size bbolt can map: `newBackend` panics otherwise,
`notes/axiom-review/openbackend.md`). The post: what
`backend.New` gives (`newPostK`: D22 receiver epochs, S8a, 2026-10-24, the creator's batch-lock
step trades the fresh backend's payment rights `bFresh` for `K`, as `New`'s spec now says; until
then `newPost`, which is `K := bFresh`), as a `Backend`; `newPostK` holds `backend.fkCl γ P D`:
the client's half of the compaction keys' flag (`backend.fkOwn`, at `0` if `D` records no
compaction: then it is the backend's no-compaction token `mvcc.bkNoCmp`, what the store's `restore`
consumes, `mvcc.bkNoCmp_of_fkCl`) and the bit `backend.fkV` (at `true` if `D`'s compaction keys hold
well-formed values, `mvcc.fkV_of_fkCl`, `mvcc.fkCl_wf`; both computed by `New`'s proof from `D`, so
this axiom claims nothing more of the file); the backend-compaction stage, 2026-10-29: until then a
separate wand
`⌜noCmpData D⌝ -∗ bkNoCmp γ`, an opaque token, D22 S-g). Stated at `HasLC.hasLC` (`newPost` is).
(2026-11-02, the user's approval, branch `snap-window`) And the backend's hooks are `hooks`
(`backend.hooksAt`): `newBackend` sets `bcfg.Hooks = hooks` (`server/storage/backend.go:58`), which
`New` stores in `b.hooks` (`backend/backend.go:275`); `New`'s proof gives it.
(2026-11-06, branch `begin-tok`, the user's approval: `notes/begin-tok-plan.md`, Q2) Under
`[ThreadBoundLe GF (2 ^ 29)]`, which `backend.New` (through `bbolt.Open_kv`) now takes; the triple
is unchanged: `OpenBackend`'s goroutine pays `New`'s `threadTok` with its own.
(S5, 2026-11-18) The pre is the concrete `fileHolds` (`backend.New`'s), the post `New`'s with the
claim on the name (`bPath γ.db`): the axiom creates nothing (`notes/bbolt-integration-plan.md`, S5).
(#30, 2026-11-22, ledger 2026-11-22) Under `[ReceiptBoundLe GF (2 ^ 60)]`, `New`'s receipt bound
(bbolt's `2 ^ 62` since S3e, the backend's buffers' `2 ^ 60` since #30's step 2): until then the axiom
gave `New`'s post at any receipt bound, which `New`'s proof does not (false above that bound).
(etcd-dist D6, C-I1, 2026-11-25) And, when `cfg.UnsafeNoFsync` is `false`, the crash laws' token
`backend.dbOpts γ.db` (`DbOpts.lean`): the database was opened with `NoSync = false` and
`NoGrowSync = false` (`server/storage/backend.go:38` copies `UnsafeNoFsync` into the backend's
configuration, `backend/backend.go:230-231` into `bopts.NoSync`/`bopts.NoGrowSync`, which `bolt.Open`
stores in the `DB`, bbolt `db.go:182-192`; at the etcd pin `30df685e4` and the translated bbolt `2f6fcff`,
etcd's `go.mod` replacing bbolt by `19e0771`; re-checked 2026-11-28). The one thing the post holds that `New`'s proved post does not: `dbOpts`, bbolt's
`boltSyncs γ.db` (the `DB`'s two fields persistently `false`), read by the C-I1 laws
(`backend/CrashInterim.lean`; review `notes/axiom-review/openbackend-dbopts.md`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.InvOpen
public import Perennial.ProgramLogic.Bounds
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Image
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.DbOpts

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI backend storage

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.Assumptions]

/-- `OpenBackend(cfg, hooks)` of the file holding `D`: the backend `backend.New` makes. -/
abbrev storage.OpenBackend.spec : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 29)] [ReceiptBoundLe GF (2 ^ 60)] (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (h : GoInterface) (P : BParams)
    (D : Data) (W Pk K : BNames → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ∗
      fileHolds (config.backendPathOf cfg.DataDir') D ∗ openPre cfg h P D W Pk K }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.OpenBackend)) (Val #cfg)) (Val #h))
  {{ (b : Loc) (γ : BNames),
      RET #(interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #b);
      newPostK γ P W Pk K b D ∗ hooksAt b h ∗
      -- (2026-11-04, R2b-3c part 2, the user's approval) the backend's file is the configuration's
      -- backend path
      bFile γ (config.backendPathOf cfg.DataDir') ∗
      -- (S5, 2026-11-18) and the claim on its name, `backend.New`'s (`bPath`)
      bPath γ.db (config.backendPathOf cfg.DataDir') ∗
      -- (etcd-dist D6, C-I1, 2026-11-25) the database syncs unless `UnsafeNoFsync`
      (⌜cfg.UnsafeNoFsync' = false⌝ -∗ backend.dbOpts γ.db) }}

end spec

end EtcdGrove
end Perennial
