/- Lean-first (no Rocq counterpart).

# C-I1's `dbOpts`: the database was opened syncing (etcd-dist D6)

Split from `CrashInterim.lean` (2026-11-25) so that its producer, `storage.OpenBackend`'s post
(`Spec/go_etcd_io/etcd/server/v3/storage/OpenBackend.lean`), can name it without importing the crash
laws. **Trusted** (through its producer, the axiom `storage.OpenBackend`): bbolt's `boltSyncs γ`, the database's
`NoSync`/`NoGrowSync` fields persistently `false` (concrete since 2026-11-25, plan F4; review
`notes/axiom-review/openbackend-dbopts.md`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBbolt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

open Iris Iris.BI

section preds
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors}

/-- (C-I1) **The database `γ` syncs** (persistent by its form): the bbolt database `γ` was opened with
`NoSync = false` and `NoGrowSync = false` (bbolt's fields `db.NoSync`, `db.NoGrowSync`, set by `Open`
from its options and never written again, `Inv/Bolt.lean`'s `dbFixed`), so that every `Tx.Commit`
`fdatasync`s after its pages and after its meta (`tx.go`, both under `!db.NoSync`), `DB.grow`
`fsync`s after its `Truncate` (under `!db.NoGrowSync`), and `Open` `fdatasync`s before it returns
(fork `db.go:326`). **Producer**: `storage.OpenBackend`'s post, when the configuration's
`UnsafeNoFsync` is `false` (etcd's default; `server/storage/backend.go:35` copies it into the
backend's configuration, `backend/backend.go:227-228` into `bopts.NoSync` and `bopts.NoGrowSync`,
which `bolt.Open` stores; defrag reopens the database with the same `b.bopts`, `backend.go:594`).
Never produced for defrag's temporary database (`NoSync = true`, `backend.go:531`), which no `γ` of
a backend names. Concretely bbolt's `boltSyncs γ` (`Spec/go_etcd_io/bbolt/Api.lean`): `γ`'s `DB` has both
fields `false` (persistent points-tos), which bbolt's invariant (`dbFixed`) agrees with. -/
def dbOptsRaw [hG : HeapGS hlc GF] (γ : DBNames) : IProp GF := onFs iprop(bbolt.boltSyncs γ)

/-- (C-I1) `dbOptsRaw`, persistent. -/
def dbOpts [hG : HeapGS hlc GF] (γ : DBNames) : IProp GF := iprop(<pers> dbOptsRaw γ)

instance dbOpts_persistent [hG : HeapGS hlc GF] (γ : DBNames) : Persistent (dbOpts (GF := GF) γ) := by
  unfold dbOpts; infer_instance

end preds

end backend
end EtcdGrove
end Perennial
