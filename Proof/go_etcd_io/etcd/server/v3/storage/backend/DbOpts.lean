/- Lean-first (no Rocq counterpart).

# C-I1's `dbOpts`: the database was opened syncing (etcd-dist D6)

Split from `CrashInterim.lean` (2026-11-25) so that its producer, `storage.OpenBackend`'s post
(`Spec/go_etcd_io/etcd/server/v3/storage/OpenBackend.lean`), can name it without importing the crash
laws. **Trusted**: an opaque persistent token, read only by the C-I1 axioms (`CrashInterim.lean`).
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
a backend names. Opaque, so it says nothing of the heap: only the C-I1 axioms read it. -/
opaque dbOptsRaw [hG : HeapGS hlc GF] (γ : DBNames) : IProp GF := iprop(False)

/-- (C-I1) `dbOptsRaw`, persistent. -/
def dbOpts [hG : HeapGS hlc GF] (γ : DBNames) : IProp GF := iprop(<pers> dbOptsRaw γ)

instance dbOpts_persistent [hG : HeapGS hlc GF] (γ : DBNames) : Persistent (dbOpts (GF := GF) γ) := by
  unfold dbOpts; infer_instance

end preds

end backend
end EtcdGrove
end Perennial
