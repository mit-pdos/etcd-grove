/-
**The backend's pool of reader slots** (the backend-auth-split stage, 2026-11-02; moved from the
stage's Draft, `AuthSplitDraft.lean`, decision 2: readers backed by thread tokens).

- `rdPool γ P b` (persistent): a `threadPool` of the backend's reader slots (`rdTok`), from which a
  thread token borrows one slot for one read (`rdTok_borrow`, `rdTok_giveBack`; the glue
  `reader_RLock`/`reader_RUnlock`), for the readers that hold no lock of their owner's.
- `bkRPool γ P b`: a pooled reader's resource, the pool and its `rdPoolN` slots' open shares
  (`rdOpen` each), not persistent.
- `rdAuth γ P b`: the auth store's share, `authRdN` slots (the auth-on snapshot plan's N4,
  2026-11-03: the store's reader resource a ticket, backed by these slots of each backend); their
  open shares travel with the pool's (`bkRPool`).
- `rdStock γ P b`: the `rdStockN` slots the constructor's post leaves counted past the pool and the
  auth share.
- `newPost_pool`/`newPostK_pool`: the constructor's post with its slots split into the pool and
  the stock (`newPostP`, `newPostKP`), for a thread bound within the pool.

What the partition counts (2026-11-06, `notes/axiom-review/authrdn-count.md`, attack 6): the
`actualMaxReaders` slots are the `readTx.mu` read locks taken with an `rdTok` (every one the verified
backend code takes, and those of the auth store's tickets), not every Go reader of `readTx.mu`.
`EtcdServer.monitorStorageVersion`'s goroutine read-locks it (`StorageVersion` →
`schema.DetectSchemaVersion`, `schema.go:85-88`) without one: its spec (`srvSVRes`) holds no
`rdTok`, so Go's `readTx.mu` can have one reader more than the slots count. Go's limit
(`2 ^ 30 - 1` readers) is still not reached: each reader is a live goroutine, at most the thread
bound (`≤ 2 ^ 28` in every closed theorem through `NewServer`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBackend
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.Model2
public import Spec.go_uber_org.zap.Defs
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.DelKeys
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast
public import Perennial.Ghost.SavedProp
public import Perennial.Proof.ThreadPool
public import Perennial.ProgramLogic.Bounds

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend

/-- The size of the backend's reader pool: the thread bound the server fixes (`NewServer`'s
`threadBound GF ≤ 2 ^ 28`, J8a-6). -/
@[word_unfold] def rdPoolN : Nat := 2 ^ 28

/-- **The auth store's share of a backend's reader slots** (the auth-on snapshot plan's N4,
2026-11-03): the auth store's reader resource is a ticket, of which the server hands out at most
`authRdN` copies, each backed by one of these slots of the backend current when it is redeemed.
(revoke-open Q6 (a), 2026-11-06: `rdPoolN` more, until then `2 ^ 7`, for the revocation's inner
pool's copies of the server's `E.RD`, a pool's worth (`srvRevokePoolN = rdPoolN - 1`); written over
`rdPoolN` since review round 1, NIT 3.6, so that the two stay in step. A backend constant sized by a
consumer two packages up, the server.) -/
@[word_unfold] def authRdN : Nat := rdPoolN + 2 ^ 7

/-- The reader slots the constructor's post leaves counted, past the pool's `rdPoolN` and the auth
share's `authRdN`. (Irreducible, 2026-11-02: a unifier unfolding it would evaluate `Nat.sub` by
`2 ^ 28` steps; its value is `rdStockN_val`.) -/
@[irreducible] def rdStockN : Nat := Int.toNat sync.rwmutex.actualMaxReaders - rdPoolN - authRdN

section pool
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

end pool

section poolLC
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

end poolLC

end backend
end EtcdGrove
end Perennial
