/-
`RLock` (the backend), begun while the client holds an idle part of the tracked buckets: the
readers' view on those buckets is the part's contents. Lean-first (no Rocq counterpart); the
authstore-noax stage (2026-11-18, `notes/decisions.md`, "authstore-noax"): what the auth store's
`Recover` needs of a new backend's read transaction. A second triple of `readTx.RLock` (its proved
one is `backend.readTx.RLock.spec`): the backend's read model does not yet relate the readers'
view of a hook's bucket to the writer's contents (the auth-schema-srv Scope's G1,
`notes/auth-schema-srv-scope.md`), so this is the trust boundary until it does.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBackend

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.backend backend

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- `rt.RLock()` of the shared read transaction (as `backend.readTx.RLock.spec`), by a client
holding **the idle part of the tracked buckets `S` at `r`** (`rbOwnIn γ S r`, kept): the readers'
state `rv` it holds reads `r` on `S` (each key of a bucket of `S`: `r`'s value, none if `r` has the
bucket absent or the key absent).

Go (at the etcd pin): `RLock` read-locks `readTx.mu` (`read_tx.go:101`); the readers' state is the
read buffer over bbolt's read transaction of the last commit (`baseReadTx.buf`, `tx`). The part is
idle: since the last `batchTxBuffered.Unlock` handed it (which makes it idle,
`batchTxBuffered.Unlock.spec`), no session has put in, deleted from, created or deleted a bucket of
`S` (each needs the part). That `Unlock` wrote the session's buffered puts back into the read buffer
(`batch_tx.go:328-357`, under `readTx.Lock()`, keeping each key's last put, `tx_buffer.go:96-115`),
and, when a delete was pending, committed (`pendingDeleteOperations > 0`, etcd-io/etcd#17119:
`commit` resets the read transaction to bbolt's new committed state and empties the read buffer,
under `readTx.Lock()`), so when it returned the readers' state read the writer's contents on `S`.
Later write-backs and commits (other sessions', the `run` goroutine's periodic commit, `Commit`,
`ForceCommit`, defragmentation) move only what the writer's contents already hold, which on `S` is
`r` (the hook's own keys are `Meta`'s, not the client's buckets'); and both take `readTx.Lock()`,
which excludes the holders of `readTx.mu`'s read lock, so the state `RLock` acquires is fixed until
`RUnlock`. The same reasoning as the trusted readers that take an idle part
(`membershipBackend.MustReadMembersFromBackend.spec`, `TestBksNewAuthStoreIdle`). -/
abbrev backend.readTx.RLock.specIdle : Prop :=
  ∀ (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) (rt : Loc) (qo : Qp)
    (S : GoString → Prop) (r : GMap GoString BktData),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ P W Pk b ∗
      bF go!"readTx" b ↦□ rt ∗ rdTok γ P b ∗ bOpen γ qo ∗ rbOwnIn γ S r }}
    (App (Val (rt @!! go.GoType.PointerType readTx.ty @!! go!"RLock")) (Val #()))
  {{ RET #(); ∃ (rtx : Loc) (rv : RView), rtHeld γ P b rtx rv ∗ bOpen γ qo ∗ rbOwnIn γ S r ∗
      ⌜∀ n, S n → ∀ k, vOf P rv n k = ((r.lookup n).getD ∅).lookup k⌝ }}

end spec

end EtcdGrove
end Perennial
