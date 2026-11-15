/-
`b.begin(write)` (`backend.go:1086-1098`): translated; internal. `unsafeBegin` under `mu.RLock`, then
`tx.Size()`, `tx.DB()`, `db.Stats()` and `db.Info()`, the size and open-transaction atomics stored.

**Users.** `write = true`: `batchTx.commit` (a new write transaction after a commit) and
`newBatchTxBuffered` (through `Commit`), under the batch mutex with no write transaction
(`btStopped`); `write = false`: `batchTxBuffered.unsafeCommit` (`batch_tx.go:405`: the new read
transaction after a commit), under the batch mutex and `readTx.Lock`, the new write transaction
already begun (`btPhys γ I 0 d`: `I` is the last commit, which no commit can pass while the batch
mutex is held).

**Proof sketch.** `b.mu.RLock()`; bbolt's `Begin(write)` (4c; an error is `lg.Fatal`: excluded by
`dbBroken_state`, the last commit having succeeded); `b.mu.RUnlock()`; `tx.Size()`, `tx.DB()`;
`db.Stats()` with **`statSlot (some (tx, T))`**: the transaction's whole `boltTx`, for a read
transaction and, by 4c's `statSlot_wtx` (`T.rw = true`: the writer holds `rwlock`, and `isBolt`
keeps one spare `statlock` reader slot for it), for a write transaction (re-review N2: the law
exists).
`db.Info()` (the page size); the atomics stored. A read transaction's own reader slot is the
caller's `threadTok` (a fresh one: the thread that will roll it back gets the old read
transaction's, `wp_fork_tok_self`), held by `rtNew`.

**Changes.** verify-round (A11-completeness F4): one spec for both modes (it was stated at `#true`
only, with no account of `Stats`); `Stats`' slot named. **Margin.** The atomics' values.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.backend.Internal
public import Perennial.ProgramLogic.Bounds

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Backend

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- **`b.begin(write)`**: a bbolt transaction at the committed image (a write one under the batch
lock). -/
def backend.begin.spec : Prop :=
  ∀ (γ : BeNames) (b : Loc) (p : GoString) (Pk : IProp GF) (I : Image) (d : Nat) (w : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ b p Pk ∗ btHeld γ ∗
      (if w then btStopped γ ∗ beCommitted γ I else rtHeld γ ∗ btPhys γ I 0 d ∗ threadTok) }}
    (App (Val (b @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty @!! go!"begin")) (Val #w))
  {{ (tx : Loc), RET #tx; btHeld γ ∗
      (if w then btPhys γ I 0 d else rtHeld γ ∗ btPhys γ I 0 d ∗ rtNew γ tx I) }}

end spec

end Backend
end EtcdGrove
end Perennial
