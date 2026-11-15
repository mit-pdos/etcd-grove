/-
## `(*batchTxBuffered).Unlock()` (`batch_tx.go:328-361`): translated

**Users.** Every session's end (the `Lock*` users above). Snippets `parts.go` (`ReqWriteThenRead`,
`ReqDeleteVisible`).

**Proof sketch.** With writes pending since the last commit: `readTx.Lock()` (the readers'
authority), `writeback` (the write buffer's puts into the read buffer, with the last commit's hook
leftovers, whose values are the committed ones: the visible image becomes the
session's puts over its base, `Sess.mid`: **the first update fires here**; the version bumped),
`readTx.Unlock()`. If the batch limit is reached or the session deleted (`pendingDeleteOperations`),
`commit(false)` (`batchTxBuffered.commit.spec`): `readTx.Lock()`, the hooks (`hookOk`, from `Pk` and
a session at the batch image whose base is `Sess.mid`: what readers see then), the old read transaction to its rollback goroutine (it waits for the
interval's readers), bbolt's commit (4c's `Tx.Commit` over its nested `commitAU`, from the
whole `boltState` the lock's invariant holds, `boltState_commit_au`; an error `lg.Fatal`s): **at its
commit update (the meta page write) the second update fires** (the visible image is the batch's: the read buffer
reset, a new read transaction at the commit), the hooks' update, then the client's commit step
(`commitOk`: the history gets the batch image); a new write transaction and read transaction. With
no commit, the session deleted nothing, so `Sess.mid`'s entries are the batch image's already and
the second update fires right after the first. The second update's target `Sess.fin` keeps `mid`'s
buffer flags (a lower bound: with a commit the buffer is in fact empty, which a later commit step
records, `beCurIs_flush`). `batchTx.Unlock` (`pending ≥ batchLimit` is false now, or
commits again the same way), the mutex released with `Pk` (the hooks' and the commit step's `Pk`
back) and the session's turn (`beTurn γ`, which the second update handed over: the lock's
invariant holds it between sessions, so the second update always fires before the next session's
`Lock*` can return a turn).

**Changes** (from `specs-ref`'s, the deleting/put session split, `relog`, `thinV`, `sbKept`, the
write-back's budget): one statement for every session: two updates of the published footprint (the
write-back's, the commit's), exact in both (`Sess.mid`), in place of a logical view kept thin of
the physical one.

verify-round (A10-provability B1): the second update's atomic precondition includes the session's
turn `beTurn γ` (from the `Lock*`), which the backend takes back at its commit point. A client that
parks lock-scoped state between sessions (mvcc's storage bridge, `MvccStorage.lean`: its batch part
taken out at the lock, put back at this update) keeps the turn with the parked state and gives it up
in the same step; a later session's turn then refutes the parked case (`beTurn_excl`).

**Margin.** What readers see between the two updates is `Sess.mid` exactly; after a commit the
buffer flags could be set (`Sess.fin` keeps them a lower bound).
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.backend.Api

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

/-- **`t.Unlock()`**: the session ends; the published cells `F` become visible in two steps (the
session's puts at the write-back, `Sess.mid`; its deletes at the commit, which a deleting session
always makes); a commit runs the hooks and the client's commit step. The second update also takes
back the session's turn. -/
def batchTxBuffered.Unlock.spec : Prop :=
  ∀ (γ : BeNames) (b : Loc) (p : GoString) (Pk : IProp GF) (q : Qp) (F : Fp) (S : Sess)
    (Ψ1 Ψ2 : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ b p Pk ∗ beSess γ q F S ∗ beLive γ (btLoc γ) 1 ∗ Pk ∗
      (AU <{ ∃∃ (V : Image), beVis γ F V }> @ ⊤, ∅ <{ beVis γ F S.mid, COMM Ψ1 }>) ∗
      (Ψ1 -∗ AU <{ ∃∃ (V : Image), beVis γ F V ∗ beTurn γ }> @ ⊤, ∅ <{ beVis γ F S.fin, COMM Ψ2 }>) }}
    (App (Val ((btLoc γ) @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered.ty @!! go!"Unlock")) (Val #()))
  {{ RET #(); beOpen γ q ∗ Ψ2 }}

end spec

end Backend
end EtcdGrove
end Perennial
