/-
`(*storeTxnWrite).End()` (`kvstore_txn.go:209`): with changes, `s.revMu.Lock()` and `currentRev++`;
`tx.Unlock()` (`keyBackend`: the batch's data made visible, the lock's invariant `Pk` back to it);
`s.revMu.Unlock()`; `s.mu.RUnlock()`. Internal: the plain store's write transaction's end (through
`metricsTxnWrite.End`: `Txn.End.contract`), and the watchable store's (3f's
`watchableStoreTxnWrite.End`, after it notified its watchers).

**Both callers, one spec.** It takes the commit's first update in a form either caller can give: its
atomic precondition admits the state at `σ₀` (the plain store: nothing notified yet, its caller's
`Txn.End` update) or already notified (`σ₀.notify pend`: the watchable store, which fired its
caller's first update itself and hands this one over trivially, `notify` being idempotent). Its
commit gives the second update (the bump), fired when `currentRev` is bumped under `s.revMu` and the
batch written back (`Unlock`'s update over `kbData`, in the same critical section: a read that sees
the new revision sees the new data). With no change, both fire with nothing changed (no bump: the
state's history `commit []` is itself). The receipt is the store's (its invariant counts its events).

**Changes** from `specs-ref`'s file: over `storeTxnWNC`, the client's state (`mvccState`) and the two
updates of the frozen API (round 9's idempotent notify); no certificates, writer fragments or tokens.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.InternalTxn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI EtcdModel EtcdWire go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- The write transaction ends: the notify step (at `σ₀` or already done), then the bump, by the
caller's updates; the reader token and the share back. -/
def storeTxnWrite.End.spec : Prop :=
  ∀ (t : Loc) (γ : MvccName) (trace : Loc) (σ₀ : MvccState) (pend : List Event) (q : Qp)
    (B : MvccStorage) (Pk Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      storeTxnWNC t γ trace σ₀ pend ∗ mvccBackend γ q B Pk ∗ Pk ∗
      AU <{ ∃∃ (σ : MvccState), mvccState γ σ }> @ ⊤ \ ↑mvccN, ∅
        <{ ⌜σ = σ₀ ∨ σ = σ₀.notify pend⌝ ∗ mvccState γ (σ.notify pend) ∗
            ⧖ (evCount (σ.kv.commit pend)), COMM
            AU <{ ∃∃ (σ' : MvccState), mvccState γ σ' }> @ ⊤ \ ↑mvccN, ∅
              <{ ⌜σ' = σ₀.notify pend⌝ ∗ mvccState γ σ'.commitPending, COMM Q }> }> }}
    (App (Val (t @!! go.GoType.PointerType storeTxnWrite.ty @!! go!"End")) (Val #()))
  {{ RET #(); mvccReaders γ 1 ∗ mvccBackend γ q B Pk ∗ Q }}

end spec
end Mvcc
end EtcdGrove
end Perennial
