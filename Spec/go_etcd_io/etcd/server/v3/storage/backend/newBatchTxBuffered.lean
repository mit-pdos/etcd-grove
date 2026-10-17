/-
`newBatchTxBuffered` (`batch_tx.go`). `newBatchTxBuffered(b)`, from `newBackend`, before the
backend's invariants exist: a batch transaction with empty buffers, and its first `Commit`,
which (no transaction open yet, no hooks yet) only begins bbolt's write transaction and the
read side's read transaction. Its pre is what `newBackend` has made at that point: the backend's
fields (owned), `readTx.mu` initialized but not yet a guard (`rwmutex.isRWMutex` with its state,
unlocked), `b.mu`'s guard with a reader's slot, the metrics' invariant, bbolt's database open.
Lean-first (no Rocq counterpart); 2026-10-17, branch `construct` (the backend's constructor).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.BeginCtx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.backend backend

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- `newBatchTxBuffered(b)` on a backend being constructed: the batch transaction `t` (its lock
free, its buffers empty, nothing pending) after its first commit, which began bbolt's write
transaction `wtx` and the read side's read transaction `rtx` over the database's data `D`. -/
abbrev backend.newBatchTxBuffered.spec : Prop :=
  ∀ (b rt db : Loc) (lim : w64) (γrw : sync.rwmutex.RWMutexNames) (γd : DBNames) (D : Data),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      beginCtx b ∗ bF go!"readTx" b ↦□ rt ∗ bF go!"batchLimit" b ↦□ lim ∗ ⌜0 < sint.Z lim⌝ ∗
      bF go!"hooks" b ↦ (GoInterface.nil : Hooks) ∗ rtxOf (baseOf rt) ↦ Loc.null ∗
      sync.rwmutex.isRWMutex (rmuOf (baseOf rt)) γrw (nroot.@"rw") ∗
      sync.rwmutex.ownRWMutex γrw (rwmutex.RLocked 0) ∗
      sync.ownRWMutex (bF go!"mu" b) (fun q => bF go!"db" b ↦{DFrac.own q} db) ∗
      ownDB db γd D ∗ wrTok γd }}
    (App (Val (@! newBatchTxBuffered)) (Val #b))
  {{ (t : Loc), RET #t; ∃ (wtx rtx : Loc),
      muOf t ↦ (false : Bool) ∗ txFOf t ↦ wtx ∗ pendOf t ↦ (W64 0) ∗ delOf t ↦ (W64 0) ∗
      ownWB (wbOf t) ⟨∅, ∅⟩ ∗ beOf t ↦□ b ∗
      bF go!"hooks" b ↦ (GoInterface.nil : Hooks) ∗ rtxOf (baseOf rt) ↦ rtx ∗
      sync.rwmutex.ownRWMutex γrw (rwmutex.RLocked 0) ∗
      sync.ownRWMutex (bF go!"mu" b) (fun q => bF go!"db" b ↦{DFrac.own q} db) ∗
      ownDB db γd D ∗ ownWTx wtx γd D D ∗ txDB wtx db ∗
      txLive rtx 1 ∗ rtxSnap rtx D ∗ rtxStats rtx ∗ txDB rtx db }}

end spec

end EtcdGrove
end Perennial
