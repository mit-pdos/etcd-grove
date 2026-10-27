/-
`batchTxBuffered.unsafeCommit` (`batch_tx.go`). `t.unsafeCommit(stop)` under the batch lock and `readTx.mu` (held whole): the pre-commit hook (with the hooks' resource `Pk`), the interval ended (its read transaction rolled back by a goroutine once its readers are done, the shared read transaction reset), the batch transaction committed (`batchTx.commit`), and a new interval begun unless stopping. The lock's state becomes free (every put written back before: `p0 = pend`; the write buffer empty off the hook's buckets), paid by `payIn`; in an `Unlock`'s window (`win`), the clients' view comes back at the new committed data. The caller's request `X ⇒ Y` (`commitReq`; D22 the stored-index window, 2026-10-23) is served by the hook.
Lean-first (no Rocq counterpart); see `InvBatch.lean` and `InvBackend.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBatch

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

/-- `t.unsafeCommit(stop)` under the batch lock and `readTx.mu` (held whole): the pre-commit hook (with the hooks' resource `Pk`), the interval ended (its read transaction rolled back by a goroutine once its readers are done, the shared read transaction reset), the batch transaction committed (`batchTx.commit`), and a new interval begun unless stopping. The lock's state becomes free (every put written back before: `p0 = pend`; the write buffer empty off the hook's buckets), paid by `payIn`; in an `Unlock`'s window (`win`), the clients' view comes back at the new committed data. The caller's request `X ⇒ Y` (`commitReq`; D22 the stored-index window, 2026-10-23) is served by the hook. -/
abbrev backend.batchTxBuffered.unsafeCommit.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (W Pk : IProp GF) (b t rt : Loc) (st : BSess) (win stop : Bool) (m u : Nat)
    (X Y : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ P W Pk b ∗ bF go!"batchTx" b ↦□ t ∗ bF go!"readTx" b ↦□ rt ∗ batchLockedW γ P b st win ∗ Pk ∗ rtRes γ P rt 1 ∗
      ⌜sint.Z st.pend + P.hookMax < 2 ^ 58 ∧ st.cnt.p0 = sint.nat st.pend ∧ (∀ nm i, P.BT.lookup nm = some i → P.HB nm = false → bkOf st.W.bks i = []) ∧ (win = false → vData P (st.C, st.R) = sData P st.S)⌝ ∗ payIn γ st stop m u ∗ X ∗ commitReq γ P Pk b X Y }}
    (App (Val (t @!! go.GoType.PointerType batchTxBuffered.ty @!! go!"unsafeCommit")) (Val #stop))
  {{ RET #(); Y ∗ rtRes γ P rt 1 ∗ Pk ∗ payOut γ stop m ∗
      (if stop then iprop(sync.ownMutex (muOf t) ∗ pendOf t ↦ W64 0 ∗ bStopped γ)
       else iprop(∃ (st' : BSess) (db : Loc), sync.ownMutex (muOf t) ∗ batchPhys γ b t db st' ∗
         batchGhostAt γ P st' true ∗
         ⌜freeOk P st' ∧ vData P (st'.C, st'.R) = sData P st.S ∧ st'.pend = W64 0⌝ ∗
         (if win then bView γ 1 (vData P (st'.C, st'.R)) else iprop(True)))) }}

end spec

end EtcdGrove
end Perennial
