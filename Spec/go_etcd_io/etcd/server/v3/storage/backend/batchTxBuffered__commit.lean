/-
`batchTxBuffered.commit` (`batch_tx.go`). `t.commit(stop)` under the batch lock: `unsafeCommit` under `readTx.mu`.
Lean-first (no Rocq counterpart); see `InvBatch.lean` and `InvBackend.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBatch
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.ClaimedLemmas

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

/-- `t.commit(stop)` under the batch lock: `unsafeCommit` under `readTx.mu`. (A1.5 of `auth-schema-srv`, 2026-11-17) In a claimed session's `Unlock` (mode `c = true`, its claimed
writes `st.cw` among the buckets `Sc`), the commit moves the claimed buckets' readers' contents to the
writer's through the client's accessor (`rbAcc`, its resource `Rr` back); a caller in the client-facing
mode passes `[]` and the trivial accessor (`rbAcc_nil`). -/
abbrev backend.batchTxBuffered.commit.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (W Pk : IProp GF) (b t rt : Loc) (st : BSess) (win stop : Bool) (m u : Nat)
    (X Y : IProp GF) (L' : VData) (c : Bool) (Sc : List GoString) (Rr : IProp GF) (E : CoPset)
    (n : Nat) (Qw : IProp GF),
  ↑rbClaimN ⊆ E →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ P W Pk b ∗ bF go!"batchTx" b ↦□ t ∗ bF go!"readTx" b ↦□ rt ∗ batchLockedW γ P b st win c ∗ Pk ∗ ⌜sint.Z st.pend + P.hookMax < 2 ^ 58 ∧ st.cnt.p0 = sint.nat st.pend ∧ (∀ nm i, P.BT.lookup nm = some i → P.HB nm = false → bkOf st.W.bks i = []) ∧
        (∀ n, P.RB n = true → st.tk n = .idle ∨ st.tk n = .del)⌝ ∗
      (if win then thinV γ (sData P st.S) L' else thinV γ (sData P st.S) (vData P (st.C, st.R))) ∗
      ⌜win = true → st.win = true ∧ dlsOk P st L'⌝ ∗ ⌜st.cnt.hw = false⌝ ∗
      payIn γ st stop m u ∗ X ∗ commitReq γ P Pk b X Y ∗
      ⌜Sc.Nodup ∧ (c = false ∨ ∀ n, st.cw n = true → n ∈ Sc)⌝ ∗ Rr ∗
      rbAcc γ Sc (fun n _ v => v = bktOf st.S n) Rr E ∗
      -- (backend-snapshot B2) `unsafeCommit`'s: a lower bound of the commit counter, and `W` lent
      cntLb γ n ∗ (if stop then emp else if win then iprop(bView γ 1 L' -∗ W ∗ Qw) else W) }}
    (App (Val (t @!! go.GoType.PointerType batchTxBuffered.ty @!! go!"commit")) (Val #stop))
  {{ RET #(); Y ∗ Rr ∗ Pk ∗ payOut γ stop m ∗
      (if stop then iprop(sync.ownMutex (muOf t) ∗ pendOf t ↦ W64 0 ∗ bStopped γ ∗ bDBOutG γ P ∗
         -- (2026-11-06, `notes/begin-tok-plan.md`) the rollback goroutine's fork token: no new
         -- read transaction takes it at the stop
         threadTok)
       else iprop(∃ (st' : BSess) (db : Loc), sync.ownMutex (muOf t) ∗ batchPhys γ b t db st' ∗
         batchGhostAt γ P st' true ∗
         ⌜freeOk P st' ∧ vData P (st'.C, st'.R) = sData P st.S ∧ st'.pend = W64 0 ∧
           rbData P st'.S = rbData P st.S⌝ ∗
         (if win then bView γ 1 L' else iprop(True)))) ∗
      (if stop then emp else iprop(cntLb γ (n + 1) ∗
        (if win then iprop(bView γ 1 L' -∗ W ∗ Qw) else W))) }}

end spec

end EtcdGrove
end Perennial
