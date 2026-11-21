/-
`batchTx.commit` (`batch_tx.go`). `t.commit(stop)` on the writer: nothing if nothing is pending (and not stopping); else bbolt's write transaction committed (`lg.Fatal` on an error), `pending` reset, and, unless stopping, a new write transaction begun over the new committed data.
Lean-first (no Rocq counterpart); see `InvBatch.lean` and `InvBackend.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.RegLemmas
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

/-- `t.commit(stop)` on the writer: nothing if nothing is pending (and not stopping); else bbolt's write transaction committed (`lg.Fatal` on an error), `pending` reset, and, unless stopping, a new write transaction begun over the new committed data. -/
abbrev backend.batchTx.commit.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (W Pk : IProp GF) (b t db : Loc) (st : BSess) (stop : Bool) (n : Nat)
    (F : IProp GF), armStep γ P W Pk γ.db.ns F st.S n →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ P W Pk b ∗ bF go!"batchTx" b ↦□ t ∗ btW γ t st ∗ ownDB db γ.db st.C ∗ txDB st.tx γ.db db ∗ sync.ownRWMutex (bF go!"mu" b) (fun q => bF go!"db" b ↦{DFrac.own q} db) ∗
      -- (backend-snapshot B1) the batch lock's quarter of the open flag (the commit point opens the
      -- commit invariant), and a stop's payment (`stopPay`: the stop's commit stops the backend);
      -- (B2) otherwise a frame `F` with which the commit point, or a no-op, arms the snapshots'
      -- registrations (`armStep`; `F` kept whole), and a lower bound of the commit counter
      dghostVar γ.opn (DFrac.own (1 : Qp).half.half) false ∗
      (if stop then stopPay γ else iprop(F ∗ cntLb γ n)) ∗
      -- (B4) a reader's lower bound of the compaction keys' flag at the writer's contents with no read
      -- buffer, which the commit point leaves in the commit invariant (for a snapshot)
      fkRd γ P (st.S, ⟨∅, W64 0⟩) ∗
      ⌜st.pend = W64 0 → st.S = st.C⌝ }}
    (App (Val (btOf t @!! go.GoType.PointerType batchTx.ty @!! go!"commit")) (Val #stop))
  {{ RET #(); sync.ownRWMutex (bF go!"mu" b) (fun q => bF go!"db" b ↦{DFrac.own q} db) ∗
      ((⌜st.pend = W64 0 ∧ stop = false⌝ ∗ btW γ t st ∗ ownDB db γ.db st.C ∗ txDB st.tx γ.db db ∗
          dghostVar γ.opn (DFrac.own (1 : Qp).half.half) false ∗ F ∗ cntLb γ (n + 1)) ∨
       (⌜¬ (st.pend = W64 0 ∧ stop = false)⌝ ∗ ownDB db γ.db st.S ∗ pendOf t ↦ W64 0 ∗
        ∃ tx' : Loc, txFOf t ↦ tx' ∗
          (if stop then iprop(bStopped γ ∗ dbHalf γ.db st.S)
           else iprop(ownWTx tx' γ.db st.S st.S ∗ txDB tx' γ.db db ∗
             dghostVar γ.opn (DFrac.own (1 : Qp).half.half) false ∗ F ∗ cntLb γ (n + 1))))) }}

end spec

end EtcdGrove
end Perennial
