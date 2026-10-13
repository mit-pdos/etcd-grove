/-
`batchTx.commit` (`batch_tx.go`). `t.commit(stop)` on the writer: nothing if nothing is pending (and not stopping); else bbolt's write transaction committed (`lg.Fatal` on an error), `pending` reset, and, unless stopping, a new write transaction begun over the new committed data.
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- `t.commit(stop)` on the writer: nothing if nothing is pending (and not stopping); else bbolt's write transaction committed (`lg.Fatal` on an error), `pending` reset, and, unless stopping, a new write transaction begun over the new committed data. -/
abbrev backend.batchTx.commit.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (WR : IProp GF) (b t db : Loc) (st : BSess) (stop : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ P WR b ∗ bF go!"batchTx" b ↦□ t ∗ btW γ t st ∗ ownDB db γ.db st.C ∗ txDB st.tx db ∗ sync.ownRWMutex (bF go!"mu" b) (fun q => bF go!"db" b ↦{DFrac.own q} db) }}
    (App (Val (btOf t @!! go.GoType.PointerType batchTx.ty @!! go!"commit")) (Val #stop))
  {{ RET #(); sync.ownRWMutex (bF go!"mu" b) (fun q => bF go!"db" b ↦{DFrac.own q} db) ∗
      ((⌜st.pend = W64 0 ∧ stop = false⌝ ∗ btW γ t st ∗ ownDB db γ.db st.C ∗ txDB st.tx db) ∨
       (⌜¬ (st.pend = W64 0 ∧ stop = false)⌝ ∗ ownDB db γ.db st.S ∗ pendOf t ↦ W64 0 ∗
        ∃ tx' : Loc, txFOf t ↦ tx' ∗
          (if stop then iprop(True) else iprop(ownWTx tx' γ.db st.S st.S ∗ txDB tx' db)))) }}

end spec

end EtcdGrove
end Perennial
