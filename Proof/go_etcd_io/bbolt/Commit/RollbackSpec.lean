/-
`tx.rollback()` of a writer (U10d of `notes/bbolt-proof-plan.md`; design §3.11, "Commit's error
paths"): its spec, for `Commit`'s error paths and `commitFreelist`'s. Proof:
`Proof/go_etcd_io/bbolt/Tx__rollback.lean`.
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Ctx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **When a writer may roll back** (`Tx.close_w.spec`'s cases, without its "nothing pending"
clause, which the rollback establishes): the store's writer state is live for the txid `wt`, the
records' `tx.meta.txid`; a lent view is the records'; and a publish happened only while mapped
(`writeMeta` never unmaps). -/
def rbOK (X : WX) (ws : WSt) (w : WDb) : Prop :=
  ∃ v wt pb wl, ws = (some v, some wt, pb, wl) ∧ X.t.mv.txid' = W64 (wt : Int) ∧
    (wl = true ↔ w.ms ≠ none) ∧ (wl = true → v = X.v) ∧ (pb = true → w.ms ≠ none)

/-- **`tx.rollback()` of a writer** (design §3.11): from a write transaction ready to close
(`wtxEnd`). If the meta page was published (`meta().Txid()` is the writer's: the commit point
passed), it only closes (the fork's `2d39641`: the freed pages stay pending). Otherwise it rolls
the freelist back (`freelist.Rollback`, `store_rollback`), reloads it if mapped (`Reload` of the
synced freelist page, or `NoSyncReload(db.freepages())`, a read transaction on the spare pair),
and closes. The transaction is done. -/
abbrev Tx.rollback.spec : Prop :=
  ∀ [HasExt osFsExt] (K : BC) (tx : Loc) (r : TxReg) (X : WX) (ws : WSt) (w : WDb),
  rbOK X ws w →
  {{ wtxEnd (GF := GF) K tx r X ws w }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"rollback")) (Val #()))
  {{ RET #(); txDoneDef tx }}

end spec

end bbolt
end EtcdGrove
end Perennial
