/-
`Tx.close_w` (bbolt, internal): its spec (U0b of `notes/bbolt-proof-plan.md`, a frozen
cross-unit contract). Proved by U5; used by U5 (`Rollback`), U10 (`Commit`, `rollback`). Proof:
`Proof/go_etcd_io/bbolt/Tx__close_w.lean` (U5c's, batch 34).
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
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **`tx.close()` of a writer** (design §4.2's three cases): before the publish (nothing pending
for it: its `Rollback` ran), after it (`pub`), or after a failed remap (no mapping, its view
parked); a lent view is the records' (`wl = true → v = X.v`, batch 34: `store_wclose` takes its
cells, which `wtxW` holds at `X.v`). It reads the freelist's counts, clears `db.rwtx`, unlocks
`rwlock` (its resource back: `store_wclose`, the writer side idle), adds its statistics to the
database's under `statlock`; the transaction is done. -/
abbrev Tx.close_w.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (r : TxReg) (X : WX) (ws : WSt) (w : WDb),
  (∃ v wt pb wl, ws = (some v, some wt, pb, wl) ∧
    (pb = true ∨ w.fl.pending !! W64 (wt : Int) = none) ∧ (wl = true ↔ w.ms ≠ none) ∧
    (wl = true → v = X.v)) →
  {{ wtxEnd (GF := GF) K tx r X ws w }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"close")) (Val #()))
  {{ RET #(); txDoneDef tx }}

end spec

end bbolt
end EtcdGrove
end Perennial
