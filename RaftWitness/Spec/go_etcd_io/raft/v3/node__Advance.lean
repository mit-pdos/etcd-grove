/- Lean-first (no Rocq counterpart).

## `node.Advance()` (node.go:549)

The driver, done with a `Ready` (its entries appended: the storage's receipt), hands it
back to `run` (`advancec <- struct{}{}`, `advanceP`); its token is idle again, at the
committed log handed out so far. `n.done` is never closed (`Stop` is out of scope).

(D19i part 1, 2026-10-18) And the storage's floor is at least the committed log handed out
(`storFloor`): `run` raises it at the rendezvous (`advInv`), so the application may compact
and snapshot its storage up to what it applied, before `run`'s `rn.Advance` moves `applied`.
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.InvNode

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
abbrev node.Advance.spec : Prop :=
  ∀ (γ : NodeNames) (id : w64) (n : Loc) (ds es : List EntryM) (ca : Nat)
    (cfg : CCState),
  -- (2026-10-15, stage N) **A1**, in the dynamic mode: every conf entry of the committed log
  -- handed out has been applied (`node.ApplyConfChange`): none past the driver's configuration
  -- index (`issues/raft-advance-before-applyconfchange.md`)
  (γ.mode.isDyn = true → NoConfIn ds ca ds.length) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      nodeDriverBusy γ id n ds es ∗ appendReceipt γ.stor es ∗ nodeCfg γ ca cfg }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"Advance")) (Val #()))
  {{ RET #(); nodeDriver γ id n ds ∗ nodeCfg γ ca cfg ∗
      ∃ x : w64, storFloor γ.stor x ∗ ⌜(ds.length : Int) ≤ uint.Z x⌝ }}

end spec

end EtcdGrove
end Perennial
