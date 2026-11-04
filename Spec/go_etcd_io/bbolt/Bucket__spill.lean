/-
`Bucket.spill` (bbolt, internal): its spec (U0b of `notes/bbolt-proof-plan.md`, a frozen
cross-unit contract). Proved by U9b; used by U10 (`Commit`). Proof:
`Proof/go_etcd_io/bbolt/Bucket__spill.lean` (a `sorry` until U9b).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Ctx
public import Spec.fmt.ErrorOk

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

/-- **`tx.root.spill()`** (design §4.2, spill's post): from records satisfying `spillPre`, on
success the spilled tree (`spillOK`: `treeOK`, the writer's data, dropped base pages pending,
new pages allocated and written in `tx.pages`), possibly after remaps (the view re-based),
and `allocate`'s premises for `commitFreelist`'s (`derefPre`, `liveFresh`, `liveReach`; batch 12;
the high-water mark's pages inside the mapping, batch 29). On an
error (from `allocate`), a `fmtErrorOk` error, the freelist changed by free and allocation steps
only, and either the mapping intact (`wtxW`, `wdbW`) or lost (`wtxLost`, `wdbLost`). -/
abbrev Bucket.spill.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (w : WDb),
  spillPre X w.fl → liveReach X → X.t.mv.pgid'.toNat * 4096 ≤ mapLen w.ms →
  {{ wtxW (GF := GF) K tx r m X ∗ wdbW K tx X.v w }}
    (App (Val (tx.[Tx, go!"root"] @!! go.GoType.PointerType Bucket.ty @!! go!"spill")) (Val #()))
  {{ (err : GoInterface), RET #err;
      (⌜err = interface.nil⌝ ∗ ∃ (X' : WX) (w' : WDb), wtxW K tx r m X' ∗ wdbW K tx X'.v w' ∗
        ⌜spillOK X X' w.C w.fl w'.fl w.wtxid ∧ w'.C = w.C ∧
          derefPre X' ∧ liveFresh X' ∧ liveReach X' ∧
          X'.t.mv.pgid'.toNat * 4096 ≤ mapLen w'.ms⌝) ∨
      (⌜err ≠ interface.nil⌝ ∗ fmtErrorOk err ∗ ∃ (X' : WX) (w' : WDb) (st : List FLStep),
        ⌜w'.C = w.C ∧ w'.fl = w.fl.applySteps w.wtxid st ∧
          X'.v.pages = X.v.pages⌝ ∗
        ((wtxW K tx r m X' ∗ wdbW K tx X'.v w') ∨ (wtxLost K tx r m X' ∗ wdbLost K tx X'.v w'))) }}

end spec

end bbolt
end EtcdGrove
end Perennial
