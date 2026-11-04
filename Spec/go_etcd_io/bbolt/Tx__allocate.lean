/-
`Tx.allocate` (bbolt, internal): its spec (U0b of `notes/bbolt-proof-plan.md`, a frozen
cross-unit contract). Proved by U4; used by U9b (`node.spill`), U10 (`commitFreelist`). Proof:
`Proof/go_etcd_io/bbolt/Tx__allocate.lean` (a `sorry` until U4).
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

/-- **`tx.allocate(count)`** (design §4.2): a buffer of `count` pages for the writer, from the
freelist or at the high-water mark (`allocRes`; a `store_alloc` step), added to `tx.pages`; the
mapping grown first if need be (a remap: `dereference`, `munmap`, `mmap`, the view re-based,
`wdbRemap`; `derefPre`, `liveFresh`, `liveReach` are `dereference`'s premises, batch 12, kept
by a success: `allocRes_derefPre`). On an error (`fmtErrorOk`): before any unmap, nothing changed; or the mapping lost
(the records dereferenced and re-based, `wtxLost`, `wdbLost`). -/
abbrev Tx.allocate.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (w : WDb) (count : w64),
  0 < sint.Z count → sint.nat count * 4096 < 2 ^ 62 → derefPre X → liveFresh X → liveReach X →
  {{ wtxW (GF := GF) K tx r m X ∗ wdbW K tx X.v w }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"allocate")) (Val #count))
  {{ (p : Loc) (err : GoInterface), RET (PairV #p #err);
      (⌜err = interface.nil⌝ ∗ ∃ (X' : WX) (w' : WDb) (id : w64),
        wtxW K tx r m X' ∗ wdbW K tx X'.v w' ∗
        ⌜allocRes X X' w.fl w'.fl w.wtxid (sint.nat count) p id ∧
          w'.C = w.C ∧ (X'.v = X.v → w' = w.withFl w'.fl) ∧
          (X'.v ≠ X.v → wdbRemap w w')⌝) ∨
      (⌜err ≠ interface.nil⌝ ∗ fmtErrorOk err ∗
        ((wtxW K tx r m X ∗ wdbW K tx X.v w) ∨
         (∃ (X' : WX) (w' : WDb), wtxLost K tx r m X' ∗ wdbLost K tx X'.v w' ∗
           ⌜(∃ Xd b, derefRel X Xd ∧ X' = Xd.rebase b) ∧ w'.C = w.C ∧ w'.fl = w.fl⌝))) }}

end spec

end bbolt
end EtcdGrove
end Perennial
