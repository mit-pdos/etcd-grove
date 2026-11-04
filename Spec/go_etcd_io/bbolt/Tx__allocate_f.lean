/-
`Tx.allocate` (bbolt, internal) over the flagged writer side (batch 44.1 of
`notes/bbolt-proof-plan.md`): `Tx.allocate.spec` with `wdbW' fr`/`wdbLost' fr` in place of
`wdbW`/`wdbLost`, for `Commit`'s `commitFreelist`, which allocates after the old synced freelist
page's free (`fr = true`). `Tx.allocate.spec` is its `fr = false` case. Proof:
`Proof/go_etcd_io/bbolt/Tx__allocate_f.lean` (U4c's `Mmap/TxAlloc`).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.WdbFlag
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
by a success: `allocRes_derefPre`; batch 29, U4c's corrected statement: the writer's txid is the
transaction's meta copy's, and the high-water mark's pages lie inside the mapping, before and
after; the writer side changes only by its freelist or a remap). On an error (`fmtErrorOk`): before any unmap, nothing changed; or the mapping lost
(the records dereferenced and re-based, `wtxLost`, `wdbLost`). Batch 44.1: over the flagged writer
side `wdbW' fr` (`wdbLost' fr`). -/
abbrev Tx.allocate_f.spec : Prop :=
  ∀ (fr : Bool) (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (w : WDb) (count : w64),
  0 < sint.Z count → sint.nat count * 4096 < 2 ^ 62 → X.t.mv.txid' = w.wtxid →
  X.t.mv.pgid'.toNat * 4096 ≤ mapLen w.ms → derefPre X → liveFresh X → liveReach X →
  {{ wtxW (GF := GF) K tx r m X ∗ wdbW' fr K tx X.v w }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"allocate")) (Val #count))
  {{ (p : Loc) (err : GoInterface), RET (PairV #p #err);
      (⌜err = interface.nil⌝ ∗ ∃ (X' : WX) (w' : WDb) (id : w64),
        wtxW K tx r m X' ∗ wdbW' fr K tx X'.v w' ∗
        ⌜allocRes X X' w.fl w'.fl w.wtxid (sint.nat count) p id ∧
          w'.C = w.C ∧ X'.t.mv.pgid'.toNat * 4096 ≤ mapLen w'.ms ∧
          (w' = w.withFl w'.fl ∨ wdbRemap w w')⌝) ∨
      (⌜err ≠ interface.nil⌝ ∗ fmtErrorOk err ∗
        ((wtxW K tx r m X ∗ wdbW' fr K tx X.v w) ∨
         (∃ (X' : WX) (w' : WDb), wtxLost K tx r m X' ∗ wdbLost' fr K tx X'.v w' ∗
           ⌜(∃ Xd b, derefRel X Xd ∧ X' = Xd.rebase b) ∧ w'.C = w.C ∧ w'.fl = w.fl⌝))) }}

end spec

end bbolt
end EtcdGrove
end Perennial
