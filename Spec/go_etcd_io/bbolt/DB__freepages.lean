/-
`DB.freepages` (bbolt, internal): its spec (U0b of `notes/bbolt-proof-plan.md`, a frozen
cross-unit contract). Proved by U10; used by U10 (`rollback`), U11 (`loadFreelist`). Proof:
`Proof/go_etcd_io/bbolt/DB__freepages.lean` (a `sorry` until U10).
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

/-- `db.freepages()` on the spare reader pair (as `DB.beginTx_s`): a read transaction checks the
committed tree `C` (`recursivelyCheckBucket` in a forked goroutine; it reports nothing on a
`treeOK` tree, else `freepages` panics) and is rolled back; returns the ids in `[2, hwm)` no tree
page covers, increasing (`freeIdsOf`), as a fresh slice (Go builds it by `append`: its capacity is
the caller's, which `Interface.Init` takes), with the facts `NoSyncReload` and `Init` need: the ids
increasing, at least 2, fewer than `2 ^ 63`. The premise `C.hwm ≤ 2 ^ 62` is `storeOK`'s (rollback;
`Open`: `C.hwm * 4096 ≤ size < 2 ^ 63`); the loop's `append`s need the length bound. The writer
side's quarter of the meta cells (`metaCellsQ`) is for the scan's `db.meta()` on each iteration
(no `metalock` is taken). -/
abbrev DB.freepages.spec : Prop :=
  ∀ (K : BC) (C : CommitSt) (b : Loc) (l : Nat),
  C.metaOk → treeOK C → C.hwm ≤ 2 ^ 62 →
  {{ K.core (GF := GF) ∗ sparePair K.B K.db K.sp ∗ ghostVar K.B.cur (1 : Qp).half.half C ∗
      ghostVar K.B.map (1 : Qp).half (some (b, l) : MapSt) ∗
      metaCellsQ (1 : Qp).half.half (some (b, l) : MapSt) C ∗
      K.db.[DB, go!"opened"] ↦{DFrac.own (1 : Qp).half} true }}
    (App (Val (K.db @!! go.GoType.PointerType DB.ty @!! go!"freepages")) (Val #()))
  {{ (s : GoSlice), RET #s; s ↦* freeIdsOf C ∗ ownSliceCap w64 s (DFrac.own 1) ∗
      ⌜PgidsIncr (freeIdsOf C) ∧ (∀ x ∈ freeIdsOf C, 2 ≤ x.toNat) ∧
        (freeIdsOf C).length < 2 ^ 63⌝ ∗ sparePair K.B K.db K.sp ∗
      ghostVar K.B.cur (1 : Qp).half.half C ∗ ghostVar K.B.map (1 : Qp).half (some (b, l) : MapSt) ∗
      metaCellsQ (1 : Qp).half.half (some (b, l) : MapSt) C ∗
      K.db.[DB, go!"opened"] ↦{DFrac.own (1 : Qp).half} true }}

end spec

end bbolt
end EtcdGrove
end Perennial
