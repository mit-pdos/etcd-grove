/-
`node.put` (bbolt, internal): its spec (U0b of `notes/bbolt-proof-plan.md`, a frozen
cross-unit contract). Proved by U7; used by U7 (`Put`, `CreateBucket*`), U9 (`node.spill`'s `parent.put`, `Bucket.spill`'s header puts). Proof:
`Proof/go_etcd_io/bbolt/node__put.lean` (a `sorry` until U7).
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

/-- `n.put(oldKey, newKey, value, pgId, flags)` on a live node of the writer's heap (its object
at `1`, `objOwn`) whose entries are sorted and not stale: at the search index of `oldKey`, the
entry `⟨flags, pgId, newKey, value⟩` replaces the one of key `oldKey`, or is inserted there
(`wsPutAt`; the inodes may move: a new slice `s`). The new entry's bytes are `newKey`'s and
`value`'s with their sources (`srcOwn`, persistent: view bytes or heap bytes `↦*□`), which the
node keeps; `oldKey`'s and the entries' keys are read through the view's cells (`viewCells`, any
fraction). It reads `n.bucket.tx.meta.pgid` (fractions of the three). It panics if `pgId` is not
below that high-water mark or a key is empty: excluded by the premises. -/
abbrev node.put.spec : Prop :=
  ∀ (v : View) (n bl : Loc) (r : NRec) (tx mp : Loc) (mv : Meta) (dqb : DFrac) (qv : Qp)
    (oldKey newKey value : GoSlice) (okb nkb vb : List w8) (oks nks vs : Src) (pgId : w64)
    (flags : w32),
  r.nv.bucket' = bl → wsSorted r.ws → wsLive r.ws → pgId.toNat < mv.pgid'.toNat →
  0 < okb.length → 0 < nkb.length → oks ≠ Src.stale → nks ≠ Src.stale → vs ≠ Src.stale →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗
      objOwn v n (DFrac.own 1) true (WObj.node bl r) ∗ viewCells qv v ∗
      bl.[Bucket, go!"tx"] ↦{dqb} tx ∗ tx.[Tx, go!"meta"] ↦{dqb} mp ∗ mp ↦{dqb} mv ∗
      srcOwn v oldKey oks okb ∗ srcOwn v newKey nks nkb ∗ srcOwn v value vs vb }}
    (App (App (App (App (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"put"))
      (Val #oldKey)) (Val #newKey)) (Val #value)) (Val #pgId)) (Val #flags))
  {{ RET #(); ∃ (s : GoSlice) (ins : List Inode),
      objOwn v n (DFrac.own 1) true
        (WObj.node bl (r.withEnts s ins (wsPutAt r.ws okb ⟨flags, pgId, nkb, vb, nks, vs⟩))) ∗
      viewCells qv v ∗
      bl.[Bucket, go!"tx"] ↦{dqb} tx ∗ tx.[Tx, go!"meta"] ↦{dqb} mp ∗ mp ↦{dqb} mv }}

end spec

end bbolt
end EtcdGrove
end Perennial
