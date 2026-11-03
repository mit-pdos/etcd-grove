/-
`Cursor.seek_w` (bbolt, internal): its spec (U0b of `notes/bbolt-proof-plan.md`, a frozen
cross-unit contract). Proved by U6; used by U7 (`Put`, `Delete`, `CreateBucket*`, `DeleteBucket`), U9 (`Bucket.spill`). Proof:
`Proof/go_etcd_io/bbolt/Cursor__seek_w.lean` (a `sorry` until U6).
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

/-- **The writer's search** (U6's search lemma as a spec): `c.seek(key)` in a searchable bucket
`bl` (any bucket of `X`, the root bucket included; `bktLocalOK`): the stack becomes a logical
path routing `key` (`lPath`, `lRoutes`; with `lRoutes_found`, it ends at `key`'s entry iff the
bucket has one), and the entry at the leaf's search index is returned (its key, value and flags,
with their sources), or nil, nil, 0 past the leaf's end. Nothing of `X` changes. -/
abbrev Cursor.seek_w.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (bl c : Loc) (stk : GoSlice)
    (els0 : List elemRef) (key : GoSlice) (kb : List w8) (ks : Src),
  bktLocalOK X bl → ks ≠ Src.stale →
  {{ wtxW (GF := GF) K tx r m X ∗ c ↦ Cursor.mk bl stk ∗ stk ↦* els0 ∗
      ownSliceCap elemRef stk (DFrac.own 1) ∗ srcOwn X.v key ks kb }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"seek")) (Val #key))
  {{ (k v : GoSlice) (fl : w32), RET (PairV (PairV #k #v) #fl);
      ∃ (stk' : GoSlice) (els : List elemRef) (pids : List w64),
      wtxW K tx r m X ∗ c ↦ Cursor.mk bl stk' ∗ stk' ↦* els ∗
      ownSliceCap elemRef stk' (DFrac.own 1) ∗ ⌜lPath X bl els pids ∧ lRoutes X bl els pids kb⌝ ∗
      (match (lLeaf X bl pids)[wsIdx (lLeaf X bl pids) kb]? with
       | some w => iprop(⌜k ≠ slice.nil ∧ fl = w.flags⌝ ∗ srcOwn X.v k w.ks w.key ∗
           srcOwn X.v v w.vs w.value)
       | none => iprop(⌜k = slice.nil ∧ v = slice.nil ∧ fl = W32 0⌝)) }}

end spec

end bbolt
end EtcdGrove
end Perennial
