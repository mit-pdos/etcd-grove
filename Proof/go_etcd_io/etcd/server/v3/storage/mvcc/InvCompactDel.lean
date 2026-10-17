/-
Index-driven compaction's `del` map (`map[BucketKey]struct{}`, etcd-io/etcd#21951;
`CompactDel.lean` for the model): `BucketKey` as a map key, `delAdd` (what `keyIndex.compact`
adds), and `delSetOk` (what `treeIndex.Compact` returns: every bucket key in it is one compaction
at the revision may delete, with its tombstone mark, `DelOk`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvCompact
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.CompactDel

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section maps
variable [ext : FfiSyntax]

/-- `BucketKey`s are compared by their fields (the `del` map's keys). -/
instance bucketKey_decEq : DecidableEq BucketKey := fun a b =>
  if h : a.Revision' = b.Revision' ∧ a.tombstone' = b.tombstone' then
    isTrue (by cases a; cases b; simp only at h; rw [h.1, h.2])
  else isFalse (by intro e; subst e; exact h ⟨rfl, rfl⟩)

/-- The Go `BucketKey` of a model revision and a tombstone mark (`newBucketKey`). -/
def bkVal (r : Rev) (t : Bool) : BucketKey := BucketKey.mk (revVal r) t

/-- `keyIndex.compact`'s additions to `del`, in order. -/
def delAdd (D : GMap BucketKey Unit) (L : List (Rev × Bool)) : GMap BucketKey Unit :=
  L.foldl (fun D p => GMap.insert (bkVal p.1 p.2) () D) D

/-- **The map `treeIndex.Compact(c)` returns as `del`**: each bucket key in it is a revision
compaction at `c` may delete (of the log certified at `c`), marked a tombstone exactly when it is
one (`DelOk`). -/
def delSetOk (D : GMap BucketKey Unit) (log : Log) (c : Int) : Prop :=
  ∀ bk, (D.lookup bk).isSome → DelOk log c (revOf bk.Revision') bk.tombstone'

end maps

section inj
variable [FfiSyntax] [GoGlobalContext] [GoLocalContext] [GoSemanticsFunctions]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- A `BucketKey` value determines its fields: the `del` map's keys are compared by value. -/
instance bucketKey_intoValInj : go.IntoValInj BucketKey where
  intoVal_inj x y h := by
    have hr : ∀ z : BucketKey, is_go_step_pure (StructFieldGet BucketKey.underlying go!"Revision")
        #z = Eq (Val #(z.Revision')) := fun z =>
      (BucketKey.TypeAssumptions.get_Revision z).isGoStep_det_internal.isGoStep_pure_det
    have ht : ∀ z : BucketKey, is_go_step_pure (StructFieldGet BucketKey.underlying go!"tombstone")
        #z = Eq (Val #(z.tombstone')) := fun z =>
      (BucketKey.TypeAssumptions.get_tombstone z).isGoStep_det_internal.isGoStep_pure_det
    have e1 := hr x
    rw [h, hr y] at e1
    have e2 := ht x
    rw [h, ht y] at e2
    have f1 : Val #(x.Revision') = Val #(y.Revision') := by
      have := congrFun e1 (Val #(x.Revision')); simp only [eq_iff_iff, iff_true] at this; exact this.symm
    have f2 : Val #(x.tombstone') = Val #(y.tombstone') := by
      have := congrFun e2 (Val #(x.tombstone')); simp only [eq_iff_iff, iff_true] at this; exact this.symm
    injection f1 with f1
    injection f2 with f2
    cases x; cases y
    simp only [BucketKey.mk.injEq]
    exact ⟨go.intoVal_inj f1, GoGlobalContext.intoVal_inj_bool f2⟩

end inj

section safe
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- A `BucketKey` is a safe map key: comparing it with itself (field by field) does not panic. -/
instance bucketKey_safeMapKey (bk : BucketKey) : SafeMapKey (GF := GF) BucketKey.ty bk where
  wp_go_eq_safe_map_key s E Φ := by
    iintro HΦ
    wp_pures
    iapply HΦ

end safe

end mvcc
end EtcdGrove
end Perennial
