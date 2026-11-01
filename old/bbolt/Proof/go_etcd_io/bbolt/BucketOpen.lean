/-
A nested bucket, opened from its value in its parent's leaf (`openBucket`): its `InBucket`
header is the value's first 16 bytes (`ibOf`, `value_inbucket`), read in place or, when the
value is not 8-aligned, in a copy; an inline bucket's page is the rest of the value.
-/
module

public import Proof.go_etcd_io.bbolt.BucketRead
public import Spec.go_etcd_io.bbolt.newBucket

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section defs
variable [ext : FfiSyntax]

/-- The `InBucket` header in a bucket value's first 16 bytes. -/
def ibOf (v : List w8) : internal.common.InBucket :=
  internal.common.InBucket.mk (W64 (inBucketRoot v : Int)) (W64 (leAt v 8 8 : Int))

/-- The bucket `openBucket` returns, of the transaction `txl`, its header at `ibl` (its inline
page right after it, for an inline bucket) and no caches (a read transaction). -/
def openedBucketOf (txl ibl : Loc) (v : List w8) : Bucket :=
  Bucket.mk ibl txl map.nil (if inBucketRoot v = 0 then ibl +ₗ 16 else null) null map.nil
    defaultFillPercent

theorem inBucketRoot_lt (v : List w8) : inBucketRoot v < 2 ^ 64 := leAt_lt v 0 8

theorem ibOf_root_zero (v : List w8) : (ibOf v).root' = W64 0 ↔ inBucketRoot v = 0 := by
  have h := inBucketRoot_lt v
  unfold ibOf; simp only
  constructor
  · intro e
    have := congrArg BitVec.toNat e
    rw [toNat_W64 _ h] at this; simpa using this
  · intro e; rw [e]; rfl

end defs

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem inBucketBytes_ibOf (v : List w8) (h : 16 ≤ v.length) :
    inBucketBytes (ibOf v) = v.take 16 := by
  unfold inBucketBytes ibOf
  simp only
  rw [toNat_W64 _ (inBucketRoot_lt v), toNat_W64 _ (leAt_lt v 8 8)]
  unfold inBucketRoot
  rw [leBytes_leAt v 0 8 (by omega), leBytes_leAt v 8 8 (by omega)]
  unfold bytesAt
  rw [List.drop_zero]
  have : v.take 16 = v.take 8 ++ (v.drop 8).take 8 := by
    rw [show (16 : Nat) = 8 + 8 from rfl, List.take_add]
  rw [this]

include package_sem in
/-- A bucket value's bytes: its header (as an `InBucket`) and the rest. -/
theorem value_inbucket (l : Loc) (dq : DFrac) (v : List w8) (h : 16 ≤ v.length)
    (hc : l.locCar ≠ 0) :
    bytesPointsto (GF := GF) l dq v ⊣⊢ l ↦{dq} ibOf v ∗ bytesPointsto (l +ₗ 16) dq (v.drop 16) := by
  have Hv : v = v.take 16 ++ v.drop 16 := (List.take_append_drop 16 v).symm
  refine (BIBase.BiEntails.of_eq (congrArg (bytesPointsto l dq) Hv)).trans ?_
  refine (bytesPointsto_app l dq _ _).trans ?_
  rw [List.length_take, Nat.min_eq_left h, ← inBucketBytes_ibOf v h]
  exact sep_congr (InBucket_bytes (hG := hG) l (ibOf v) dq hc).symm .rfl

/-- A nonempty byte slice's pointer is in a block. -/
theorem slice_car_keep (s : GoSlice) (bs : List w8) (dq : DFrac) (hne : bs ≠ []) :
    (s ↦*{dq} bs : IProp GF) ⊢ ⌜s.ptr.locCar ≠ 0⌝ ∗ s ↦*{dq} bs := by
  refine (and_intro ?_ .rfl).trans persistent_and_sep_mp
  refine (ownSlice_bytes s bs dq hne).1.trans ?_
  exact sep_elim_left.trans (bytesPointsto_car _ _ _ hne)

end lemmas

end bbolt
end EtcdGrove
end Perennial
