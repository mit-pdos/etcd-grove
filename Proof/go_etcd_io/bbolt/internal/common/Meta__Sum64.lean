/-
`(*Meta).Sum64`'s proof (`internal/common/meta.go`): `fnv.New64a()`, then `Write` of the
meta's first 56 bytes (a `*[56]byte` view of `*m`, sliced) and `Sum64`, through the `hash.Hash64`
interface, by the specs of `hash/fnv` (`Spec/hash/fnv/`); `metaSum` is the model's FNV-1a 64.
-/
module

public import Spec.go_etcd_io.bbolt.internal.common.Meta__Sum64
public import Spec.hash.fnv.New64a
public import Spec.hash.fnv.sum64a__Write
public import Spec.hash.fnv.sum64a__Sum64
public import Proof.go_etcd_io.bbolt.internal.common.Lemmas.Layout
public import Proof.go_etcd_io.bbolt.internal.common.Lemmas.Bytes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt
namespace internal
namespace common

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

/-- `*[56]byte`, the view `Sum64` hashes, points to a plain array (the conversion from
`unsafe.Pointer` has a rule). -/
instance metaPrefixArray_isPlain : go.IsPlain (go.GoType.ArrayType 56 go.byte) (56 * 1) :=
  ⟨1, .array 56 go.byte 1 1 (.scalar _ _ .isPlainScalar_uint8) (by decide)⟩

theorem Meta.Sum64.wp_proof
    (wp_New64a : hash.fnv.New64a.spec (GF := GF) (hG := hG))
    (wp_Write : hash.fnv.sum64a.Write.spec (GF := GF) (hG := hG))
    (wp_Sum64 : hash.fnv.sum64a.Sum64.spec (GF := GF) (hG := hG)) :
    Meta.Sum64.spec (GF := GF) (hG := hG) := by
  intro l v dq Hl0
  wp_start as Hl
  wp_auto
  wp_apply wp_New64a as %lh Hh
  have e0 : arrayIndexRef w8 (sint.Z (W64 0)) l = l := go.arrayIndexRef_0 _ _
  have e56 : (W64 56 - W64 0 : w64) = W64 ((((encode v).take 56).length : Nat) : Int) := by
    rw [List.length_take, ByteEncoding.encode_length]; rfl
  rw [e0, e56]
  have hsplit := bytesPointsto_app (GF := GF) l dq ((encode v).take 56) ((encode v).drop 56)
  rw [List.take_append_drop] at hsplit
  icases (typedPointsto_bytes l v dq Hl0).1 $$ Hl with Hl
  icases hsplit.1 $$ Hl with ⟨Hp, Hrest⟩
  icases (bytesPointsto_ownSlice l dq _ Hl0 (by
    rw [List.length_take, ByteEncoding.encode_length]; decide)).1 $$ Hp with Hp
  wp_apply wp_Write $$ [Hh Hp] as ⟨Hh, Hp⟩
  · iframe
  try wp_auto
  wp_apply wp_Sum64 $$ Hh as Hh
  try wp_auto
  icases (bytesPointsto_ownSlice l dq _ Hl0 (by
    rw [List.length_take, ByteEncoding.encode_length]; decide)).2 $$ Hp with Hp
  icases hsplit.2 $$ [Hp Hrest] with Hl
  · iframe
  icases (typedPointsto_bytes l v dq Hl0).2 $$ Hl with Hl
  rw [show hash.fnv.fnv64aFrom hash.fnv.fnv64aOffset ((encode v).take 56) = metaSum v from rfl]
  iapply HΦ
  iexact Hl

end proof

end common
end internal
end bbolt
end EtcdGrove
end Perennial
