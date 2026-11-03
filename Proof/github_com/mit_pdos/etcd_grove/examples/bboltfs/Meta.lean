/-
Facts for minibolt's `Meta` (`examples/bboltfs/page.go`): the checksum `sum64` computes, what
`validate` checks, and the meta `pickMeta` picks.

`metaSum v` is `sum64`'s result: FNV-64a (Perennial's `unsafememory` example's `fnv64`, the same
loop) over the first 56 bytes of `v`, all but the checksum. It does not depend on the checksum
(`metaSum_with_checksum`). `metaValid v` is what `validate` checks: the magic, the version, and a
checksum equal to `metaSum v`; a meta whose checksum is set to `metaSum` is valid when its magic
and version are (`metaValid_withSum`). `pickMetaRes` is `pickMeta`'s choice. `[56]byte`, the array
`sum64` views the `Meta` as, is plain (`byteArray56.isPlain`), and `Meta.wp_alloc_pos` allocates a
`Meta` at a positive address, where it has a byte view.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.Layout

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace github_com.mit_pdos.etcd_grove.examples.bboltfs


/-! ## The checksum of a `Meta` -/

section meta_bytes
variable [GooseExts]

/-- `Meta.sum64`'s result for a `Meta` `v`: FNV-64a over its bytes before `checksum` (56 of its
64). -/
def metaSum (v : Meta) : w64 := fnv64 ((encode v).take 56)

/-- The bytes of a `Meta` before its checksum are those of its other fields. -/
theorem Meta.encode_take (v : Meta) :
    (encode v).take 56 = encode (v.magic', v.version', v.pageSize', v.flags', v.root',
      v.freelist', v.pgid', v.txid') := by
  have e : encode v = encode (v.magic', v.version', v.pageSize', v.flags', v.root', v.freelist',
      v.pgid', v.txid') ++ encode v.checksum' := by
    show encode (v.magic', v.version', v.pageSize', v.flags', v.root', v.freelist', v.pgid',
      v.txid', v.checksum') = _
    simp only [ByteEncoding.prod_encode, List.append_assoc]
  rw [e, List.take_left' (by rw [ByteEncoding.encode_length])]

/-- The checksum does not cover itself. -/
theorem metaSum_with_checksum (v : Meta) (c : w64) :
    metaSum { v with checksum' := c } = metaSum v := by
  simp only [metaSum, Meta.encode_take]

/-- What `validate` checks: the magic (`0xED0CDAED`), the version (2), and the checksum. -/
def metaValid (v : Meta) : Prop :=
  v.magic' = W32 0xED0CDAED ∧ v.version' = W32 2 ∧ v.checksum' = metaSum v

instance metaValid.decidable (v : Meta) : Decidable (metaValid v) := by
  unfold metaValid; infer_instance

/-- A meta with the right magic and version, its checksum set (`write`, `initPages`), is valid. -/
theorem metaValid_withSum (v : Meta) (hm : v.magic' = W32 0xED0CDAED) (hv : v.version' = W32 2) :
    metaValid { v with checksum' := metaSum v } :=
  ⟨hm, hv, (metaSum_with_checksum v _).symm⟩

end meta_bytes

/-! ## `pickMeta`'s choice -/

section pick
variable [GooseExts]

/-- The first of `a` and `b` whose meta is valid, or nil. -/
def pickValid (a : Loc) (va : Meta) (b : Loc) (vb : Meta) : Loc :=
  if metaValid va then a else if metaValid vb then b else null

/-- `pickMeta(m0, m1)` of metas `v0`, `v1`: the valid one with the higher txid (`m0` on a tie), or
the other if only it is valid, or nil. -/
def pickMetaRes (m0 : Loc) (v0 : Meta) (m1 : Loc) (v1 : Meta) : Loc :=
  if uint.Z v0.txid' < uint.Z v1.txid' then pickValid m1 v1 m0 v0 else pickValid m0 v0 m1 v1

end pick

/-- `[56]byte`, the bytes `sum64` views (`(*[unsafe.Offsetof(Meta{}.checksum)]byte)(...)`), is
plain. -/
instance byteArray56.isPlain [GooseExts] [GoSemanticsFunctions] :
    go.IsPlain (go.ArrayType 56 go.byte) 56 :=
  ⟨1, .array 56 go.byte 1 1 (.scalar _ _ .isPlainScalar_uint8) (by decide)⟩

section meta_alloc
open Iris Iris.BI Iris.ProgramLogic Iris.Std
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

/-- `&Meta{...}` (or a `Meta` local) is at a positive address, so its bytes can be viewed
(`Meta.bytesView`). -/
theorem Meta.wp_alloc_pos {s : Stuckness} {E : CoPset} (v : Meta) :
    {{ (True : IProp GF) }} (App (Val (GoInstruction (GoAlloc Meta.ty))) (Val #v)) @ s; E
    {{ (l : Loc), RET #l; l ↦ v ∗ ⌜0 < l.addr⌝ }} := by
  refine struct_wp_alloc_pos (fds := Meta.fields) (fds_unsealed := Meta.fieldsUnsealed)
    [StructFieldDesc.mk (V := Meta) (T := go.StructType Meta.fields) go!"magic" go.uint32 _ _ _
        (fun _ => inferInstance) (fun _ _ => inferInstance),
      StructFieldDesc.mk (V := Meta) (T := go.StructType Meta.fields) go!"version" go.uint32 _ _ _
        (fun _ => inferInstance) (fun _ _ => inferInstance),
      StructFieldDesc.mk (V := Meta) (T := go.StructType Meta.fields) go!"pageSize" go.uint32 _ _ _
        (fun _ => inferInstance) (fun _ _ => inferInstance),
      StructFieldDesc.mk (V := Meta) (T := go.StructType Meta.fields) go!"flags" go.uint32 _ _ _
        (fun _ => inferInstance) (fun _ _ => inferInstance),
      StructFieldDesc.mk (V := Meta) (T := go.StructType Meta.fields) go!"root" InBucket.ty _ _ _
        (fun _ => inferInstance) (fun _ _ => inferInstance),
      StructFieldDesc.mk (V := Meta) (T := go.StructType Meta.fields) go!"freelist" Pgid.ty _ _ _
        (fun _ => inferInstance) (fun _ _ => inferInstance),
      StructFieldDesc.mk (V := Meta) (T := go.StructType Meta.fields) go!"pgid" Pgid.ty _ _ _
        (fun _ => inferInstance) (fun _ _ => inferInstance),
      StructFieldDesc.mk (V := Meta) (T := go.StructType Meta.fields) go!"txid" go.uint64 _ _ _
        (fun _ => inferInstance) (fun _ _ => inferInstance),
      StructFieldDesc.mk (V := Meta) (T := go.StructType Meta.fields) go!"checksum" go.uint64 _ _ _
        (fun _ => inferInstance) (fun _ _ => inferInstance)]
    ?_ ?_ v
  · simp only [FieldsMatch, fieldDeclName, fieldDeclType, and_self]
  · intro _ _ _; exact .rfl

end meta_alloc

end github_com.mit_pdos.etcd_grove.examples.bboltfs

end Perennial
