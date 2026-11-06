/-
The layouts of `internal/common`'s plain types (`Pgid`, `Txid`, `InBucket`, `Page`,
`leafPageElement`, `branchPageElement`, `Meta`), their `IsPlain` instances (for
`(*T)(unsafe.Pointer(p))`), and their byte views (`Perennial/Golang/Theory/Unsafe.lean`): each
struct is the bytes of its fields in order, in the encodings of `Model/Page.lean` and
`Model/Meta.lean`. Ported from Perennial's `unsafememory/Layout.lean` (U1 of
`notes/bbolt-proof-plan.md`).
-/
module

public import Proof.go_etcd_io.bbolt.Model.Meta
public import Perennial.Golang.Theory.Unsafe

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

/-! ## Layout tactics (here rather than in `Golang/Theory/Unsafe.lean`, which would make that module
and its imports part of the precompiled `PerennialMeta` library) -/

/-- Prove `go.PlainFields fds off stop ?align` for a concrete field list, computing the alignment:
each field's layout is a scalar's or a hypothesis in the context (a named type's
`PlainLayout`). -/
macro "solve_plain_fields" : tactic => `(tactic| (
  repeat (first
    | exact go.PlainFields.nil _
    | (apply go.PlainFields.cons_ (hb := rfl)
       · dsimp only [go.fieldDeclType]
         first
         | exact go.PlainLayout.scalar _ _ inferInstance
         | assumption
       · decide))))

/-- Prove `go.PlainLayout (go.StructType fds) size align` for a concrete field list (field layouts
as in `solve_plain_fields`). -/
macro "solve_plain_struct_layout" : tactic => `(tactic| (
  apply go.PlainLayout.struct'
  · simp
  · solve_plain_fields
  · decide
  · decide))

/-- Prove `go.PlainFieldOffset fds base f off` for a concrete field list (field layouts as in
`solve_plain_fields`). -/
macro "solve_plain_field_offset" : tactic => `(tactic| (
  repeat (first
    | exact go.PlainFieldOffset.here _ _ _
    | (apply go.PlainFieldOffset.there
       · dsimp only [go.fieldDeclName]; decide
       · dsimp only [go.fieldDeclType]
         first
         | exact go.PlainLayout.scalar _ _ inferInstance
         | assumption))))

namespace go_etcd_io.bbolt.internal.common

open Perennial.EtcdGrove.bbolt

section layouts
variable [GooseExts] [GoLocalContext] [GoGlobalContext] [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

theorem Pgid.layout : go.PlainLayout Pgid.ty 8 8 :=
  .named _ go.uint64 8 8 go.is_underlying (by unfold Pgid.ty go.uint64; simp)
    (.scalar _ _ .isPlainScalar_uint64)

instance Pgid.isPlain : go.IsPlain Pgid.ty 8 := ⟨8, Pgid.layout⟩

theorem Txid.layout : go.PlainLayout Txid.ty 8 8 :=
  .named _ go.uint64 8 8 go.is_underlying (by unfold Txid.ty go.uint64; simp)
    (.scalar _ _ .isPlainScalar_uint64)

instance Txid.isPlain : go.IsPlain Txid.ty 8 := ⟨8, Txid.layout⟩

/-- `InBucket` (`root Pgid; sequence uint64`): 16 bytes, `sequence` at 8. -/
theorem InBucket.fields_layout : go.PlainLayout (go.StructType InBucket.fields) 16 8 := by
  have := Pgid.layout
  simp only [InBucket.fields, InBucket.fieldsUnsealed]
  solve_plain_struct_layout

theorem InBucket.layout : go.PlainLayout InBucket.ty 16 8 :=
  .named _ _ 16 8 go.is_underlying (by unfold InBucket.ty; simp) InBucket.fields_layout

instance InBucket.isPlain : go.IsPlain InBucket.ty 16 := ⟨8, InBucket.layout⟩

/-- `Page` (`id Pgid; flags, count uint16; overflow uint32`): 16 bytes, `flags` at 8, `count` at
10, `overflow` at 12. -/
theorem Page.fields_layout : go.PlainLayout (go.StructType Page.fields) 16 8 := by
  have := Pgid.layout
  simp only [Page.fields, Page.fieldsUnsealed]
  solve_plain_struct_layout

theorem Page.layout : go.PlainLayout Page.ty 16 8 :=
  .named _ _ 16 8 go.is_underlying (by unfold Page.ty; simp) Page.fields_layout

instance Page.isPlain : go.IsPlain Page.ty 16 := ⟨8, Page.layout⟩

/-- `leafPageElement` (four `uint32`s): 16 bytes. -/
theorem leafPageElement.fields_layout :
    go.PlainLayout (go.StructType leafPageElement.fields) 16 4 := by
  simp only [leafPageElement.fields, leafPageElement.fieldsUnsealed]
  solve_plain_struct_layout

theorem leafPageElement.layout : go.PlainLayout leafPageElement.ty 16 4 :=
  .named _ _ 16 4 go.is_underlying (by unfold leafPageElement.ty; simp)
    leafPageElement.fields_layout

instance leafPageElement.isPlain : go.IsPlain leafPageElement.ty 16 := ⟨4, leafPageElement.layout⟩

/-- `branchPageElement` (`pos, ksize uint32; pgid Pgid`): 16 bytes, `pgid` at 8. -/
theorem branchPageElement.fields_layout :
    go.PlainLayout (go.StructType branchPageElement.fields) 16 8 := by
  have := Pgid.layout
  simp only [branchPageElement.fields, branchPageElement.fieldsUnsealed]
  solve_plain_struct_layout

theorem branchPageElement.layout : go.PlainLayout branchPageElement.ty 16 8 :=
  .named _ _ 16 8 go.is_underlying (by unfold branchPageElement.ty; simp)
    branchPageElement.fields_layout

instance branchPageElement.isPlain : go.IsPlain branchPageElement.ty 16 :=
  ⟨8, branchPageElement.layout⟩

/-- `Meta`: 64 bytes, no padding (`root` at 16, `txid` at 48, `checksum` at 56). -/
theorem Meta.fields_layout : go.PlainLayout (go.StructType Meta.fields) 64 8 := by
  have := Pgid.layout
  have := Txid.layout
  have := InBucket.layout
  simp only [Meta.fields, Meta.fieldsUnsealed]
  solve_plain_struct_layout

theorem Meta.layout : go.PlainLayout Meta.ty 64 8 :=
  .named _ _ 64 8 go.is_underlying (by unfold Meta.ty; simp) Meta.fields_layout

instance Meta.isPlain : go.IsPlain Meta.ty 64 := ⟨8, Meta.layout⟩

end layouts

section views
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

instance InBucket.bytesView : BytesView (GF := GF) InBucket where
  typedPointsto_bytes l v dq hl := by
    apply bytesView_of_def l v dq _ (ByteEncoding.encode_ne_nil v (by decide))
    have := Pgid.layout
    have off := structFieldRef_offset _ InBucket InBucket.fields_layout
    have o1 : go.PlainFieldOffset InBucket.fields 0 go!"root" 0 := by
      simp only [InBucket.fields, InBucket.fieldsUnsealed]; solve_plain_field_offset
    have o2 : go.PlainFieldOffset InBucket.fields 0 go!"sequence" 8 := by
      simp only [InBucket.fields, InBucket.fieldsUnsealed]; solve_plain_field_offset
    simp only [TypedPointsto.typedPointstoDef]
    rw [off _ _ o1 l hl, off _ _ o2 l hl]
    exact bytesView_field l 0 _ dq _ _ _ hl (bytesView_last_field l 8 _ dq _ _ hl)

instance Page.bytesView : BytesView (GF := GF) Page where
  typedPointsto_bytes l v dq hl := by
    apply bytesView_of_def l v dq _ (ByteEncoding.encode_ne_nil v (by decide))
    have := Pgid.layout
    have off := structFieldRef_offset _ Page Page.fields_layout
    have o0 : go.PlainFieldOffset Page.fields 0 go!"id" 0 := by
      simp only [Page.fields, Page.fieldsUnsealed]; solve_plain_field_offset
    have o1 : go.PlainFieldOffset Page.fields 0 go!"flags" 8 := by
      simp only [Page.fields, Page.fieldsUnsealed]; solve_plain_field_offset
    have o2 : go.PlainFieldOffset Page.fields 0 go!"count" 10 := by
      simp only [Page.fields, Page.fieldsUnsealed]; solve_plain_field_offset
    have o3 : go.PlainFieldOffset Page.fields 0 go!"overflow" 12 := by
      simp only [Page.fields, Page.fieldsUnsealed]; solve_plain_field_offset
    simp only [TypedPointsto.typedPointstoDef]
    rw [off _ _ o0 l hl, off _ _ o1 l hl, off _ _ o2 l hl, off _ _ o3 l hl]
    exact (bytesView_field l 0 _ dq _ _ _ hl
      (bytesView_field l 8 _ dq _ _ _ hl
      (bytesView_field l 10 _ dq _ _ _ hl
      (bytesView_last_field l 12 _ dq _ _ hl))))

instance leafPageElement.bytesView : BytesView (GF := GF) leafPageElement where
  typedPointsto_bytes l v dq hl := by
    apply bytesView_of_def l v dq _ (ByteEncoding.encode_ne_nil v (by decide))
    have off := structFieldRef_offset _ leafPageElement leafPageElement.fields_layout
    have o0 : go.PlainFieldOffset leafPageElement.fields 0 go!"flags" 0 := by
      simp only [leafPageElement.fields, leafPageElement.fieldsUnsealed]; solve_plain_field_offset
    have o1 : go.PlainFieldOffset leafPageElement.fields 0 go!"pos" 4 := by
      simp only [leafPageElement.fields, leafPageElement.fieldsUnsealed]; solve_plain_field_offset
    have o2 : go.PlainFieldOffset leafPageElement.fields 0 go!"ksize" 8 := by
      simp only [leafPageElement.fields, leafPageElement.fieldsUnsealed]; solve_plain_field_offset
    have o3 : go.PlainFieldOffset leafPageElement.fields 0 go!"vsize" 12 := by
      simp only [leafPageElement.fields, leafPageElement.fieldsUnsealed]; solve_plain_field_offset
    simp only [TypedPointsto.typedPointstoDef]
    rw [off _ _ o0 l hl, off _ _ o1 l hl, off _ _ o2 l hl, off _ _ o3 l hl]
    exact (bytesView_field l 0 _ dq _ _ _ hl
      (bytesView_field l 4 _ dq _ _ _ hl
      (bytesView_field l 8 _ dq _ _ _ hl
      (bytesView_last_field l 12 _ dq _ _ hl))))

instance branchPageElement.bytesView : BytesView (GF := GF) branchPageElement where
  typedPointsto_bytes l v dq hl := by
    apply bytesView_of_def l v dq _ (ByteEncoding.encode_ne_nil v (by decide))
    have := Pgid.layout
    have off := structFieldRef_offset _ branchPageElement branchPageElement.fields_layout
    have o0 : go.PlainFieldOffset branchPageElement.fields 0 go!"pos" 0 := by
      simp only [branchPageElement.fields, branchPageElement.fieldsUnsealed]; solve_plain_field_offset
    have o1 : go.PlainFieldOffset branchPageElement.fields 0 go!"ksize" 4 := by
      simp only [branchPageElement.fields, branchPageElement.fieldsUnsealed]; solve_plain_field_offset
    have o2 : go.PlainFieldOffset branchPageElement.fields 0 go!"pgid" 8 := by
      simp only [branchPageElement.fields, branchPageElement.fieldsUnsealed]; solve_plain_field_offset
    simp only [TypedPointsto.typedPointstoDef]
    rw [off _ _ o0 l hl, off _ _ o1 l hl, off _ _ o2 l hl]
    exact (bytesView_field l 0 _ dq _ _ _ hl
      (bytesView_field l 4 _ dq _ _ _ hl
      (bytesView_last_field l 8 _ dq _ _ hl)))

instance Meta.bytesView : BytesView (GF := GF) Meta where
  typedPointsto_bytes l v dq hl := by
    apply bytesView_of_def l v dq _ (ByteEncoding.encode_ne_nil v (by decide))
    have := Pgid.layout
    have := InBucket.layout
    have := Txid.layout
    have off := structFieldRef_offset _ Meta Meta.fields_layout
    have o0 : go.PlainFieldOffset Meta.fields 0 go!"magic" 0 := by
      simp only [Meta.fields, Meta.fieldsUnsealed]; solve_plain_field_offset
    have o1 : go.PlainFieldOffset Meta.fields 0 go!"version" 4 := by
      simp only [Meta.fields, Meta.fieldsUnsealed]; solve_plain_field_offset
    have o2 : go.PlainFieldOffset Meta.fields 0 go!"pageSize" 8 := by
      simp only [Meta.fields, Meta.fieldsUnsealed]; solve_plain_field_offset
    have o3 : go.PlainFieldOffset Meta.fields 0 go!"flags" 12 := by
      simp only [Meta.fields, Meta.fieldsUnsealed]; solve_plain_field_offset
    have o4 : go.PlainFieldOffset Meta.fields 0 go!"root" 16 := by
      simp only [Meta.fields, Meta.fieldsUnsealed]; solve_plain_field_offset
    have o5 : go.PlainFieldOffset Meta.fields 0 go!"freelist" 32 := by
      simp only [Meta.fields, Meta.fieldsUnsealed]; solve_plain_field_offset
    have o6 : go.PlainFieldOffset Meta.fields 0 go!"pgid" 40 := by
      simp only [Meta.fields, Meta.fieldsUnsealed]; solve_plain_field_offset
    have o7 : go.PlainFieldOffset Meta.fields 0 go!"txid" 48 := by
      simp only [Meta.fields, Meta.fieldsUnsealed]; solve_plain_field_offset
    have o8 : go.PlainFieldOffset Meta.fields 0 go!"checksum" 56 := by
      simp only [Meta.fields, Meta.fieldsUnsealed]; solve_plain_field_offset
    simp only [TypedPointsto.typedPointstoDef]
    rw [off _ _ o0 l hl, off _ _ o1 l hl, off _ _ o2 l hl, off _ _ o3 l hl, off _ _ o4 l hl, off _ _ o5 l hl, off _ _ o6 l hl, off _ _ o7 l hl, off _ _ o8 l hl]
    exact (bytesView_field l 0 _ dq _ _ _ hl
      (bytesView_field l 4 _ dq _ _ _ hl
      (bytesView_field l 8 _ dq _ _ _ hl
      (bytesView_field l 12 _ dq _ _ _ hl
      (bytesView_field l 16 _ dq _ _ _ hl
      (bytesView_field l 32 _ dq _ _ _ hl
      (bytesView_field l 40 _ dq _ _ _ hl
      (bytesView_field l 48 _ dq _ _ _ hl
      (bytesView_last_field l 56 _ dq _ _ hl)))))))))

end views

end go_etcd_io.bbolt.internal.common
end Perennial
