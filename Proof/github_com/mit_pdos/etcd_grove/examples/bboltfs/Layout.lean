/-
The layouts of minibolt's plain types (`examples/bboltfs/page.go`: `Pgid`, `InBucket`, `Page`,
`Meta`), checked against gc's, their `IsPlain` instances (for `(*T)(unsafe.Pointer(p))`), and their
byte views (Perennial's `Golang/Theory/Unsafe.lean`): each struct is the bytes of its fields in
order. The types and their layouts are those of Perennial's `unsafememory` example
(`goose/testdata/examples/unsafememory`), and so are these proofs (its `Layout.lean`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.Bytes

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

namespace github_com.mit_pdos.etcd_grove.examples.bboltfs

/-! ## Layouts -/

section layouts
variable [GooseExts] [GoLocalContext] [GoGlobalContext] [sem : go.Semantics]
variable [package_sem : Assumptions]

theorem Pgid.layout : go.PlainLayout Pgid.ty 8 8 :=
  .named _ go.uint64 8 8 go.is_underlying (by unfold Pgid.ty go.uint64; simp)
    (.scalar _ _ .isPlainScalar_uint64)

instance Pgid.isPlain : go.IsPlain Pgid.ty 8 := ⟨8, Pgid.layout⟩

/-- `InBucket` (`root Pgid; sequence uint64`): 16 bytes, `sequence` at 8. -/
theorem InBucket.fields_layout : go.PlainLayout (go.StructType InBucket.fields) 16 8 := by
  have := Pgid.layout
  simp only [InBucket.fields, InBucket.fieldsUnsealed]
  bboltfs_plain_struct_layout

theorem InBucket.layout : go.PlainLayout InBucket.ty 16 8 :=
  .named _ _ 16 8 go.is_underlying (by unfold InBucket.ty; simp) InBucket.fields_layout

instance InBucket.isPlain : go.IsPlain InBucket.ty 16 := ⟨8, InBucket.layout⟩

/-- `Page` (`id Pgid; flags, count uint16; overflow uint32`): 16 bytes, `flags` at 8, `count` at
10, `overflow` at 12. -/
theorem Page.fields_layout : go.PlainLayout (go.StructType Page.fields) 16 8 := by
  have := Pgid.layout
  simp only [Page.fields, Page.fieldsUnsealed]
  bboltfs_plain_struct_layout

theorem Page.layout : go.PlainLayout Page.ty 16 8 :=
  .named _ _ 16 8 go.is_underlying (by unfold Page.ty; simp) Page.fields_layout

instance Page.isPlain : go.IsPlain Page.ty 16 := ⟨8, Page.layout⟩

/-- `Meta`: 64 bytes, no padding (`root` at 16, `txid` at 48, `checksum` at 56). -/
theorem Meta.fields_layout : go.PlainLayout (go.StructType Meta.fields) 64 8 := by
  have := Pgid.layout
  have := InBucket.layout
  simp only [Meta.fields, Meta.fieldsUnsealed]
  bboltfs_plain_struct_layout

theorem Meta.layout : go.PlainLayout Meta.ty 64 8 :=
  .named _ _ 64 8 go.is_underlying (by unfold Meta.ty; simp) Meta.fields_layout

instance Meta.isPlain : go.IsPlain Meta.ty 64 := ⟨8, Meta.layout⟩

end layouts

/-! ## Byte encodings: a struct is its fields' bytes in order -/

section encodings
variable [GooseExts]

instance InBucket.byteEncoding : ByteEncoding InBucket 16 :=
  ByteEncoding.ofEquiv (W := Pgid × w64) (fun v => (v.root', v.sequence'))
    (fun p => ⟨p.1, p.2⟩) (fun _ => rfl) (fun _ => rfl)

instance Page.byteEncoding : ByteEncoding Page 16 :=
  ByteEncoding.ofEquiv (W := Pgid × w16 × w16 × w32)
    (fun v => (v.id', v.flags', v.count', v.overflow'))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩) (fun _ => rfl) (fun _ => rfl)

instance Meta.byteEncoding : ByteEncoding Meta 64 :=
  ByteEncoding.ofEquiv (W := w32 × w32 × w32 × w32 × InBucket × Pgid × Pgid × w64 × w64)
    (fun v => (v.magic', v.version', v.pageSize', v.flags', v.root', v.freelist', v.pgid',
      v.txid', v.checksum'))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2⟩) (fun _ => rfl) (fun _ => rfl)

end encodings

/-! ## Byte views -/

section views
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

instance InBucket.bytesView : BytesView (GF := GF) InBucket where
  typedPointsto_bytes l v dq hl := by
    apply bytesView_of_def l v dq _ (ByteEncoding.encode_ne_nil v (by decide))
    have := Pgid.layout
    have off := structFieldRef_offset _ InBucket InBucket.fields_layout
    have o1 : go.PlainFieldOffset InBucket.fields 0 go!"root" 0 := by
      simp only [InBucket.fields, InBucket.fieldsUnsealed]; bboltfs_plain_field_offset
    have o2 : go.PlainFieldOffset InBucket.fields 0 go!"sequence" 8 := by
      simp only [InBucket.fields, InBucket.fieldsUnsealed]; bboltfs_plain_field_offset
    simp only [TypedPointsto.typedPointstoDef]
    rw [off _ _ o1 l hl, off _ _ o2 l hl]
    exact bytesView_field l 0 _ dq _ _ _ hl (bytesView_last_field l 8 _ dq _ _ hl)

instance Page.bytesView : BytesView (GF := GF) Page where
  typedPointsto_bytes l v dq hl := by
    apply bytesView_of_def l v dq _ (ByteEncoding.encode_ne_nil v (by decide))
    have := Pgid.layout
    have off := structFieldRef_offset _ Page Page.fields_layout
    have o0 : go.PlainFieldOffset Page.fields 0 go!"id" 0 := by
      simp only [Page.fields, Page.fieldsUnsealed]; bboltfs_plain_field_offset
    have o1 : go.PlainFieldOffset Page.fields 0 go!"flags" 8 := by
      simp only [Page.fields, Page.fieldsUnsealed]; bboltfs_plain_field_offset
    have o2 : go.PlainFieldOffset Page.fields 0 go!"count" 10 := by
      simp only [Page.fields, Page.fieldsUnsealed]; bboltfs_plain_field_offset
    have o3 : go.PlainFieldOffset Page.fields 0 go!"overflow" 12 := by
      simp only [Page.fields, Page.fieldsUnsealed]; bboltfs_plain_field_offset
    simp only [TypedPointsto.typedPointstoDef]
    rw [off _ _ o0 l hl, off _ _ o1 l hl, off _ _ o2 l hl, off _ _ o3 l hl]
    exact (bytesView_field l 0 _ dq _ _ _ hl
      (bytesView_field l 8 _ dq _ _ _ hl
      (bytesView_field l 10 _ dq _ _ _ hl
      (bytesView_last_field l 12 _ dq _ _ hl))))

instance Meta.bytesView : BytesView (GF := GF) Meta where
  typedPointsto_bytes l v dq hl := by
    apply bytesView_of_def l v dq _ (ByteEncoding.encode_ne_nil v (by decide))
    have := Pgid.layout
    have := InBucket.layout
    have off := structFieldRef_offset _ Meta Meta.fields_layout
    have o0 : go.PlainFieldOffset Meta.fields 0 go!"magic" 0 := by
      simp only [Meta.fields, Meta.fieldsUnsealed]; bboltfs_plain_field_offset
    have o1 : go.PlainFieldOffset Meta.fields 0 go!"version" 4 := by
      simp only [Meta.fields, Meta.fieldsUnsealed]; bboltfs_plain_field_offset
    have o2 : go.PlainFieldOffset Meta.fields 0 go!"pageSize" 8 := by
      simp only [Meta.fields, Meta.fieldsUnsealed]; bboltfs_plain_field_offset
    have o3 : go.PlainFieldOffset Meta.fields 0 go!"flags" 12 := by
      simp only [Meta.fields, Meta.fieldsUnsealed]; bboltfs_plain_field_offset
    have o4 : go.PlainFieldOffset Meta.fields 0 go!"root" 16 := by
      simp only [Meta.fields, Meta.fieldsUnsealed]; bboltfs_plain_field_offset
    have o5 : go.PlainFieldOffset Meta.fields 0 go!"freelist" 32 := by
      simp only [Meta.fields, Meta.fieldsUnsealed]; bboltfs_plain_field_offset
    have o6 : go.PlainFieldOffset Meta.fields 0 go!"pgid" 40 := by
      simp only [Meta.fields, Meta.fieldsUnsealed]; bboltfs_plain_field_offset
    have o7 : go.PlainFieldOffset Meta.fields 0 go!"txid" 48 := by
      simp only [Meta.fields, Meta.fieldsUnsealed]; bboltfs_plain_field_offset
    have o8 : go.PlainFieldOffset Meta.fields 0 go!"checksum" 56 := by
      simp only [Meta.fields, Meta.fieldsUnsealed]; bboltfs_plain_field_offset
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

end github_com.mit_pdos.etcd_grove.examples.bboltfs
end Perennial
