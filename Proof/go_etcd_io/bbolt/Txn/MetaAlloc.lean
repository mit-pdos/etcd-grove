/-
`&common.Meta{}` at a positive address (maintainer 13, item 3: `Tx.init`'s meta copy, which
`writeMeta` views as bytes, needs `0 < addr`; `≠ null` does not give it, `Loc.addr` being an
`Int`). `struct_wp_alloc_pos` is a copy of Perennial's (in its `unsafememory` test example,
`Proof/github_com/mit_pdos/perennial/goose/testdata/examples/unsafememory/Meta.lean`), which belongs
in `Golang/Theory` (`notes/perennial-changes.md`); `Meta.wp_alloc_pos` instantiates it for
bbolt's `common.Meta`.
-/
module

public import Proof.go_etcd_io.bbolt.internal.common.Lemmas.Layout
public import GeneratedProof.go_etcd_io.bbolt.internal.common

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section alloc_pos
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [go.PreSemantics]

/-- The allocation of a struct, at a positive address (`GoPrealloc` gives one:
`wp_GoPrealloc_pos`); `struct_wp_alloc` keeps only `l ≠ null`. -/
theorem struct_wp_alloc_pos {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    {fds fds_unsealed : List go.field_decl} [EqualsUnfold fds fds_unsealed]
    [go.TypeReprUnderlying (go.StructType fds) V]
    (fs : List (StructFieldDesc (GF := GF) V (go.StructType fds)))
    (hfs : FieldsMatch fds_unsealed fs)
    (hdef : ∀ l v dq, typedPointstoDef l v dq ⊣⊢ structFieldsPointsto fs l v dq)
    {s : Stuckness} {E : CoPset} {t : go.GoType} [t ↓u go.StructType fds] (v : V) :
    {{ (True : IProp GF) }} (App (Val (GoInstruction (GoAlloc t))) (Val #v)) @ s; E
    {{ (l : Loc), RET #l; l ↦ v ∗ ⌜0 < l.addr⌝ }} := by
  iintro %Φ _ HΦ
  have hpw : PureWp (hlc := hlc) (GF := GF) ((#v : val).isPanic = false)
      (App (Val (GoInstruction (GoAlloc t))) (Val #v))
      (allocStructRaw fds #v fds_unsealed) := by
    have _tagged := @go.tagged_internal_inst
    infer_instance
  iapply (wp_pure_raw_step (Hwp := hpw) (by simp))
  inext
  rw [allocStructRaw_eq]
  wp_bind (GoPrealloc #())
  iapply wp_GoPrealloc_pos
  · itrivial
  inext
  iintro %l %Hl
  wp_pures
  rw [subst_allocFields]
  wp_bind (List.foldr _ _ _)
  iapply (struct_alloc_fields' v l s E fds_unsealed fs hfs)
  iintro Hfs
  wp_pures
  iapply HΦ
  isplitl [Hfs]
  · rw [typedPointsto_unseal]
    unfold typedPointstoWrap
    isplitl [Hfs]
    · iapply (hdef l v _).2
      iexact Hfs
    · ipureintro; intro h; subst h; simp [null] at Hl
  · ipureintro; exact Hl.1

end alloc_pos

section meta_alloc
open go_etcd_io.bbolt.internal.common
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

/-- **`&common.Meta{...}` is at a positive address.** -/
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
      StructFieldDesc.mk (V := Meta) (T := go.StructType Meta.fields) go!"txid" Txid.ty _ _ _
        (fun _ => inferInstance) (fun _ _ => inferInstance),
      StructFieldDesc.mk (V := Meta) (T := go.StructType Meta.fields) go!"checksum" go.uint64 _ _ _
        (fun _ => inferInstance) (fun _ _ => inferInstance)]
    ?_ ?_ v
  · simp only [FieldsMatch, fieldDeclName, fieldDeclType, and_self]
  · intro _ _ _; exact .rfl

end meta_alloc

end bbolt
end EtcdGrove
end Perennial
