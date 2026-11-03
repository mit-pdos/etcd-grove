/-
Byte facts minibolt's proofs share, copied from Perennial's `unsafememory` example (its `Meta.lean`
and `Pages.lean`): FNV-1a (`fnv64`, the hash `Meta.sum64` computes), the bounds of a byte points-to
(`bytesPointsto_in_bounds`), and a byte slice over a byte points-to (`bytesPointsto_ownSlice`), and the allocation of a struct
at a positive address (`struct_wp_alloc_pos`).

Copied, not imported: the example's proof modules import `Perennial.Proof.time.Base`, and so
Perennial's channel theory, whose `Perennial.wp_Close` clashes with the Linux file extension's
(`GooseLang/Ext/OsFs/Specs.lean`), which minibolt's proofs import as well.
-/
module

public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.bboltfs
public import Perennial.Golang.Theory.Unsafe
public import Perennial.Golang.Theory.Plain

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

/-! ## Layout tactics (Perennial's `unsafememory` example's, renamed) -/

/-- Prove `go.PlainFields fds off stop ?align` for a concrete field list, computing the alignment:
each field's layout is a scalar's or a hypothesis in the context (a named type's
`PlainLayout`). -/
macro "bboltfs_plain_fields" : tactic => `(tactic| (
  repeat (first
    | exact go.PlainFields.nil _
    | (apply go.PlainFields.cons_ (hb := rfl)
       · dsimp only [go.fieldDeclType]
         first
         | exact go.PlainLayout.scalar _ _ inferInstance
         | assumption
       · decide))))

/-- Prove `go.PlainLayout (go.StructType fds) size align` for a concrete field list (field layouts
as in `bboltfs_plain_fields`). -/
macro "bboltfs_plain_struct_layout" : tactic => `(tactic| (
  apply go.PlainLayout.struct'
  · simp
  · bboltfs_plain_fields
  · decide
  · decide))

/-- Prove `go.PlainFieldOffset fds base f off` for a concrete field list (field layouts as in
`bboltfs_plain_fields`). -/
macro "bboltfs_plain_field_offset" : tactic => `(tactic| (
  repeat (first
    | exact go.PlainFieldOffset.here _ _ _
    | (apply go.PlainFieldOffset.there
       · dsimp only [go.fieldDeclName]; decide
       · dsimp only [go.fieldDeclType]
         first
         | exact go.PlainLayout.scalar _ _ inferInstance
         | assumption))))

namespace github_com.mit_pdos.etcd_grove.examples.bboltfs

/-! ## FNV-1a -/

/-- FNV-1a's 64-bit prime. -/
def fnvPrime : BitVec 64 := 1099511628211

/-- FNV-1a's 64-bit offset basis, the hash of no bytes. -/
def fnvOffset : BitVec 64 := 14695981039346656037

/-- One step of FNV-1a: `h ^= uint64(c); h *= prime`. -/
def fnvStep (h : BitVec 64) (c : BitVec 8) : BitVec 64 := (h ^^^ c.setWidth 64) * fnvPrime

/-- FNV-1a over `bs` from `h`. -/
def fnvFrom (h : BitVec 64) (bs : List (BitVec 8)) : BitVec 64 := bs.foldl fnvStep h

/-- FNV-1a's 64-bit hash of `bs`. -/
def fnv64 (bs : List (BitVec 8)) : BitVec 64 := fnvFrom fnvOffset bs

section bytes
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
open ProofMode

/-- The bytes of a non-empty byte points-to lie in `(0, maxAddr]`. -/
theorem bytesPointsto_in_bounds (l : Loc) (dq : DFrac) (bs : List w8) (h : bs ≠ []) :
    bytesPointsto (GF := GF) l dq bs ⊢ ⌜0 < l.addr ∧ l.addr + bs.length ≤ maxAddr⌝ := by
  induction bs generalizing l with
  | nil => exact absurd rfl h
  | cons b bs ih =>
    unfold bytesPointsto
    iintro ⟨Hb, Hbs⟩
    icases heapPointsto_pos l dq _ $$ Hb with %H1
    icases heapPointsto_lt_maxAddr l dq _ $$ Hb with %H2
    cases bs with
    | nil => ipureintro; simp; omega
    | cons b' bs' =>
      icases ih (l +ₗ 1) (by simp) $$ Hbs with %H3
      ipureintro
      simp only [Loc.add, List.length_cons] at H3 ⊢
      omega


/-- A byte points-to from a positive address is a byte slice there. -/
theorem bytesPointsto_ownSlice (l : Loc) (dq : DFrac) (bs : List w8) (hl : 0 < l.addr)
    (hlen : bs.length < 2 ^ 63) :
    bytesPointsto (GF := GF) l dq bs ⊣⊢
      slice.mk l (W64 (bs.length : Int)) (W64 (bs.length : Int)) ↦*{dq} bs := by
  have hz : sint.Z (W64 (bs.length : Int)) = bs.length := sint_Z_W64_nat _ hlen
  have hnn : l ≠ null := by intro h; subst h; simp [null] at hl
  rw [ownSlice_unseal]; unfold ownSliceDef
  dsimp only
  rw [hz]
  by_cases hbs : bs = []
  · subst hbs
    constructor
    · iintro _
      iright
      isplitl
      · iapply array_empty _ _ hnn
      · ipureintro; omega
    · iintro _; unfold bytesPointsto; itrivial
  · have ha := typedPointsto_byte_array (GF := GF) l (bs.length : Int) (array.mk _ bs) dq hbs
    constructor
    · iintro H
      iright
      isplitl
      · iapply ha.2; iframe H; ipureintro; rfl
      · ipureintro; omega
    · iintro (%H | ⟨H, _⟩)
      · exfalso; apply hnn; have := congrArg GoSlice.ptr H.1; simpa [slice.nil] using this
      · icases ha.1 $$ H with ⟨_, H⟩
        iexact H

end bytes

/-! ## Allocation of a struct at a positive address

`struct_wp_alloc` (the allocation of a struct, `IntoValTyped.wp_alloc`) keeps only `l ≠ null` of
the address `GoPrealloc` gives; a byte view of the new struct (`BytesView`) needs `0 < l.addr`,
which `GoPrealloc` also gives (`wp_GoPrealloc_pos`). -/

section alloc_pos
open Iris Iris.BI Iris.ProgramLogic Iris.Std
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [go.PreSemantics]

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

end github_com.mit_pdos.etcd_grove.examples.bboltfs

end Perennial
