/-
**Deep ownership of Go values: the combinators** of the generated deep values of the API objects
(`Proof/k8s_io/api/Deep.lean`, `etc/gen-k8s-deep.py`). Lean-first (no Rocq counterpart).

A Go value of a struct type owns the heap its pointers, slices and maps reach; its *deep value*
forgets the locations, so that a deep copy has the same deep value as the original. For an
element type with values `V`, deep values `E` and ownership `inner : V → DFrac → E → IProp`:

* `ownBaseD v dq e`: a basic value, `⌜v = e⌝`;
* `ownPtrD inner p dq d`: a pointer, `nil` for `none`, else it points to a value owned with `e`;
* `ownSliceD inner s dq ds`: a slice whose elements are owned with `ds` (nil-ness is not kept);
* `ownMapD m dq d`: a map of basic keys and values, `nil` for `none`, else `m ↦${dq} M`;
* `ownOpaquePtrD p d`: a pointer to a value that is never owned (an axiomatized Goose type,
  whose typed points-to is a `sorry` of the translation): only whether it is `nil`;
* `ownNilSliceD`, `ownNilMapD`, `ownNilIfaceD`: a slice, map or interface that must be `nil`.

The `*_of` lemmas prove the generated `own_zero` lemmas (the zero value owns its zero deep value).
-/
module

public import GeneratedProof.k8s_io.api.core.v1
public import GeneratedProof.k8s_io.api.apps.v1
public import Perennial.Proof.time.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

/-- `metav1.Time` is a basic deep value (a `time.Time`; its `*Location` is shared). -/
instance metav1Time.countable [FfiSyntax] :
    Pos.Countable k8s_io.apimachinery.pkg.apis.«meta».v1.Time :=
  .ofInjective (fun t => Pos.Countable.encode t.Time')
    (by rintro ⟨a⟩ ⟨b⟩ h; have h := Pos.encode_inj h; simp_all)

instance metav1MicroTime.countable [FfiSyntax] :
    Pos.Countable k8s_io.apimachinery.pkg.apis.«meta».v1.MicroTime :=
  .ofInjective (fun t => Pos.Countable.encode t.Time')
    (by rintro ⟨a⟩ ⟨b⟩ h; have h := Pos.encode_inj h; simp_all)

section own
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- A basic value: its deep value is itself. -/
def ownBaseD {V : Type} (v : V) (_dq : DFrac) (e : V) : IProp GF := iprop(⌜v = e⌝)

/-- A pointer: `nil` for `none`; else it points to a value owned with the deep value. -/
def ownPtrD {V E : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    (inner : V → DFrac → E → IProp GF) (p : Loc) (dq : DFrac) : Option E → IProp GF
  | none => iprop(⌜p = null⌝)
  | some e => iprop(∃ x : V, p ↦{dq} x ∗ inner x dq e)

/-- A slice: its elements, owned with the deep values (one each). -/
def ownSliceD {V E : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    (inner : V → DFrac → E → IProp GF) (s : GoSlice) (dq : DFrac) (ds : List E) : IProp GF :=
  iprop(∃ vs : List V, s ↦*{dq} vs ∗ [∗list] x;e ∈ vs;ds, inner x dq e)

/-- A map of basic keys and values: `nil` for `none`. -/
def ownMapD {K V : Type} [ZeroVal K] [DecidableEq K] [ZeroVal V] [go.IntoValInj K]
    (m : GoMap) (dq : DFrac) : Option (GMap K V) → IProp GF
  | none => iprop(⌜m = null⌝)
  | some M => iprop(m ↦${dq} M)

/-- A pointer to a value that is never owned: only whether it is `nil`. -/
def ownOpaquePtrD (p : Loc) : Option Unit → IProp GF
  | none => iprop(⌜p = null⌝)
  | some () => iprop(⌜p ≠ null⌝)

/-- A slice that must be `nil`. -/
def ownNilSliceD (s : GoSlice) : IProp GF := iprop(⌜s = slice.nil⌝)

/-- A map that must be `nil`. -/
def ownNilMapD (m : GoMap) : IProp GF := iprop(⌜m = null⌝)

/-- An interface that must be `nil`. -/
def ownNilIfaceD (i : GoInterface) : IProp GF := iprop(⌜i = interface.nil⌝)

/-! The zero value's fields (the generated `own_zero` proofs). -/

theorem ownBaseD_of {V : Type} (v e : V) (h : v = e) (dq : DFrac) :
    ⊢ ownBaseD (GF := GF) v dq e := by
  unfold ownBaseD; ipureintro; exact h

theorem ownPtrD_none_of {V E : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    (inner : V → DFrac → E → IProp GF) (p : Loc) (h : p = null) (dq : DFrac) :
    ⊢ ownPtrD inner p dq none := by
  unfold ownPtrD; ipureintro; exact h

theorem ownSliceD_nil_of {V E : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    (inner : V → DFrac → E → IProp GF) (s : GoSlice) (h : s = slice.nil) (dq : DFrac) :
    ⊢ ownSliceD inner s dq [] := by
  subst h
  unfold ownSliceD
  iexists []
  isplitl
  · iapply ownSlice_nil
  · iapply (BigSepL2.bigSepL2_nil (PROP := IProp GF)).2; itrivial

theorem ownMapD_none_of {K V : Type} [ZeroVal K] [DecidableEq K] [ZeroVal V] [go.IntoValInj K]
    (m : GoMap) (h : m = null) (dq : DFrac) :
    ⊢ ownMapD (GF := GF) (K := K) (V := V) m dq none := by
  unfold ownMapD; ipureintro; exact h

theorem ownOpaquePtrD_none_of (p : Loc) (h : p = null) :
    ⊢ ownOpaquePtrD (GF := GF) p none := by
  unfold ownOpaquePtrD; ipureintro; exact h

theorem ownNilSliceD_of (s : GoSlice) (h : s = slice.nil) : ⊢ ownNilSliceD (GF := GF) s := by
  unfold ownNilSliceD; ipureintro; exact h

theorem ownNilMapD_of (m : GoMap) (h : m = null) : ⊢ ownNilMapD (GF := GF) m := by
  unfold ownNilMapD; ipureintro; exact h

theorem ownNilIfaceD_of (i : GoInterface) (h : i = interface.nil) :
    ⊢ ownNilIfaceD (GF := GF) i := by
  unfold ownNilIfaceD; ipureintro; exact h

end own

end EtcdGrove
end Perennial
