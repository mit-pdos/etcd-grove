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
instance metav1Time.countable [GooseExts] :
    Pos.Countable k8s_io.apimachinery.pkg.apis.«meta».v1.Time :=
  .ofInjective (fun t => Pos.Countable.encode t.Time')
    (by rintro ⟨a⟩ ⟨b⟩ h; have h := Pos.encode_inj h; simp_all)

instance metav1MicroTime.countable [GooseExts] :
    Pos.Countable k8s_io.apimachinery.pkg.apis.«meta».v1.MicroTime :=
  .ofInjective (fun t => Pos.Countable.encode t.Time')
    (by rintro ⟨a⟩ ⟨b⟩ h; have h := Pos.encode_inj h; simp_all)

section own
variable [GooseExts] [GooseSemantics] [GooseInterp]
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

/-! ### Read-only copies: timelessness, persistence at `DFrac.discard`, and the update to it -/

/-- **A deep ownership persists** (every fraction can be given up for the discarded one). -/
class DeepPersist {V E : Type} (inner : V → DFrac → E → IProp GF) : Prop where
  persist : ∀ x dq e, inner x dq e ⊢ |==> inner x DFrac.discard e

instance ownBaseD_timeless {V : Type} (v : V) (dq : DFrac) (e : V) :
    Timeless (ownBaseD (GF := GF) v dq e) := by unfold ownBaseD; infer_instance

instance ownBaseD_persistent {V : Type} (v : V) (dq : DFrac) (e : V) :
    Persistent (ownBaseD (GF := GF) v dq e) := by unfold ownBaseD; infer_instance

instance ownBaseD_deepPersist {V : Type} : DeepPersist (GF := GF) (ownBaseD (V := V)) where
  persist := by intro x dq e; unfold ownBaseD; iintro %h; imodintro; ipureintro; exact h

instance ownPtrD_timeless {V E : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    (inner : V → DFrac → E → IProp GF) [∀ x dq e, Timeless (inner x dq e)] (p : Loc) (dq : DFrac)
    (e : Option E) : Timeless (ownPtrD inner p dq e) := by
  cases e <;> unfold ownPtrD <;> infer_instance

instance ownPtrD_persistent {V E : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    (inner : V → DFrac → E → IProp GF) [∀ x e, Persistent (inner x DFrac.discard e)] (p : Loc)
    (e : Option E) : Persistent (ownPtrD inner p DFrac.discard e) := by
  cases e <;> unfold ownPtrD <;> infer_instance

instance ownPtrD_deepPersist {V E : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    (inner : V → DFrac → E → IProp GF) [hI : DeepPersist inner] :
    DeepPersist (fun p dq e => ownPtrD (GF := GF) (V := V) inner p dq e) where
  persist := by
    intro p dq e
    cases e with
    | none => unfold ownPtrD; iintro %h; imodintro; ipureintro; exact h
    | some e =>
      unfold ownPtrD
      iintro ⟨%x, Hp, Hi⟩
      imod (typedPointsto_dfractional (GF := GF) p x).dfractional_persist dq $$ Hp with Hp
      imod hI.persist x dq e $$ Hi with Hi
      imodintro
      iexists x
      iframe

theorem bigSepL2_persist_upd {V E : Type} (inner : V → DFrac → E → IProp GF) [hI : DeepPersist inner]
    (dq : DFrac) : ∀ (vs : List V) (es : List E),
      ([∗list] x;e ∈ vs;es, inner x dq e) ⊢ |==> [∗list] x;e ∈ vs;es, inner x DFrac.discard e
  | [], [] => by
    iintro -
    imodintro
    iapply (BigSepL2.bigSepL2_nil (PROP := IProp GF)).2
    iempintro
  | [], _ :: _ => by iintro H; ihave %h := BigSepL2.bigSepL2_nil_inv_left $$ H; cases h
  | _ :: _, [] => by iintro H; ihave %h := BigSepL2.bigSepL2_nil_inv_right $$ H; cases h
  | x :: vs, e :: es => by
    iintro ⟨Hx, Hrest⟩
    imod hI.persist x dq e $$ Hx with Hx
    imod bigSepL2_persist_upd inner dq vs es $$ Hrest with Hrest
    imodintro
    iframe

instance ownSliceD_timeless {V E : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    (inner : V → DFrac → E → IProp GF) [∀ x dq e, Timeless (inner x dq e)] (s : GoSlice) (dq : DFrac)
    (es : List E) : Timeless (ownSliceD inner s dq es) := by
  unfold ownSliceD; infer_instance

instance ownSliceD_persistent {V E : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    (inner : V → DFrac → E → IProp GF) [∀ x e, Persistent (inner x DFrac.discard e)] (s : GoSlice)
    (es : List E) : Persistent (ownSliceD inner s DFrac.discard es) := by
  unfold ownSliceD; infer_instance

instance ownSliceD_deepPersist {V E : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    (inner : V → DFrac → E → IProp GF) [hI : DeepPersist inner] :
    DeepPersist (fun s dq es => ownSliceD (GF := GF) (V := V) inner s dq es) where
  persist := by
    intro s dq es
    unfold ownSliceD
    iintro ⟨%vs, Hs, Hl⟩
    imod ownSlice_persist _ _ _ $$ Hs with Hs
    imod bigSepL2_persist_upd inner dq vs es $$ Hl with Hl
    imodintro
    iexists vs
    iframe

instance ownMapD_timeless {K V : Type} [ZeroVal K] [DecidableEq K] [ZeroVal V] [go.IntoValInj K]
    (m : GoMap) (dq : DFrac) (e : Option (GMap K V)) : Timeless (ownMapD (GF := GF) m dq e) := by
  cases e <;> unfold ownMapD <;> infer_instance

instance ownMapD_persistent {K V : Type} [ZeroVal K] [DecidableEq K] [ZeroVal V] [go.IntoValInj K]
    (m : GoMap) (e : Option (GMap K V)) : Persistent (ownMapD (GF := GF) m DFrac.discard e) := by
  cases e <;> unfold ownMapD <;> infer_instance

instance ownMapD_deepPersist {K V : Type} [ZeroVal K] [DecidableEq K] [ZeroVal V] [go.IntoValInj K] :
    DeepPersist (fun m dq e => ownMapD (GF := GF) (K := K) (V := V) m dq e) where
  persist := by
    intro m dq e
    cases e with
    | none => unfold ownMapD; iintro %h; imodintro; ipureintro; exact h
    | some M =>
      unfold ownMapD
      iintro H
      imod ownMap_persist _ _ _ $$ H with H
      imodintro
      iexact H

instance ownOpaquePtrD_timeless (p : Loc) (e : Option Unit) : Timeless (ownOpaquePtrD (GF := GF) p e) := by
  cases e <;> unfold ownOpaquePtrD <;> infer_instance
instance ownOpaquePtrD_persistent (p : Loc) (e : Option Unit) : Persistent (ownOpaquePtrD (GF := GF) p e) := by
  cases e <;> unfold ownOpaquePtrD <;> infer_instance
instance ownNilSliceD_timeless (s : GoSlice) : Timeless (ownNilSliceD (GF := GF) s) := by
  unfold ownNilSliceD; infer_instance
instance ownNilSliceD_persistent (s : GoSlice) : Persistent (ownNilSliceD (GF := GF) s) := by
  unfold ownNilSliceD; infer_instance
instance ownNilMapD_timeless (m : GoMap) : Timeless (ownNilMapD (GF := GF) m) := by
  unfold ownNilMapD; infer_instance
instance ownNilMapD_persistent (m : GoMap) : Persistent (ownNilMapD (GF := GF) m) := by
  unfold ownNilMapD; infer_instance
instance ownNilIfaceD_timeless (i : GoInterface) : Timeless (ownNilIfaceD (GF := GF) i) := by
  unfold ownNilIfaceD; infer_instance
instance ownNilIfaceD_persistent (i : GoInterface) : Persistent (ownNilIfaceD (GF := GF) i) := by
  unfold ownNilIfaceD; infer_instance

end own

end EtcdGrove
end Perennial
