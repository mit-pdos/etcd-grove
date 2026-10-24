/-
The interval tree over **bytes-affine** intervals (`BytesAffineComparable`: a byte slice, compared
by `bytes.Compare`, the empty slice the top): a bytes-affine interval as the Go `Interval`
(`bytesIvl`, what `NewBytesAffineInterval(b, e)` returns; 2026-10-14, unit P2), the key
representation `bytesKey` (a slice holding the key's contents; the auth plan's S2b, 2026-10-23),
and the tree's ownership predicate over them (`ownIvtB`, the auth plan's S2): the generic
`ownIvtK` (`Defs.lean`) for `bytesKey`, so the model is the string-affine tree's (`Model.lean`,
entries over the keys' contents, `GoString`) and the nodes hold read-only slices.

Until S2b the three facts the auth store's permission cache needs (`Insert`, `Intersects`,
`Contains` over bytes-affine keys) were axioms here; they are now the generic proofs
instantiated (`Spec/Proof/.../adt/intervalTree__{Insert,Intersects,Contains}_bytes.lean`, linked
in `Link.lean`; `notes/decisions.md`, "S2b of the auth plan"). Here: the empty tree is a
bytes-affine tree (`ownIvtB_of_empty`: `NewIntervalTree`'s string-affine postcondition), a built
tree can be made read-only (`ownIvtB_persist`, the cache's trees are never modified), the entries
are in the tree's order (`ownIvtB_sorted`), and `bytesKey`'s comparison contract from
`BytesAffineComparable.Compare`'s spec (`bytesKey_ok`).
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.adt.NodeLemmas
public import Proof.go_etcd_io.etcd.pkg.v3.adt.Contains
public import Spec.go_etcd_io.etcd.pkg.v3.adt.BytesAffineComparable__Compare

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace adt

open Iris Iris.BI go_etcd_io.etcd.pkg.v3.adt

/-- A slice's length is zero only for the empty contents. -/
theorem slice_len_eq_zero {s : GoSlice} {bs : GoString}
    (h : bs.length = sint.nat s.len ∧ 0 ≤ sint.Z s.len) : s.len = W64 0 ↔ bs = [] := by
  constructor
  · intro h0
    have : bs.length = 0 := by rw [h.1, h0]; rfl
    exact List.eq_nil_of_length_eq_zero this
  · intro hn
    subst hn
    have := h.1
    simp only [List.length_nil] at this
    have := h.2
    word

section defs
variable [ext : FfiSyntax] [GoGlobalContext]

/-- The bytes-affine interval value `[b, e)` (slices `b`, `e`) as the Go `Interval`. -/
def bytesIvl (b e : GoSlice) : Interval :=
  { Begin' := interface.mkOk BytesAffineComparable.ty #b,
    End' := interface.mkOk BytesAffineComparable.ty #e }

@[simp] theorem bytesIvl_Begin (b e : GoSlice) :
    (bytesIvl b e).Begin' = interface.mkOk BytesAffineComparable.ty #b := rfl
@[simp] theorem bytesIvl_End (b e : GoSlice) :
    (bytesIvl b e).End' = interface.mkOk BytesAffineComparable.ty #e := rfl

end defs

section reprs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.adt.Assumptions]

open Iris.ProofMode

/-- A points-to made read-only. -/
theorem tp_persist' {V : Type} [TypedPointsto (GF := GF) V] (l : Loc) (v : V) (dq : DFrac) :
    (l ↦{dq} v : IProp GF) ⊢ |==> l ↦□ v :=
  (typedPointsto_dfractional (GF := GF) l v).dfractional_persist dq

omit package_sem in
/-- The Go value `v` (a slice) holds the key `k` at `d`: a byte slice with those contents. -/
def bytesKeyAt (d : DFrac) (v : val) (k : GoString) : IProp GF :=
  iprop(∃ s : GoSlice, ⌜v = #s⌝ ∗ s ↦*{d} k)

omit package_sem in
/-- Two slices' contents at one slice agree. -/
theorem bytes_keyAt_agree (d d' : DFrac) (v : val) (k k' : GoString) :
    bytesKeyAt (GF := GF) d v k ∗ bytesKeyAt d' v k' ⊢ ⌜k = k'⌝ := by
  unfold bytesKeyAt
  iintro ⟨⟨%s, %Hs, H⟩, ⟨%s', %Hs', H'⟩⟩
  subst Hs
  have : s = s' := go.intoVal_inj Hs'
  subst this
  iapply ownSlice_agree _ _ _ _ _ $$ H H'

omit package_sem in
/-- **Bytes-affine keys**: a `BytesAffineComparable`, a byte slice holding the key's contents at
the fraction. -/
def bytesKey : KeyRep (GF := GF) where
  ty := BytesAffineComparable.ty
  keyAt := bytesKeyAt
  keyAt_persistent := fun _ _ => by unfold bytesKeyAt; infer_instance
  keyAt_agree := bytes_keyAt_agree

omit package_sem in
@[simp] theorem bytesKey_ty : (bytesKey (GF := GF)).ty = BytesAffineComparable.ty := rfl
omit package_sem in
theorem bytesKey_keyAt (d : DFrac) (v : val) (k : GoString) :
    (bytesKey (GF := GF)).keyAt d v k = bytesKeyAt d v k := rfl

omit package_sem in
theorem bytesIvl_eq (b e : GoSlice) : bytesIvl b e = (bytesKey (GF := GF)).ivl #b #e := rfl

omit package_sem in
/-- A slice holding a key, as `bytesKey` holds it. -/
theorem bytesKeyAt_intro (d : DFrac) (s : GoSlice) (k : GoString) :
    (s ↦*{d} k : IProp GF) ⊢ bytesKeyAt d #s k := by
  unfold bytesKeyAt
  iintro H
  iexists s
  iframe
  ipureintro; rfl

omit package_sem in
/-- `bytesKey` holding a key at a slice's value is the slice holding it. -/
theorem bytesKeyAt_elim (d : DFrac) (s : GoSlice) (k : GoString) :
    bytesKeyAt (GF := GF) d #s k ⊢ (s ↦*{d} k : IProp GF) := by
  unfold bytesKeyAt
  iintro ⟨%s', %Hs, H⟩
  have : s' = s := (go.intoVal_inj Hs).symm
  subst this
  iexact H

/-- **The comparison contract of bytes-affine keys**, from `BytesAffineComparable.Compare`'s
spec. -/
theorem bytesKey_ok (h : adt.BytesAffineComparable.Compare.spec (GF := GF) (hG := hG)) :
    (bytesKey (GF := GF)).CompareOk := by
  intro d d' v v' k k'
  simp only [bytesKey_keyAt, bytesKey_ty]
  unfold bytesKeyAt
  iintro %Φ ⟨Hpkg, ⟨%s, %Hs, H⟩, ⟨%s', %Hs', H'⟩⟩ HΦ
  subst Hs Hs'
  wp_apply h s s' k k' d d' $$ [Hpkg H H'] as ⟨H, H'⟩
  · iframe
  iapply HΦ
  isplitl [H]
  · iexists s; iframe; ipureintro; rfl
  · iexists s'; iframe; ipureintro; rfl

include sem package_sem in
/-- **The tree at `t` holds the entries `L` over bytes-affine keys**, at `dq`: `ownIvtK` for
`bytesKey` (each node's begin, end and `max` a read-only slice holding the key). -/
def ownIvtB (t : Loc) (L : List Entry) (dq : DFrac) : IProp GF :=
  ownIvtK bytesKey t L dq

instance ownIvtB_persistent (t : Loc) (L : List Entry) :
    Persistent (ownIvtB (GF := GF) t L .discard) := by
  unfold ownIvtB; infer_instance

/-- The entries are in the tree's order. -/
theorem ownIvtB_sorted (t : Loc) (L : List Entry) (dq : DFrac) :
    ownIvtB (GF := GF) t L dq ⊢ ⌜IvSorted L⌝ :=
  ownIvtK_sorted bytesKey t L dq

/-- A built tree made read-only. -/
theorem ownIvtB_persist (t : Loc) (L : List Entry) :
    ownIvtB (GF := GF) t L (DFrac.own 1) ⊢ |==> ownIvtB t L .discard :=
  ownIvtK_persist bytesKey t L

/-- The empty tree (`NewIntervalTree`'s, `ownIvt t [] 1`) is a bytes-affine tree: only the
sentinel, which holds no key. -/
theorem ownIvtB_of_empty (t : Loc) : ownIvt (GF := GF) t [] 1 ⊢ ownIvtB t [] (DFrac.own 1) := by
  unfold ownIvt ownIvtB ownIvtK
  iintro ⟨%tv, %T, Ht, Hs, Hn, %H⟩
  obtain ⟨hio, hok, hsorted, hcount, hlen⟩ := H
  cases T with
  | node c l e r => simp at hio
  | leaf =>
    ihave %Hroot := ownNode_leaf_open _ _ _ _ _ $$ Hn
    iexists tv, .leaf
    iframe
    isplitl []
    · rw [ownNode_leaf]; ipureintro; exact Hroot
    ipureintro
    exact ⟨rfl, hok, hsorted, hcount, hlen⟩

end reprs

end adt
end EtcdGrove
end Perennial
