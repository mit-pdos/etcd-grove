/-
The byte view of bbolt's on-disk structs: a `Page` header, a `Meta`, an `InBucket` and the
leaf and branch page elements are their fields' little-endian bytes, in order (they have
no padding: every field is aligned where the one before it ends). A page in the memory map
is reinterpreted as these structs through `unsafe.Pointer`; these lemmas move between the
two views (`Perennial.Golang.Theory.Bytes` for words and byte slices).
-/
module

public import Proof.go_etcd_io.bbolt.internal.common.Init
public import Perennial.Golang.Theory.Bytes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.common

section bytes
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

/-- Element 0 of an array is at its start (in a block or not). -/
theorem arrayIndexRef_zero (V : Type) (l : Loc) : arrayIndexRef V 0 l = l := by
  unfold arrayIndexRef; split <;> simp

/-- The bytes of a page header: `id` (8), `flags` (2), `count` (2), `overflow` (4). -/
def pageBytes (p : Page) : List w8 :=
  leBytes 8 p.id'.toNat ++ leBytes 2 p.flags'.toNat ++ leBytes 2 p.count'.toNat ++
    leBytes 4 p.overflow'.toNat

/-- The offset of a field of `Page`. -/
macro "solve_field_ref" : tactic => `(tactic| (
  apply go.StructLayout.field_ref _ _ _ _ ‹_›
  simp [go.structFieldOffset, go.structLayout, go.structLayoutAux, go.roundUp]
  try decide))

include package_sem in
theorem Page_fields (l : Loc) (h : l.locCar ≠ 0) :
    structFieldRef Page go!"id" l = l ∧ structFieldRef Page go!"flags" l = l +ₗ 8 ∧
    structFieldRef Page go!"count" l = l +ₗ 10 ∧
    structFieldRef Page go!"overflow" l = l +ₗ 12 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have H0 : structFieldRef Page go!"id" l = l +ₗ 0 := by solve_field_ref
    simpa using H0
  all_goals solve_field_ref

theorem pageBytes_split (l : Loc) (dq : DFrac) (p : Page) :
    bytesPointsto (GF := GF) l dq (pageBytes p) ⊣⊢
      bytesPointsto l dq (leBytes 8 p.id'.toNat) ∗
      bytesPointsto (l +ₗ 8) dq (leBytes 2 p.flags'.toNat) ∗
      bytesPointsto (l +ₗ 10) dq (leBytes 2 p.count'.toNat) ∗
      bytesPointsto (l +ₗ 12) dq (leBytes 4 p.overflow'.toNat) := by
  unfold pageBytes
  rw [List.append_assoc, List.append_assoc]
  refine ((bytesPointsto_app _ _ _ _).trans (sep_congr .rfl ((bytesPointsto_app _ _ _ _).trans
    (sep_congr .rfl (bytesPointsto_app _ _ _ _))))).trans ?_
  simp only [leBytes_length, loc_add_assoc]
  exact .rfl

include package_sem in
/-- A page header is its bytes. -/
theorem Page_bytes (l : Loc) (p : Page) (dq : DFrac) (h : l.locCar ≠ 0) :
    l ↦{dq} p ⊣⊢ bytesPointsto (GF := GF) l dq (pageBytes p) := by
  obtain ⟨Hid, Hfl, Hcnt, Hov⟩ := Page_fields (hG := hG) l h
  rw [typedPointsto_unseal_eq]
  simp only [TypedPointsto.typedPointstoDef]
  rw [Hid, Hfl, Hcnt, Hov]
  refine Iris.BI.BiEntails.trans ?_ (pageBytes_split l dq p).symm
  constructor
  · iintro ⟨⟨Hid, Hfl, Hcnt, Hov, -⟩, -⟩
    isplitl [Hid]; · iapply (typedPointsto_w64_bytes _ _ _).1 $$ Hid
    isplitl [Hfl]; · iapply (typedPointsto_w16_bytes _ _ _).1 $$ Hfl
    isplitl [Hcnt]; · iapply (typedPointsto_w16_bytes _ _ _).1 $$ Hcnt
    iapply (typedPointsto_w32_bytes _ _ _).1 $$ Hov
  · iintro ⟨Hid, Hfl, Hcnt, Hov⟩
    isplitl [Hid Hfl Hcnt Hov]
    · isplitl [Hid]; · iapply (typedPointsto_w64_bytes _ _ _).2 $$ Hid
      isplitl [Hfl]; · iapply (typedPointsto_w16_bytes _ _ _).2 $$ Hfl
      isplitl [Hcnt]; · iapply (typedPointsto_w16_bytes _ _ _).2 $$ Hcnt
      isplitl [Hov]; · iapply (typedPointsto_w32_bytes _ _ _).2 $$ Hov
      itrivial
    · ipureintro; exact loc_ne_null_of_car l h

end bytes

end bbolt
end EtcdGrove
end Perennial
