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

include package_sem in
theorem typeSize_leafPageElement : typeSize leafPageElement = 16 := by
  rw [go.StructLayout.size (V := leafPageElement)]
  simp [go.structLayout, go.structLayoutAux, go.roundUp] <;> decide

include package_sem in
theorem typeSize_branchPageElement : typeSize branchPageElement = 16 := by
  rw [go.StructLayout.size (V := branchPageElement)]
  simp [go.structLayout, go.structLayoutAux, go.roundUp] <;> decide

/-- A location in a block is not null, nor is any offset of it. -/
theorem loc_add_ne_null (l : Loc) (k : Int) (h : l.locCar ≠ 0) : l +ₗ k ≠ null := by
  intro e; apply h; simpa [Loc.add, null] using congrArg Loc.locCar e

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

/-- The bytes of an `InBucket`: `root` (8), `sequence` (8). -/
def inBucketBytes (b : InBucket) : List w8 :=
  leBytes 8 b.root'.toNat ++ leBytes 8 b.sequence'.toNat

include package_sem in
theorem InBucket_fields (l : Loc) (h : l.locCar ≠ 0) :
    structFieldRef InBucket go!"root" l = l ∧ structFieldRef InBucket go!"sequence" l = l +ₗ 8 := by
  refine ⟨?_, ?_⟩
  · have H0 : structFieldRef InBucket go!"root" l = l +ₗ 0 := by solve_field_ref
    simpa using H0
  · solve_field_ref

include package_sem in
/-- An `InBucket` (a bucket's header, inline in a leaf or in a meta) is its bytes. -/
theorem InBucket_bytes (l : Loc) (b : InBucket) (dq : DFrac) (h : l.locCar ≠ 0) :
    l ↦{dq} b ⊣⊢ bytesPointsto (GF := GF) l dq (inBucketBytes b) := by
  obtain ⟨Hr, Hs⟩ := InBucket_fields (hG := hG) l h
  rw [typedPointsto_unseal_eq]
  simp only [TypedPointsto.typedPointstoDef]
  rw [Hr, Hs]
  refine Iris.BI.BiEntails.trans ?_ ((bytesPointsto_app l dq _ _).symm)
  simp only [leBytes_length]
  constructor
  · iintro ⟨⟨Hr, Hs, -⟩, -⟩
    isplitl [Hr]; · iapply (typedPointsto_w64_bytes _ _ _).1 $$ Hr
    iapply (typedPointsto_w64_bytes _ _ _).1 $$ Hs
  · iintro ⟨Hr, Hs⟩
    isplitl [Hr Hs]
    · isplitl [Hr]; · iapply (typedPointsto_w64_bytes _ _ _).2 $$ Hr
      isplitl [Hs]; · iapply (typedPointsto_w64_bytes _ _ _).2 $$ Hs
      itrivial
    · ipureintro; exact loc_ne_null_of_car l h

/-- The bytes of a `Meta`: `magic`, `version`, `pageSize`, `flags` (4 each), `root` (16),
`freelist`, `pgid`, `txid`, `checksum` (8 each); 64 in all, the checksum the last 8. -/
def metaBytes (m : Meta) : List w8 :=
  leBytes 4 m.magic'.toNat ++ leBytes 4 m.version'.toNat ++ leBytes 4 m.pageSize'.toNat ++
    leBytes 4 m.flags'.toNat ++ inBucketBytes m.root' ++ leBytes 8 m.freelist'.toNat ++
    leBytes 8 m.pgid'.toNat ++ leBytes 8 m.txid'.toNat ++ leBytes 8 m.checksum'.toNat

theorem metaBytes_length (m : Meta) : (metaBytes m).length = 64 := by
  simp [metaBytes, inBucketBytes, leBytes_length]

include package_sem in
theorem Meta_fields (l : Loc) (h : l.locCar ≠ 0) :
    structFieldRef Meta go!"magic" l = l ∧ structFieldRef Meta go!"version" l = l +ₗ 4 ∧
    structFieldRef Meta go!"pageSize" l = l +ₗ 8 ∧ structFieldRef Meta go!"flags" l = l +ₗ 12 ∧
    structFieldRef Meta go!"root" l = l +ₗ 16 ∧ structFieldRef Meta go!"freelist" l = l +ₗ 32 ∧
    structFieldRef Meta go!"pgid" l = l +ₗ 40 ∧ structFieldRef Meta go!"txid" l = l +ₗ 48 ∧
    structFieldRef Meta go!"checksum" l = l +ₗ 56 := by
  have Hib : typeSize InBucket = 16 := by
    rw [go.StructLayout.size (V := InBucket)]
    simp [go.structLayout, go.structLayoutAux, go.roundUp] <;> decide
  have Hia : typeAlign InBucket = 8 := by
    rw [go.StructLayout.align (V := InBucket)]
    simp [go.structLayout, go.structLayoutAux, go.roundUp] <;> decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have H0 : structFieldRef Meta go!"magic" l = l +ₗ 0 := by
      apply go.StructLayout.field_ref _ _ _ _ h
      simp [go.structFieldOffset, go.structLayout, go.structLayoutAux, go.roundUp, Hib, Hia]
    simpa using H0
  all_goals
    apply go.StructLayout.field_ref _ _ _ _ h
    simp [go.structFieldOffset, go.structLayout, go.structLayoutAux, go.roundUp, Hib, Hia]
    try decide

end bytes

end bbolt
end EtcdGrove
end Perennial
