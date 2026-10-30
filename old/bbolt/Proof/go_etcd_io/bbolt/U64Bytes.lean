/-
A slice of `uint64`s is the bytes of its elements (little-endian, 8 each, contiguous): what a
freelist page's ids are (`freelist.Read` reads them out of the mapping, `Write` writes them
into a page buffer).
-/
module

public import Proof.go_etcd_io.bbolt.internal.common.Inodes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode

section pure
variable [ext : FfiSyntax]

/-- The bytes of `uint64`s. -/
def u64sBytes (xs : List w64) : List w8 := xs.flatMap (fun x => leBytes 8 x.toNat)

theorem u64sBytes_length (xs : List w64) : (u64sBytes xs).length = 8 * xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    show (leBytes 8 _ ++ u64sBytes xs).length = _
    rw [List.length_append, leBytes_length', ih, List.length_cons]; omega

end pure

section u64s
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

theorem arrayIndexRef_w64 (l : Loc) (i : Int) (h : l.locCar ≠ 0) :
    arrayIndexRef w64 i l = l +ₗ (8 * i) := by
  unfold arrayIndexRef
  rw [ite_eq_right_of_eq_false _ _ (eq_false h), go.typeSize_w64, Int.mul_comm]

theorem arrayElems_u64s (l : Loc) (xs : List w64) (dq : DFrac) (h : l.locCar ≠ 0) :
    arrayElems (GF := GF) l xs dq ⊣⊢ bytesPointsto l dq (u64sBytes xs) := by
  induction xs generalizing l with
  | nil =>
    unfold arrayElems u64sBytes bytesPointsto pointstoVals byteVals
    simp only [List.flatMap_nil, List.map_nil]
    exact .rfl
  | cons x xs ih =>
    refine (arrayElems_cons l x xs dq).trans ?_
    rw [arrayIndexRef_w64 l 0 h, arrayIndexRef_w64 l 1 h]
    have h8 : (l +ₗ (8 * 1 : Int)).locCar ≠ 0 := by simpa [Loc.add] using h
    rw [show u64sBytes (x :: xs) = leBytes 8 x.toNat ++ u64sBytes xs from rfl]
    refine Iris.BI.BiEntails.trans ?_ (bytesPointsto_app _ _ _ _).symm
    rw [leBytes_length, show l +ₗ (8 * 0 : Int) = l by simp [Loc.add]]
    exact sep_congr (typedPointsto_w64_bytes _ _ _) (by
      rw [show l +ₗ ((8 : Nat) : Int) = l +ₗ (8 * 1 : Int) by simp]; exact ih _ h8)

/-- A nonempty slice of `uint64`s is the bytes at its pointer. -/
theorem ownSlice_u64s (s : GoSlice) (xs : List w64) (dq : DFrac) (hne : xs ≠ [])
    (hc : s.ptr.locCar ≠ 0) :
    s ↦*{dq} xs ⊣⊢ (bytesPointsto (GF := GF) s.ptr dq (u64sBytes xs) ∗
      ⌜(xs.length : Int) = sint.Z s.len ∧ sint.Z s.len ≤ sint.Z s.cap⌝) := by
  rw [ownSlice_unseal]; unfold ownSliceDef
  rw [typedPointsto_unseal_eq]
  simp only [TypedPointsto.typedPointstoDef]
  constructor
  · iintro (%H | ⟨⟨⟨%Hlen, H⟩, %Hnn⟩, %Hcap⟩)
    · exact absurd H.2 hne
    · isplitl [H]
      · iapply (arrayElems_u64s _ _ _ hc).1 $$ H
      · ipureintro; exact ⟨by simpa using Hlen, Hcap⟩
  · iintro ⟨H, %Hlen, %Hcap⟩
    iright
    isplitl [H]
    · isplitl [H]
      · isplit
        · ipureintro; simpa using Hlen
        · iapply (arrayElems_u64s _ _ _ hc).2 $$ H
      · ipureintro; exact loc_ne_null_of_car _ hc
    · ipureintro; exact Hcap

end u64s

end bbolt
end EtcdGrove
end Perennial
