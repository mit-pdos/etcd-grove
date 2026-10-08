/-
`raftpb.ConfState.Equivalent` (confstate.go, hand-written): the vocabulary of its proof
(2026-10-08, when it stopped being an axiom). It sorts copies of the four id slices of
both `ConfState`s and compares the results with `reflect.DeepEqual`, which this
development does not translate (`reflect` is names-only): `reflect.DeepEqual` on two
`ConfState` values is the axiom instead, `Spec/reflect_DeepEqual.lean`, stated with
`confStateDeepEq` below, Go's `DeepEqual` on this struct: field by field, a slice
field comparing nil-ness and then elements.
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

/-- `reflect.DeepEqual` on two `ConfState` values whose slice fields hold the given
lists: equal `AutoLeave`, and for each slice field the same nil-ness (Go's `DeepEqual`
tells a nil slice from an empty non-nil one) and the same elements. -/
def confStateDeepEq [FfiSyntax] (a b : raftpb.ConfState)
    (av al avo aln bv bl bvo bln : List w64) : Prop :=
  (a.Voters' = slice.nil ↔ b.Voters' = slice.nil) ∧ av = bv ∧
  (a.Learners' = slice.nil ↔ b.Learners' = slice.nil) ∧ al = bl ∧
  (a.VotersOutgoing' = slice.nil ↔ b.VotersOutgoing' = slice.nil) ∧ avo = bvo ∧
  (a.LearnersNext' = slice.nil ↔ b.LearnersNext' = slice.nil) ∧ aln = bln ∧
  a.AutoLeave' = b.AutoLeave'

instance confStateDeepEq_decidable [FfiSyntax] (a b : raftpb.ConfState)
    (av al avo aln bv bl bvo bln : List w64) :
    Decidable (confStateDeepEq a b av al avo aln bv bl bvo bln) := by
  unfold confStateDeepEq; infer_instance

/-- Sorted by `uint.Z`, as `slices.Sort`'s spec states it (`Spec/slices_Sort.lean`). -/
def SortedW64 (xs : List w64) : Prop :=
  ∀ (i j : Nat) (xi xj : w64), xs[i]? = some xi → xs[j]? = some xj → i < j →
    uint.Z xi ≤ uint.Z xj

theorem sortedW64_iff_pairwise (xs : List w64) :
    SortedW64 xs ↔ xs.Pairwise (fun a b => uint.Z a ≤ uint.Z b) := by
  rw [List.pairwise_iff_getElem]
  constructor
  · intro h i j hi hj hij
    exact h i j _ _ (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem hj) hij
  · intro h i j xi xj hxi hxj hij
    obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 hxi
    obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.1 hxj
    exact h i j hi hj hij

theorem w64_eq_of_le_le {a b : w64} (h1 : uint.Z a ≤ uint.Z b) (h2 : uint.Z b ≤ uint.Z a) :
    a = b := by
  word

/-- Two sorted permutations of each other are equal: what makes `Equivalent`'s sorted
copies of permuted voter lists `DeepEqual`. -/
theorem sorted_perm_eq : ∀ (xs ys : List w64), xs ≡ₚ ys →
    xs.Pairwise (fun a b => uint.Z a ≤ uint.Z b) →
    ys.Pairwise (fun a b => uint.Z a ≤ uint.Z b) → xs = ys
  | [], ys, hp, _, _ => (List.Perm.nil_eq hp).symm ▸ rfl
  | _ :: _, [], hp, _, _ => absurd (List.Perm.length_eq hp) (by simp)
  | x :: xs, y :: ys, hp, hx, hy => by
    rw [List.pairwise_cons] at hx hy
    have hxy : x = y := by
      have hxin : x ∈ y :: ys := hp.subset (List.mem_cons_self ..)
      have hyin : y ∈ x :: xs := hp.symm.subset (List.mem_cons_self ..)
      rcases List.mem_cons.1 hxin with h | h
      · exact h
      rcases List.mem_cons.1 hyin with h' | h'
      · exact h'.symm
      exact w64_eq_of_le_le (hx.1 y h') (hy.1 x h)
    subst hxy
    have hp' : xs ≡ₚ ys := List.Perm.cons_inv hp
    rw [sorted_perm_eq xs ys hp' hx.2 hy.2]

section wp
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]

/-- `append([]uint64(nil), s...)` for an empty `s` is `nil`, whatever `s`'s pointer:
nothing is read. `Equivalent` copies the six empty id slices this way, and
`reflect.DeepEqual` then sees `nil` on both sides; its callers only know the slices'
lengths, so this needs no ownership of `s` (`wp_slice_append` would). -/
theorem wp_slice_append_nil_empty (s : GoSlice) (hlen : s.len = W64 0) :
    {{ (True : IProp GF) }}
      (App (App (Val #(functions go.append [go.GoType.SliceType go.uint64])) (Val #slice.nil))
        (Val #s))
    {{ RET #slice.nil; True }} := by
  wp_start as Hpre
  iclear Hpre
  wp_apply wp_sumAssumeNoOverflowSigned with %Hoverflow
  wp_if_destruct
  · rw [hlen]
    have h00 : (0 : w64) + W64 0 = W64 0 := by decide
    simp only [h00]
    rw [ite_eq_left ⟨by decide, by decide, by decide⟩]
    wp_auto
    have Hsn : slice.slice slice.nil w64 (W64 0) (W64 0) = slice.nil := by
      simp only [slice.slice, sliceIndexRef]
      rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0]
      decide
    rw [Hsn]
    -- `copy` into the empty slice: its loop runs zero times
    wp_func_call
    wp_call
    wp_auto
    have Hsn' : slice.slice slice.nil w64 0 (W64 0) = slice.nil := Hsn
    rw [Hsn']
    wp_for
    wp_end
  · exfalso; rw [hlen] at Hif; exact Hif (by decide)

end wp

end EtcdGrove
end Perennial
