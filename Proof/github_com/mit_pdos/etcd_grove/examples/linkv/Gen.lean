/-
Lean-first (no Rocq counterpart).

The proof of `Gen`: the two slice literals, `RandomUint64`, and the two indexings, in bounds
since they are modulo the slices' lengths.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkv.Gen
public import Perennial.Proof.github_com.goose_lang.primitive.Link

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv.Assumptions]

theorem Gen.wp_proof : Gen.spec (GF := GF) (hG := hG) := by
  unfold Gen.spec lintest.genSpec
  iintro %id
  wp_start as _
  wp_auto
  wp_apply wp_slice_literal (l := genKeys)
  isplitr
  · ipureintro; rfl
  iintro %ksl ⟨Hk, _⟩
  simp only [go.arrayLiteralSize, List.foldl, Int.reduceAdd,
    show max (max (3 : Int) 0) 0 = 3 from rfl]
  wp_auto
  wp_apply wp_slice_literal (l := genVals)
  isplitr
  · ipureintro; rfl
  iintro %vsl ⟨Hv, _⟩
  simp only [go.arrayLiteralSize, List.foldl, Int.reduceAdd,
    show max (max (4 : Int) 0) 0 = 4 from rfl]
  wp_auto
  wp_apply github_com.goose_lang.primitive.wp_RandomUint64 as %n _
  -- `keys[n % 3]`
  have hk : 0 ≤ sint.Z (n % W64 3) ∧ sint.Z (n % W64 3) < 3 := by word
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
  list_elem genKeys (sint.Z (n % W64 3)).toNat as k
  wp_apply wp_load_slice_index _ (sint.Z (n % W64 3)) genKeys _ k hk.1 $$ [Hk] with Hk
  · iframe; ipureintro; exact Hk_lookup
  wp_auto
  have hkm : k ∈ genKeys := List.mem_of_getElem? Hk_lookup
  wp_if_destruct
  · -- a put: `vals[(n / 3 / 2) % 4]`
    have hv : 0 ≤ sint.Z (n / W64 3 / W64 2 % W64 4) ∧ sint.Z (n / W64 3 / W64 2 % W64 4) < 4 := by
      word
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
    list_elem genVals (sint.Z (n / W64 3 / W64 2 % W64 4)).toNat as v
    wp_apply wp_load_slice_index _ (sint.Z (n / W64 3 / W64 2 % W64 4)) genVals _ v hv.1 $$ [Hv]
      with Hv
    · iframe; ipureintro; exact Hv_lookup
    wp_auto
    have hvm : v ∈ genVals := List.mem_of_getElem? Hv_lookup
    iapply HΦ
    imodintro
    ipureintro
    exact ⟨_, rfl, hkm, fun _ => hvm⟩
  · -- a get
    iapply HΦ
    imodintro
    ipureintro
    exact ⟨_, rfl, hkm, fun h => nomatch h⟩

end proof

end linkv
end EtcdGrove
end Perennial
