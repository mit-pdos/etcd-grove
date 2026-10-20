/- Lean-first (no Rocq counterpart). The proof of `Gen` (as linkv's). -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.cachekv.Gen
public import Perennial.Proof.github_com.goose_lang.primitive.Link

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cachekv

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.cachekv

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.cachekv.Assumptions]

theorem Gen.wp_proof : Gen.spec (GF := GF) (hG := hG) := by
  wp_start as _
  (try wp_auto)
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
  have hk : 0 ≤ sint.Z (n % W64 3) ∧ sint.Z (n % W64 3) < 3 := by word
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
  list_elem genKeys (sint.Z (n % W64 3)).toNat as k
  wp_apply wp_load_slice_index _ (sint.Z (n % W64 3)) genKeys _ k hk.1 $$ [Hk] with Hk
  · iframe; ipureintro; exact Hk_lookup
  wp_auto
  have hkm : k ∈ genKeys := List.mem_of_getElem? Hk_lookup
  have hv : 0 ≤ sint.Z (n / W64 3 % W64 4) ∧ sint.Z (n / W64 3 % W64 4) < 4 := by word
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
  list_elem genVals (sint.Z (n / W64 3 % W64 4)).toNat as v
  wp_apply wp_load_slice_index _ (sint.Z (n / W64 3 % W64 4)) genVals _ v hv.1 $$ [Hv] with Hv
  · iframe; ipureintro; exact Hv_lookup
  (try wp_auto)
  have hvm : v ∈ genVals := List.mem_of_getElem? Hv_lookup
  iapply HΦ
  ipureintro
  exact ⟨hkm, hvm⟩

end proof

end cachekv
end EtcdGrove
end Perennial
