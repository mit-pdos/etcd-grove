/- Lean-first (no Rocq counterpart). The proof of `Gen` (as linkv's). -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.common.Gen
public import Perennial.Proof.github_com.goose_lang.primitive.Link

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace common

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.common

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.common.Assumptions]

theorem Gen.wp_proof : Gen.spec (GF := GF) (hG := hG) := by
  intro ksl ks hk0 hk63
  wp_start as #Hk
  ihave %Hkl := ownSlice_len $$ Hk
  (try wp_auto)
  wp_apply wp_slice_literal (l := genVals)
  isplitr
  · ipureintro; rfl
  iintro %vsl ⟨Hv, _⟩
  simp only [go.arrayLiteralSize, List.foldl, Int.reduceAdd,
    show max (max (4 : Int) 0) 0 = 4 from rfl]
  wp_auto
  wp_apply github_com.goose_lang.primitive.wp_RandomUint64 as %n _
  (try wp_auto)
  have hlen : sint.Z ksl.len = ks.length := by have := Hkl.1; word
  have hlen : sint.Z ksl.len = ks.length := by have := Hkl.1; word
  have hne : ¬ uint.Z ksl.len = 0 := by have := Hkl.1; word
  simp only [hne, if_false]
  (try wp_auto)
  have hlpos : 0 < uint.Z ksl.len ∧ uint.Z ksl.len < 2 ^ 63 := by
    have := Hkl.1; constructor <;> word
  have hmod : uint.Z (n % ksl.len) < uint.Z ksl.len := by
    rw [word.unsigned_modu]; exact Int.emod_lt_of_pos _ hlpos.1
  have hk : 0 ≤ sint.Z (n % ksl.len) ∧ sint.Z (n % ksl.len) < sint.Z ksl.len := by
    constructor <;> word
  rw [ite_eq_left_of_eq_true _ _ (eq_true hk)]
  list_elem ks (sint.Z (n % ksl.len)).toNat as k
  wp_apply wp_load_slice_index _ (sint.Z (n % ksl.len)) ks _ k hk.1 $$ [Hk] with Hk
  · iframe #; ipureintro; exact Hk_lookup
  wp_auto
  have hkm : k ∈ ks := List.mem_of_getElem? Hk_lookup
  simp only [hne, if_false]
  (try wp_auto)
  have hv : 0 ≤ sint.Z (n / ksl.len % W64 4) ∧ sint.Z (n / ksl.len % W64 4) < 4 := by word
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
  list_elem genVals (sint.Z (n / ksl.len % W64 4)).toNat as v
  wp_apply wp_load_slice_index _ (sint.Z (n / ksl.len % W64 4)) genVals _ v hv.1 $$ [Hv] with Hv
  · iframe; ipureintro; exact Hv_lookup
  (try wp_auto)
  have hvm : v ∈ genVals := List.mem_of_getElem? Hv_lookup
  iapply HΦ
  ipureintro
  exact ⟨hkm, hvm⟩
end proof

end common
end EtcdGrove
end Perennial
